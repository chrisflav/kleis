/*
 * A TLS shim over OpenSSL, exposed to Lean as a byte transform.
 *
 * The session never touches a socket.  It owns two memory BIOs: ciphertext is
 * fed in with auth_tls_feed and drawn out with auth_tls_pull, while plaintext
 * goes in and out through auth_tls_write and auth_tls_read.  Whatever carries
 * the bytes -- libuv, a unix socket, a test harness holding two sessions
 * face to face -- is the caller's business.
 *
 * That is the whole reason this file is small.  Wiring OpenSSL to a file
 * descriptor would mean plumbing descriptors out of Lean's async runtime and
 * would tie TLS to one transport; a byte transform ties it to none, and lets
 * everything above it be tested over plain sockets.
 *
 * Certificate selection stays in Lean: the ClientHello is parsed there for its
 * SNI before a server session is created, so this file never has to call back
 * up into Lean to choose a certificate.
 */

#include <lean/lean.h>
#include <string.h>
#include <stdlib.h>

#include <openssl/ssl.h>
#include <openssl/err.h>
#include <openssl/bio.h>
#include <openssl/x509.h>

/* ------------------------------------------------------------------ */
/* External classes                                                     */
/* ------------------------------------------------------------------ */

static lean_external_class *g_ctx_class = NULL;
static lean_external_class *g_conn_class = NULL;

static void ctx_finalize(void *p) {
    if (p) SSL_CTX_free((SSL_CTX *)p);
}
static void noop_foreach(void *mod, b_lean_obj_arg fn) {
    (void)mod; (void)fn;
}

typedef struct {
    SSL *ssl;
    BIO *rbio;  /* ciphertext in  */
    BIO *wbio;  /* ciphertext out */
    char last_error[256];
} auth_conn;

static void conn_finalize(void *p) {
    auth_conn *c = (auth_conn *)p;
    if (!c) return;
    if (c->ssl) SSL_free(c->ssl);  /* frees the BIOs it owns */
    free(c);
}

static void ensure_classes(void) {
    if (!g_ctx_class)
        g_ctx_class = lean_register_external_class(ctx_finalize, noop_foreach);
    if (!g_conn_class)
        g_conn_class = lean_register_external_class(conn_finalize, noop_foreach);
}

static lean_obj_res io_error(const char *msg) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res io_error_ssl(const char *prefix) {
    char buf[512];
    unsigned long e = ERR_get_error();
    char detail[256] = "";
    if (e) ERR_error_string_n(e, detail, sizeof(detail));
    snprintf(buf, sizeof(buf), "%s%s%s", prefix, e ? ": " : "", detail);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static lean_obj_res mk_bytes(const unsigned char *data, size_t len) {
    lean_object *arr = lean_alloc_sarray(1, len, len);
    if (len) memcpy(lean_sarray_cptr(arr), data, len);
    return arr;
}

/* ------------------------------------------------------------------ */
/* Contexts                                                             */
/* ------------------------------------------------------------------ */

/* A client context.  Verification is always on: this proxy exists to hold a
 * credential, and a credential handed to an unauthenticated peer is worse than
 * no proxy at all.  caFile may be empty for the system trust store. */
LEAN_EXPORT lean_obj_res auth_tls_ctx_client(b_lean_obj_arg ca_file, lean_obj_arg w) {
    (void)w;
    ensure_classes();
    SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
    if (!ctx) return io_error_ssl("could not create a TLS client context");
    SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION);
    SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, NULL);
    const char *ca = lean_string_cstr(ca_file);
    if (ca && ca[0]) {
        if (SSL_CTX_load_verify_locations(ctx, ca, NULL) != 1) {
            SSL_CTX_free(ctx);
            return io_error_ssl("could not load the trust store");
        }
    } else if (SSL_CTX_set_default_verify_paths(ctx) != 1) {
        SSL_CTX_free(ctx);
        return io_error_ssl("could not load the system trust store");
    }
    return lean_io_result_mk_ok(lean_alloc_external(g_ctx_class, ctx));
}

/* A server context from a PEM certificate chain and private key held in
 * memory.  In memory rather than on disk because a leaf certificate here is
 * minted per connection and would otherwise be a temporary file holding a
 * private key. */
LEAN_EXPORT lean_obj_res auth_tls_ctx_server(b_lean_obj_arg cert_pem,
                                             b_lean_obj_arg key_pem,
                                             lean_obj_arg w) {
    (void)w;
    ensure_classes();
    SSL_CTX *ctx = SSL_CTX_new(TLS_server_method());
    if (!ctx) return io_error_ssl("could not create a TLS server context");
    SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION);

    const char *cert = lean_string_cstr(cert_pem);
    const char *key = lean_string_cstr(key_pem);

    BIO *cbio = BIO_new_mem_buf(cert, -1);
    if (!cbio) { SSL_CTX_free(ctx); return io_error("out of memory"); }
    X509 *x = PEM_read_bio_X509(cbio, NULL, NULL, NULL);
    if (!x) { BIO_free(cbio); SSL_CTX_free(ctx);
              return io_error_ssl("could not read the certificate"); }
    if (SSL_CTX_use_certificate(ctx, x) != 1) {
        X509_free(x); BIO_free(cbio); SSL_CTX_free(ctx);
        return io_error_ssl("could not install the certificate");
    }
    /* Any further certificates in the PEM are the chain. */
    X509 *issuer;
    while ((issuer = PEM_read_bio_X509(cbio, NULL, NULL, NULL)) != NULL) {
        if (SSL_CTX_add_extra_chain_cert(ctx, issuer) != 1) X509_free(issuer);
    }
    ERR_clear_error();
    X509_free(x);
    BIO_free(cbio);

    BIO *kbio = BIO_new_mem_buf(key, -1);
    if (!kbio) { SSL_CTX_free(ctx); return io_error("out of memory"); }
    EVP_PKEY *pk = PEM_read_bio_PrivateKey(kbio, NULL, NULL, NULL);
    BIO_free(kbio);
    if (!pk) { SSL_CTX_free(ctx); return io_error_ssl("could not read the private key"); }
    if (SSL_CTX_use_PrivateKey(ctx, pk) != 1) {
        EVP_PKEY_free(pk); SSL_CTX_free(ctx);
        return io_error_ssl("could not install the private key");
    }
    EVP_PKEY_free(pk);
    if (SSL_CTX_check_private_key(ctx) != 1) {
        SSL_CTX_free(ctx);
        return io_error_ssl("the private key does not match the certificate");
    }
    return lean_io_result_mk_ok(lean_alloc_external(g_ctx_class, ctx));
}

/* ------------------------------------------------------------------ */
/* Sessions                                                             */
/* ------------------------------------------------------------------ */

LEAN_EXPORT lean_obj_res auth_tls_conn_new(b_lean_obj_arg ctx_obj,
                                           uint8_t is_server,
                                           b_lean_obj_arg hostname,
                                           lean_obj_arg w) {
    (void)w;
    ensure_classes();
    SSL_CTX *ctx = (SSL_CTX *)lean_get_external_data(ctx_obj);
    auth_conn *c = (auth_conn *)calloc(1, sizeof(auth_conn));
    if (!c) return io_error("out of memory");
    c->ssl = SSL_new(ctx);
    if (!c->ssl) { free(c); return io_error_ssl("could not create a TLS session"); }
    c->rbio = BIO_new(BIO_s_mem());
    c->wbio = BIO_new(BIO_s_mem());
    if (!c->rbio || !c->wbio) {
        SSL_free(c->ssl); free(c);
        return io_error("out of memory");
    }
    /* SSL_set_bio takes ownership of both. */
    SSL_set_bio(c->ssl, c->rbio, c->wbio);

    const char *host = lean_string_cstr(hostname);
    if (is_server) {
        SSL_set_accept_state(c->ssl);
    } else {
        SSL_set_connect_state(c->ssl);
        if (host && host[0]) {
            SSL_set_tlsext_host_name(c->ssl, host);
            /* Without this the certificate is verified as a chain but not as
             * belonging to the host we meant to reach. */
            SSL_set1_host(c->ssl, host);
        }
    }
    return lean_io_result_mk_ok(lean_alloc_external(g_conn_class, c));
}

/* Feed received ciphertext into the session. */
LEAN_EXPORT lean_obj_res auth_tls_feed(b_lean_obj_arg conn_obj,
                                       b_lean_obj_arg bytes, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    size_t len = lean_sarray_size(bytes);
    if (len) {
        const unsigned char *p = lean_sarray_cptr(bytes);
        size_t written = 0;
        while (written < len) {
            int n = BIO_write(c->rbio, p + written, (int)(len - written));
            if (n <= 0) return io_error("the TLS input buffer rejected data");
            written += (size_t)n;
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Draw ciphertext the session wants sent. */
LEAN_EXPORT lean_obj_res auth_tls_pull(b_lean_obj_arg conn_obj, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    size_t pending = BIO_ctrl_pending(c->wbio);
    if (pending == 0) return lean_io_result_mk_ok(mk_bytes(NULL, 0));
    unsigned char *buf = (unsigned char *)malloc(pending);
    if (!buf) return io_error("out of memory");
    int n = BIO_read(c->wbio, buf, (int)pending);
    if (n < 0) n = 0;
    lean_object *out = mk_bytes(buf, (size_t)n);
    free(buf);
    return lean_io_result_mk_ok(out);
}

/* Advance the handshake.  0 = complete, 1 = needs more input, 2 = failed. */
LEAN_EXPORT lean_obj_res auth_tls_handshake(b_lean_obj_arg conn_obj, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    ERR_clear_error();
    int r = SSL_do_handshake(c->ssl);
    if (r == 1) return lean_io_result_mk_ok(lean_box(0));
    int err = SSL_get_error(c->ssl, r);
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE)
        return lean_io_result_mk_ok(lean_box(1));
    unsigned long e = ERR_get_error();
    if (e) ERR_error_string_n(e, c->last_error, sizeof(c->last_error));
    else if (err == SSL_ERROR_SSL) {
        long v = SSL_get_verify_result(c->ssl);
        snprintf(c->last_error, sizeof(c->last_error),
                 "certificate verification failed: %s",
                 X509_verify_cert_error_string(v));
    } else {
        snprintf(c->last_error, sizeof(c->last_error),
                 "the peer closed the connection during the handshake");
    }
    return lean_io_result_mk_ok(lean_box(2));
}

/* Encrypt plaintext.  Returns the number of bytes accepted; a short write
 * means the caller should pull ciphertext and try again. */
LEAN_EXPORT lean_obj_res auth_tls_write(b_lean_obj_arg conn_obj,
                                        b_lean_obj_arg bytes, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    size_t len = lean_sarray_size(bytes);
    if (len == 0) return lean_io_result_mk_ok(lean_box_uint32(0));
    ERR_clear_error();
    int n = SSL_write(c->ssl, lean_sarray_cptr(bytes), (int)len);
    if (n > 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)n));
    int err = SSL_get_error(c->ssl, n);
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    return io_error_ssl("the TLS session could not encrypt");
}

/* Decrypt whatever is available, up to `max` bytes.  An empty result means
 * nothing is ready; use auth_tls_eof to tell that from a closed session. */
LEAN_EXPORT lean_obj_res auth_tls_read(b_lean_obj_arg conn_obj,
                                       uint32_t max, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    if (max == 0) return lean_io_result_mk_ok(mk_bytes(NULL, 0));
    unsigned char *buf = (unsigned char *)malloc(max);
    if (!buf) return io_error("out of memory");
    ERR_clear_error();
    int n = SSL_read(c->ssl, buf, (int)max);
    if (n > 0) {
        lean_object *out = mk_bytes(buf, (size_t)n);
        free(buf);
        return lean_io_result_mk_ok(out);
    }
    free(buf);
    int err = SSL_get_error(c->ssl, n);
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE ||
        err == SSL_ERROR_ZERO_RETURN)
        return lean_io_result_mk_ok(mk_bytes(NULL, 0));
    return lean_io_result_mk_ok(mk_bytes(NULL, 0));
}

/* Has the peer sent close_notify? */
LEAN_EXPORT lean_obj_res auth_tls_eof(b_lean_obj_arg conn_obj, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    int shutdown = SSL_get_shutdown(c->ssl);
    return lean_io_result_mk_ok(lean_box((shutdown & SSL_RECEIVED_SHUTDOWN) ? 1 : 0));
}

/* Begin an orderly close. */
LEAN_EXPORT lean_obj_res auth_tls_close(b_lean_obj_arg conn_obj, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    ERR_clear_error();
    SSL_shutdown(c->ssl);
    return lean_io_result_mk_ok(lean_box(0));
}

/* The last handshake failure, for a log line. */
LEAN_EXPORT lean_obj_res auth_tls_error(b_lean_obj_arg conn_obj, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    return lean_io_result_mk_ok(lean_mk_string(c->last_error));
}

/* The negotiated protocol version, for the audit record. */
LEAN_EXPORT lean_obj_res auth_tls_version(b_lean_obj_arg conn_obj, lean_obj_arg w) {
    (void)w;
    auth_conn *c = (auth_conn *)lean_get_external_data(conn_obj);
    const char *v = SSL_get_version(c->ssl);
    return lean_io_result_mk_ok(lean_mk_string(v ? v : ""));
}
