/*
 * Name resolution.
 *
 * Lean's networking exposes sockets but no resolver, and a proxy that cannot
 * turn `github.com` into an address is not a proxy.  This is getaddrinfo and
 * nothing else: the result is a list of address literals, which the Lean side
 * parses back into the socket address types it already has.
 *
 * Returning literals rather than opaque sockaddrs keeps the ordering, the
 * family preference and the connection attempt loop in Lean, where they can be
 * read and changed.
 */

#include <lean/lean.h>
#include <string.h>
#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <arpa/inet.h>

LEAN_EXPORT lean_obj_res kleis_net_resolve(b_lean_obj_arg host, lean_obj_arg w) {
    (void)w;
    const char *name = lean_string_cstr(host);

    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;

    struct addrinfo *res = NULL;
    int rc = getaddrinfo(name, NULL, &hints, &res);
    if (rc != 0) {
        char buf[512];
        snprintf(buf, sizeof(buf), "could not resolve `%s`: %s", name, gai_strerror(rc));
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
    }

    lean_object *arr = lean_mk_empty_array();
    for (struct addrinfo *ai = res; ai != NULL; ai = ai->ai_next) {
        char text[INET6_ADDRSTRLEN];
        const char *ok = NULL;
        if (ai->ai_family == AF_INET) {
            struct sockaddr_in *a = (struct sockaddr_in *)ai->ai_addr;
            ok = inet_ntop(AF_INET, &a->sin_addr, text, sizeof(text));
        } else if (ai->ai_family == AF_INET6) {
            struct sockaddr_in6 *a = (struct sockaddr_in6 *)ai->ai_addr;
            ok = inet_ntop(AF_INET6, &a->sin6_addr, text, sizeof(text));
        }
        if (ok) arr = lean_array_push(arr, lean_mk_string(text));
    }
    freeaddrinfo(res);
    return lean_io_result_mk_ok(arr);
}
