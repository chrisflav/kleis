"""kleis-mail: a small HTTP face on one IMAP and one SMTP server, for kleis to stand in front of.

kleis is an HTTP proxy, and mail is not HTTP. Rather than teach kleis two more protocols, this
turns the handful of things an agent does with a mailbox into JSON over HTTP, and kleis treats
it like any other service: a manifest (mail.toml) says what each request means, a grant says
which of those are allowed, and the credential is injected on the way through.

THIS HOLDS NO CREDENTIAL, AND KNOWS NO SERVER. Every request carries the whole account it is
about in one header, which kleis adds -- it is the credential kleis spends for the task's
identity -- and that is what the gateway logs in with, once per request, and then forgets:

    X-Kleis-Mail-Account: {"user": "a@example.org", "password": "...",
                           "imap": "imap.example.org:993", "smtp": "smtp.example.org:587"}

IMAP is implicit TLS; SMTP is implicit TLS on 465 and STARTTLS on any other port. `from`, if
present, is the address mail is sent from instead of `user`. So each identity's mailbox can be
anywhere, and reaching the gateway without kleis gets you nothing you did not bring.

    KLEIS_MAIL_LISTEN      host:port to listen on (0.0.0.0:8025)

The API, every response JSON unless it says otherwise:

    GET  /mailboxes
    GET  /mailboxes/{mailbox}/messages?limit=&before_uid=&unseen=1&from=&to=&subject=&text=&since=
    GET  /mailboxes/{mailbox}/messages/{uid}                  headers, text, html, attachment list
    GET  /mailboxes/{mailbox}/messages/{uid}/raw              message/rfc822
    GET  /mailboxes/{mailbox}/messages/{uid}/attachments/{n}  the attachment's bytes
    POST /mailboxes/{mailbox}/messages/{uid}/flags            {"add": [...], "remove": [...]}
    POST /mailboxes/{mailbox}/messages/{uid}/move             {"to": "Archive"}
    POST /send   {"to": [...], "cc": [...], "bcc": [...], "subject": "", "text": "",
                  "in_reply_to": "<id@host>", "references": ["<id@host>", ...]}

Reading never marks a message seen (BODY.PEEK). A sent message is From the login, and a copy is
appended to the mailbox flagged \\Sent, if the server has one.

Recipients must be bare, lower-case addresses in arrays: that is the form kleis's grant compares
against an allowlist, so anything else is refused here rather than slipping past the grant.
"""

import base64
import email
import email.header
import email.policy
import email.utils
import imaplib
import json
import os
import re
import smtplib
import ssl
import sys
import time
import urllib.parse
from email.message import EmailMessage
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

ACCOUNT_HEADER = "X-Kleis-Mail-Account"
LISTEN = os.environ.get("KLEIS_MAIL_LISTEN", "0.0.0.0:8025")

MAX_BODY = 1 << 20
MAX_LIST = 200
TIMEOUT = 60

ADDRESS = re.compile(r"^[a-z0-9.!#$%&'*+/=?^_`{|}~-]+@[a-z0-9-]+(\.[a-z0-9-]+)+$")
MESSAGE_ID = re.compile(r"^<[^<>\s]+>$")
FLAG = re.compile(r"^\\?[A-Za-z$][A-Za-z0-9$_-]*$")


class Fail(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


# ------------------------------------------------------------------------- IMAP

def imap_quote(s):
    """An IMAP quoted string. CR and LF cannot be quoted at all, so they are refused."""
    if "\r" in s or "\n" in s or "\0" in s:
        raise Fail(400, "a search term cannot contain a line break")
    if not s.isascii():
        raise Fail(400, "a search term is ASCII; search for a part of it that is")
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def imap_mailbox(name):
    """A mailbox name as an IMAP argument: modified UTF-7, then quoted."""
    return imap_quote(utf7_encode(name))


def utf7_encode(s):
    out, run = [], []

    def flush():
        if run:
            b = "".join(run).encode("utf-16-be")
            out.append("&" + base64.b64encode(b).decode().rstrip("=").replace("/", ",") + "-")
            run.clear()

    for ch in s:
        if 0x20 <= ord(ch) <= 0x7E:
            flush()
            out.append("&-" if ch == "&" else ch)
        else:
            run.append(ch)
    flush()
    return "".join(out)


def utf7_decode(s):
    def repl(m):
        body = m.group(1)
        if body == "":
            return "&"
        b = body.replace(",", "/")
        b += "=" * (-len(b) % 4)
        return base64.b64decode(b).decode("utf-16-be")

    return re.sub(r"&([A-Za-z0-9+,]*)-", repl, s)


def imap_login(account):
    host, port = account["imap"]
    try:
        conn = imaplib.IMAP4_SSL(host, port, ssl_context=ssl.create_default_context(),
                                 timeout=TIMEOUT)
    except OSError as e:
        raise Fail(502, f"IMAP server unreachable: {e}")
    try:
        conn.login(account["user"], account["password"])
    except imaplib.IMAP4.error:
        conn.shutdown()
        raise Fail(401, "IMAP login failed")
    return conn


def check(typ, data, what):
    if typ != "OK":
        detail = b" ".join(d for d in data if isinstance(d, bytes)).decode(errors="replace")
        raise Fail(404 if "select" in what else 502, f"{what} failed: {detail}")
    return data


def select(conn, mailbox, readonly=True):
    check(*conn.select(imap_mailbox(mailbox), readonly=readonly), f"select {mailbox!r}")


LIST_LINE = re.compile(rb'^\((?P<flags>[^)]*)\) (?P<delim>"[^"]*"|NIL) (?P<name>.+)$')


def list_mailboxes(conn):
    data = check(*conn.list(), "list")
    boxes = []
    for line in data:
        if isinstance(line, tuple):
            # A literal name: the first element ends with {n}, the second is the name.
            head, name = line[0], line[1]
            m = LIST_LINE.match(head.rsplit(b" ", 1)[0] + b" x")
            raw = name
        else:
            m = LIST_LINE.match(line or b"")
            raw = m.group("name") if m else None
        if not m or raw is None:
            continue
        raw = raw.strip()
        if raw.startswith(b'"') and raw.endswith(b'"'):
            raw = raw[1:-1].replace(b'\\"', b'"').replace(b"\\\\", b"\\")
        flags = m.group("flags").decode().split()
        boxes.append({"name": utf7_decode(raw.decode("ascii", errors="replace")), "flags": flags})
    return boxes


def sent_mailbox(conn):
    for box in list_mailboxes(conn):
        if "\\Sent" in box["flags"]:
            return box["name"]
    return None


def decode_header(value):
    if value is None:
        return None
    return str(email.header.make_header(email.header.decode_header(value)))


def addresses(value):
    if not value:
        return []
    return [{"name": n or None, "address": a} for n, a in email.utils.getaddresses([value]) if a]


FETCH_ITEM = re.compile(rb"UID (\d+)|FLAGS \(([^)]*)\)|RFC822\.SIZE (\d+)")


def summary(meta, header_bytes):
    uid = flags = size = None
    for m in FETCH_ITEM.finditer(meta):
        if m.group(1):
            uid = int(m.group(1))
        elif m.group(2) is not None:
            flags = m.group(2).decode().split()
        elif m.group(3):
            size = int(m.group(3))
    msg = email.message_from_bytes(header_bytes, policy=email.policy.compat32)
    return {
        "uid": uid,
        "flags": flags or [],
        "size": size,
        "date": msg.get("Date"),
        "from": addresses(msg.get("From")),
        "to": addresses(msg.get("To")),
        "cc": addresses(msg.get("Cc")),
        "subject": decode_header(msg.get("Subject")),
        "message_id": msg.get("Message-ID"),
    }


def list_messages(conn, mailbox, q):
    select(conn, mailbox)
    criteria = []
    if q.get("unseen") in ("1", "true"):
        criteria.append("UNSEEN")
    for key, word in (("from", "FROM"), ("to", "TO"), ("subject", "SUBJECT"), ("text", "TEXT")):
        if q.get(key):
            criteria += [word, imap_quote(q[key])]
    if q.get("since"):
        try:
            day = time.strptime(q["since"], "%Y-%m-%d")
        except ValueError:
            raise Fail(400, "`since` is YYYY-MM-DD")
        criteria += ["SINCE", time.strftime("%d-%b-%Y", day)]
    if q.get("before_uid"):
        b = int_param(q, "before_uid")
        if b <= 1:
            return []
        criteria += ["UID", f"1:{b - 1}"]
    # imaplib quotes nothing in a search; with every term quoted above, joining is safe.
    data = check(*conn.uid("SEARCH", *(criteria or ["ALL"])), "search")
    uids = [int(u) for u in (data[0] or b"").split()]
    limit = min(int_param(q, "limit", 50), MAX_LIST)
    uids = sorted(uids, reverse=True)[:limit]
    if not uids:
        return []
    data = check(*conn.uid("FETCH", ",".join(map(str, uids)),
                           "(UID FLAGS RFC822.SIZE BODY.PEEK[HEADER.FIELDS "
                           "(DATE FROM TO CC SUBJECT MESSAGE-ID)])"), "fetch")
    out = [summary(item[0], item[1]) for item in data if isinstance(item, tuple)]
    out.sort(key=lambda m: m["uid"] or 0, reverse=True)
    return out


def fetch_raw(conn, mailbox, uid):
    select(conn, mailbox)
    data = check(*conn.uid("FETCH", str(uid), "(BODY.PEEK[])"), "fetch")
    for item in data:
        if isinstance(item, tuple):
            return item[1]
    raise Fail(404, f"no message with uid {uid} in {mailbox!r}")


def parts(msg):
    text, html, attachments = [], [], []
    for part in msg.walk():
        if part.is_multipart():
            continue
        disposition = part.get_content_disposition()
        ctype = part.get_content_type()
        if disposition == "attachment" or (disposition == "inline" and part.get_filename()) \
                or ctype not in ("text/plain", "text/html"):
            payload = part.get_payload(decode=True) or b""
            attachments.append({"index": len(attachments), "filename": part.get_filename(),
                                "content_type": ctype, "size": len(payload)})
            continue
        try:
            content = part.get_content()
        except (LookupError, UnicodeDecodeError):
            content = (part.get_payload(decode=True) or b"").decode("utf-8", errors="replace")
        (html if ctype == "text/html" else text).append(content)
    return text, html, attachments


def read_message(conn, mailbox, uid):
    raw = fetch_raw(conn, mailbox, uid)
    msg = email.message_from_bytes(raw, policy=email.policy.default)
    text, html, attachments = parts(msg)
    return {
        "uid": uid,
        "date": msg.get("Date"),
        "from": addresses(msg.get("From")),
        "to": addresses(msg.get("To")),
        "cc": addresses(msg.get("Cc")),
        "reply_to": addresses(msg.get("Reply-To")),
        "subject": msg.get("Subject"),
        "message_id": msg.get("Message-ID"),
        "in_reply_to": msg.get("In-Reply-To"),
        "references": (msg.get("References") or "").split(),
        "text": "\n".join(text),
        "html": "\n".join(html) or None,
        "attachments": attachments,
    }


def attachment(conn, mailbox, uid, index):
    msg = email.message_from_bytes(fetch_raw(conn, mailbox, uid), policy=email.policy.default)
    seen = 0
    for part in msg.walk():
        if part.is_multipart():
            continue
        disposition = part.get_content_disposition()
        ctype = part.get_content_type()
        if disposition == "attachment" or (disposition == "inline" and part.get_filename()) \
                or ctype not in ("text/plain", "text/html"):
            if seen == index:
                return ctype, part.get_filename(), part.get_payload(decode=True) or b""
            seen += 1
    raise Fail(404, f"message {uid} has no attachment {index}")


def set_flags(conn, mailbox, uid, body):
    select(conn, mailbox, readonly=False)
    for key, op in (("add", "+FLAGS.SILENT"), ("remove", "-FLAGS.SILENT")):
        flags = body.get(key) or []
        if not isinstance(flags, list) or not all(isinstance(f, str) and FLAG.match(f) for f in flags):
            raise Fail(400, f"`{key}` is a list of flags such as \\Seen or $Label")
        if flags:
            check(*conn.uid("STORE", str(uid), op, "(" + " ".join(flags) + ")"), "store")
    return {"ok": True}


def move(conn, mailbox, uid, body):
    target = body.get("to")
    if not isinstance(target, str) or not target:
        raise Fail(400, "`to` names the mailbox to move the message to")
    select(conn, mailbox, readonly=False)
    typ, data = conn.uid("MOVE", str(uid), imap_mailbox(target))
    if typ != "OK":
        # A server without MOVE (RFC 6851): copy, flag deleted, expunge that one message.
        check(*conn.uid("COPY", str(uid), imap_mailbox(target)), "copy")
        check(*conn.uid("STORE", str(uid), "+FLAGS.SILENT", "(\\Deleted)"), "store")
        check(*conn.uid("EXPUNGE", str(uid)), "expunge")
    return {"ok": True}


# ------------------------------------------------------------------------- SMTP

def address_list(body, key):
    value = body.get(key, [])
    if not isinstance(value, list) or not all(isinstance(a, str) for a in value):
        raise Fail(400, f"`{key}` is a list of addresses")
    for a in value:
        if not ADDRESS.match(a):
            raise Fail(400, f"`{a}` is not a bare, lower-case address")
    return value


def send(account, body):
    if not account["smtp"]:
        raise Fail(503, "this account has no SMTP server")
    sender = account["from"]
    to, cc, bcc = (address_list(body, k) for k in ("to", "cc", "bcc"))
    if not (to or cc or bcc):
        raise Fail(400, "a message needs at least one recipient")
    subject, text = body.get("subject", ""), body.get("text")
    if not isinstance(subject, str) or not isinstance(text, str):
        raise Fail(400, "`subject` and `text` are strings, and `text` is required")
    extra = set(body) - {"to", "cc", "bcc", "subject", "text", "in_reply_to", "references"}
    if extra:
        raise Fail(400, f"unknown field(s): {', '.join(sorted(extra))}")

    msg = EmailMessage()
    msg["From"] = sender
    if to:
        msg["To"] = ", ".join(to)
    if cc:
        msg["Cc"] = ", ".join(cc)
    msg["Subject"] = subject
    msg["Date"] = email.utils.formatdate(localtime=True)
    msg["Message-ID"] = email.utils.make_msgid(domain=sender.rpartition("@")[2] or None)
    reply = body.get("in_reply_to")
    refs = body.get("references") or []
    for r in ([reply] if reply else []) + refs:
        if not isinstance(r, str) or not MESSAGE_ID.match(r):
            raise Fail(400, f"`{r}` is not a message id such as <id@host>")
    if reply:
        msg["In-Reply-To"] = reply
    if refs or reply:
        msg["References"] = " ".join(refs + ([reply] if reply and reply not in refs else []))
    msg.set_content(text)

    context = ssl.create_default_context()
    try:
        host, port = account["smtp"]
        if port == 465:
            smtp = smtplib.SMTP_SSL(host, port, context=context, timeout=TIMEOUT)
        else:
            smtp = smtplib.SMTP(host, port, timeout=TIMEOUT)
            smtp.starttls(context=context)
    except OSError as e:
        raise Fail(502, f"SMTP server unreachable: {e}")
    with smtp:
        try:
            smtp.login(account["user"], account["password"])
        except smtplib.SMTPAuthenticationError:
            raise Fail(401, "SMTP login failed")
        refused = smtp.send_message(msg, from_addr=sender, to_addrs=to + cc + bcc)

    # The copy in Sent is a courtesy: the message has gone, so failing here is not an error.
    saved = None
    if account["imap"]:
        try:
            conn = imap_login(account)
            try:
                box = sent_mailbox(conn)
                if box:
                    typ, _ = conn.append(imap_mailbox(box), "(\\Seen)",
                                         imaplib.Time2Internaldate(time.time()), msg.as_bytes())
                    saved = box if typ == "OK" else None
            finally:
                conn.logout()
        except (Fail, OSError, imaplib.IMAP4.error):
            pass
    return {"ok": True, "message_id": msg["Message-ID"], "refused": sorted(refused),
            "saved_to": saved}


# ------------------------------------------------------------------------- HTTP

def int_param(q, key, default=None):
    v = q.get(key)
    if v is None:
        if default is None:
            raise Fail(400, f"`{key}` is required")
        return default
    if not v.isdigit():
        raise Fail(400, f"`{key}` is a number")
    return int(v)


def server(value, what, default_port):
    if value is None:
        return None
    if not isinstance(value, str) or not value:
        raise Fail(500, f"the account's `{what}` is `host[:port]`")
    if ":" in value:
        host, _, port = value.rpartition(":")
    else:
        host, port = value, str(default_port)
    if not host or not port.isdigit():
        raise Fail(500, f"the account's `{what}` is `host[:port]`")
    return host, int(port)


def credentials(headers):
    """The account kleis attached. Never echoed back: an error names a field, not a value."""
    raw = headers.get(ACCOUNT_HEADER)
    if not raw:
        raise Fail(401, "no account: this is reached through kleis, which adds the mailbox of "
                        "the task's identity -- or the identity has none")
    try:
        account = json.loads(raw)
    except ValueError:
        raise Fail(500, "the account kleis attached is not JSON")
    if not isinstance(account, dict) or not all(
            isinstance(account.get(k), str) and account[k] for k in ("user", "password")):
        raise Fail(500, "the account needs `user` and `password`")
    return {
        "user": account["user"],
        "password": account["password"],
        "from": account.get("from") or account["user"],
        "imap": server(account.get("imap"), "imap", 993),
        "smtp": server(account.get("smtp"), "smtp", 587),
    }


class Handler(BaseHTTPRequestHandler):
    server_version = "kleis-mail"
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        # The path and status only: never a header, which is where the password is.
        sys.stderr.write("%s %s\n" % (self.command, fmt % args))

    def reply(self, status, payload, ctype="application/json", extra=None):
        data = payload if isinstance(payload, bytes) else \
            (json.dumps(payload, ensure_ascii=False, indent=1) + "\n").encode()
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    def body(self):
        n = int(self.headers.get("Content-Length") or 0)
        if n > MAX_BODY:
            raise Fail(413, "request body too large")
        raw = self.rfile.read(n) if n else b"{}"
        try:
            value = json.loads(raw)
        except ValueError:
            raise Fail(400, "the body is JSON")
        if not isinstance(value, dict):
            raise Fail(400, "the body is a JSON object")
        return value

    def route(self):
        url = urllib.parse.urlsplit(self.path)
        segs = [urllib.parse.unquote(s) for s in url.path.split("/") if s]
        q = {k: v[-1] for k, v in urllib.parse.parse_qs(url.query).items()}
        m = self.command

        if m == "POST" and segs == ["send"]:
            body = self.body()
            return self.reply(200, send(credentials(self.headers), body))

        if not segs or segs[0] != "mailboxes":
            raise Fail(404, "no such endpoint")
        account = credentials(self.headers)
        if not account["imap"]:
            raise Fail(503, "this account has no IMAP server")
        body = self.body() if m == "POST" else None
        conn = imap_login(account)
        try:
            if m == "GET" and len(segs) == 1:
                return self.reply(200, {"mailboxes": list_mailboxes(conn)})
            if len(segs) < 3 or segs[2] != "messages":
                raise Fail(404, "no such endpoint")
            mailbox = segs[1]
            if m == "GET" and len(segs) == 3:
                return self.reply(200, {"mailbox": mailbox, "messages": list_messages(conn, mailbox, q)})
            if len(segs) < 4 or not segs[3].isdigit():
                raise Fail(404, "no such endpoint")
            uid = int(segs[3])
            rest = segs[4:]
            if m == "GET" and rest == []:
                return self.reply(200, read_message(conn, mailbox, uid))
            if m == "GET" and rest == ["raw"]:
                return self.reply(200, fetch_raw(conn, mailbox, uid), "message/rfc822")
            if m == "GET" and len(rest) == 2 and rest[0] == "attachments" and rest[1].isdigit():
                ctype, name, data = attachment(conn, mailbox, uid, int(rest[1]))
                extra = {"Content-Disposition": "attachment; filename*=UTF-8''"
                         + urllib.parse.quote(name)} if name else None
                return self.reply(200, data, ctype, extra)
            if m == "POST" and rest == ["flags"]:
                return self.reply(200, set_flags(conn, mailbox, uid, body))
            if m == "POST" and rest == ["move"]:
                return self.reply(200, move(conn, mailbox, uid, body))
            raise Fail(404, "no such endpoint")
        finally:
            try:
                conn.logout()
            except (OSError, imaplib.IMAP4.error):
                pass

    def handle_any(self):
        try:
            self.route()
        except Fail as e:
            self.reply(e.status, {"error": e.message})
        except (imaplib.IMAP4.error, smtplib.SMTPException, OSError) as e:
            self.reply(502, {"error": f"{type(e).__name__}: {e}"})

    do_GET = do_POST = do_HEAD = handle_any

    def do_PUT(self):
        self.reply(405, {"error": "method not allowed"})

    do_DELETE = do_PATCH = do_PUT


def main():
    host, _, port = LISTEN.rpartition(":")
    server = ThreadingHTTPServer((host or "0.0.0.0", int(port)), Handler)
    server.daemon_threads = True
    sys.stderr.write(f"kleis-mail on {LISTEN}\n")
    server.serve_forever()


if __name__ == "__main__":
    main()
