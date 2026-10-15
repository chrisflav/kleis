# The mail extension

Mail through kleis: reading, filing and sending, with the mailbox's password never in the
sandbox.

Mail is not HTTP, and kleis is an HTTP proxy. So this extension brings two programs:

* **kleis-mail-gateway** (`kleis-mail-gateway.py`, image `ghcr.io/chrisflav/kleis-mail`) — a
  small HTTP service that speaks IMAP and SMTP on a request's behalf. It holds no credential and
  knows no server: each request carries the whole account in an `X-Kleis-Mail-Account` header,
  which kleis adds after stripping any copy the client sent. Reached without kleis it does
  nothing.
* **kleis-mail** (`kleis-mail`) — the command-line client an agent uses. kleis hands it to the
  sandbox as a setup file (`~/.local/bin/kleis-mail`); it needs only Python 3.

## Running it

The gateway must be reachable by kleisd as `kleis-mail:8025`, and by nothing a sandbox can
route to. With Docker, put both on one network:

```sh
docker network create kleis
docker run -d --name kleis-mail --network kleis --network-alias kleis-mail \
  --read-only --cap-drop ALL ghcr.io/chrisflav/kleis-mail:<rev>
docker run -d --name kleis --network kleis … ghcr.io/chrisflav/kleis:<rev>
```

and enable the extension in `config.toml`: `extensions = ["mail", …]`.

## An account

The secret is one line of JSON:

```json
{"user": "alice@example.org", "password": "…",
 "imap": "imap.example.org:993", "smtp": "smtp.example.org:587"}
```

IMAP is implicit TLS. SMTP is implicit TLS on 465 and STARTTLS on any other port. An optional
`"from"` sends mail from another address than `user`. Declare it like any credential:

```toml
# config/credentials/mail-alice.toml
name        = "mail/alice"
service     = "mail"
secret_file = "/run/secrets/mail-alice"
```

and give a spec access:

```
spec secretary
  max_ttl 24h
  account mail/alice
    allow read, flag, move
    allow send where recipient all ends_with "@example.org"
```

## The vocabulary

| operation | group | what |
| --- | --- | --- |
| `list_mailboxes` | `read` | `GET /mailboxes` |
| `list_messages` | `read` | `GET /mailboxes/{mailbox}/messages` |
| `read_message` | `read` | a message, its raw form, an attachment |
| `set_flags` | `flag` | `POST …/{uid}/flags` |
| `move_message` | `move` | `POST …/{uid}/move` |
| `send` | | `POST /send` |

Fields: `recipient` (several values: every address in `to`, `cc` and `bcc`), `mailbox`,
`move_target`.

Nothing deletes. A message can be moved to the trash, which a person can take back out.

## What is checked where

kleis reads the recipients out of the body (`recipient(a)` once per address), so a spec can
bound who mail goes to. The gateway accepts `to`, `cc` and `bcc` only as arrays of bare,
lower-case addresses, so that what kleis read is exactly what is sent. A body kleis could not
decode is not sent: `allow send` requires at least one recipient it read. The body is read up
to kleis's decode limit (64 KiB by default), which bounds the size of a message; attachments
are not sent.
