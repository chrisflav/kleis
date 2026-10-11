# kleis-mail, the HTTP gateway to IMAP and SMTP that the mail extension forwards to. See
# extensions/mail/README.md.
#
# Build context is the repository root:  docker build -f docker/mail.Dockerfile .
#
# The standard library and nothing else: the gateway holds no credential, keeps no state, and
# needs only Python and the CA bundle to verify the mail servers it is told to reach.
FROM python:3.13-slim

COPY extensions/mail/kleis-mail-gateway.py /usr/local/lib/kleis-mail/gateway.py

# Any unprivileged uid; nothing is written anywhere.
USER 65534:65534
ENV KLEIS_MAIL_LISTEN=0.0.0.0:8025
EXPOSE 8025

HEALTHCHECK --interval=30s --timeout=3s --start-period=5s \
  CMD python3 -c "import urllib.request,urllib.error as e;\
exec('try: urllib.request.urlopen(\"http://127.0.0.1:8025/mailboxes\", timeout=2)\nexcept e.HTTPError: pass')"

ENTRYPOINT ["python3", "-u", "/usr/local/lib/kleis-mail/gateway.py"]
