#!/usr/bin/env python3
"""A tiny origin for the integration test.

Two jobs: echo back what it received, so the test can prove the credential
arrived and the client's own Authorization did not; and serve a git repository
over smart HTTP via `git http-backend`, so the test can prove a real `git push`
survives the proxy.
"""
import json, os, ssl, subprocess, sys
from http.server import BaseHTTPRequestHandler, HTTPServer

REPO_ROOT = sys.argv[2] if len(sys.argv) > 2 else "/tmp"


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    def _body(self):
        n = int(self.headers.get("Content-Length") or 0)
        return self.rfile.read(n) if n else b""

    def _echo(self, body):
        payload = json.dumps({
            "method": self.command,
            "path": self.path,
            "headers": {k.lower(): v for k, v in self.headers.items()},
            "body": body.decode("utf-8", "replace"),
        }).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def _git(self, body):
        env = dict(os.environ)
        env.update({
            "GIT_PROJECT_ROOT": REPO_ROOT,
            "GIT_HTTP_EXPORT_ALL": "1",
            "REQUEST_METHOD": self.command,
            "PATH_INFO": self.path.split("?")[0],
            "QUERY_STRING": self.path.split("?")[1] if "?" in self.path else "",
            "CONTENT_TYPE": self.headers.get("Content-Type", ""),
            "CONTENT_LENGTH": str(len(body)),
            "REMOTE_USER": "tester",
            "REMOTE_ADDR": "127.0.0.1",
            "SERVER_PROTOCOL": "HTTP/1.1",
            "GIT_COMMITTER_NAME": "origin",
            "GIT_COMMITTER_EMAIL": "origin@test",
        })
        proc = subprocess.run(["git", "http-backend"], input=body,
                              capture_output=True, env=env)
        head, _, payload = proc.stdout.partition(b"\r\n\r\n")
        status, headers = 200, []
        for line in head.decode("latin1").split("\r\n"):
            if not line:
                continue
            name, _, value = line.partition(":")
            value = value.strip()
            if name.lower() == "status":
                status = int(value.split()[0])
            else:
                headers.append((name, value))
        self.send_response(status)
        for name, value in headers:
            self.send_header(name, value)
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def _dispatch(self):
        body = self._body()
        if self.path.startswith("/echo"):
            self._echo(body)
        else:
            self._git(body)

    do_GET = _dispatch
    do_POST = _dispatch
    do_PUT = _dispatch


if __name__ == "__main__":
    server = HTTPServer(("127.0.0.1", int(sys.argv[1])), Handler)
    # With a certificate and key, serve TLS: that is the case the intercepting
    # mode has to work against, and the proxy verifies this certificate the way
    # it would verify a real origin's.
    if len(sys.argv) > 4:
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(sys.argv[3], sys.argv[4])
        server.socket = context.wrap_socket(server.socket, server_side=True)
    server.serve_forever()
