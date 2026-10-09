# The kleis daemon, as a container: `kleisd` by default, with `kleis` beside it for the
# administrative commands (`docker exec kleis kleis token list`, and so on).
#
# Build context is the repository root:  docker build -f docker/Dockerfile .

# ---- Build ----
# No official Lean image: elan installs exactly the toolchain lean-toolchain pins, as `lake`
# would locally.
FROM debian:bookworm-slim AS build
# `build-essential` for the `cc` that compiles the C shims under ffi/, `libssl-dev` for the
# OpenSSL headers the TLS shim includes and the libraries the binaries link.
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git build-essential libssl-dev \
    && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/root/.elan
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
      | sh -s -- -y --no-modify-path --default-toolchain none
WORKDIR /src
COPY lean-toolchain lakefile.lean lake-manifest.json ./
COPY Kleis.lean Kleisd.lean Main.lean ./
COPY Kleis ./Kleis
COPY ffi ./ffi
# The two executables, not the default target: the test driver has no place in the image.
# Lean's bundled linker does not search the distribution's multiarch directory, so the
# directory OpenSSL lives in is named explicitly.
ENV LIBRARY_PATH=/usr/lib/x86_64-linux-gnu
RUN lake build kleis kleisd

# ---- Runtime ----
FROM debian:bookworm-slim AS runtime
# `libssl3` is what the binaries load; `ca-certificates` is the trust store origins are verified
# against (kleisd refuses to start with an empty one); `curl` is for the health check.
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates libssl3 curl \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/.lake/build/bin/kleisd /src/.lake/build/bin/kleis /usr/local/bin/

# Configuration under /kleis/config, state under /kleis/data: a deployment mounts the first
# read-only and the second as a volume that outlives the container.
ENV KLEIS_HOME=/kleis
# An unprivileged account with a fixed uid, so a deployment can own the state directory to it.
RUN useradd --system --uid 990 --home-dir /kleis --no-create-home kleis \
    && mkdir -p /kleis/config /kleis/data && chown kleis /kleis/data
USER kleis

EXPOSE 8080
VOLUME ["/kleis/data"]

# Any valid response means the daemon is up: without a token it answers 407.
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s \
  CMD curl -s -o /dev/null http://127.0.0.1:8080/ || exit 1

ENTRYPOINT ["kleisd"]
