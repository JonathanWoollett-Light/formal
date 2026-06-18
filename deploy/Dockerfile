# Builds the `formal` verifier into an MPI-enabled runtime image for the
# Kubeflow MPI Operator (see deploy/README.md). Plain Ethernet TCP transport
# (no RDMA), which is what keeps the image portable across clouds.
#
# Build (from the repo root):
#   docker build -f deploy/Dockerfile -t <registry>/formal:<tag> .

FROM rust:1-bookworm AS build
WORKDIR /src
COPY . .
# `--features hpc` will gate the rsmpi backend once it lands; today this builds
# the default (in-process parallel + distributed-simulation) backend.
RUN cargo build --release --bin formal

FROM debian:bookworm-slim
# OpenMPI + OpenSSH: the MPI Operator launches `mpirun` from the Launcher pod
# over SSH to the Worker pods; Open MPI's same-node uses shared memory and
# cross-node uses TCP (no RDMA needed for this bandwidth-bound, latency-tolerant
# job).
RUN apt-get update \
    && apt-get install -y --no-install-recommends openmpi-bin openssh-client openssh-server ca-certificates \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/target/release/formal /usr/local/bin/formal
# The MPI Operator runs workers as `mpiuser`; mpirun needs passwordless SSH
# between pods (wired up by the operator's generated config).
ENTRYPOINT ["/usr/local/bin/formal"]
