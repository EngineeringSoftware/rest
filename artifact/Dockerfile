# ============================================================================
# dbt-fusion Record & Replay (R&R) — Artifact Evaluation
# ============================================================================
# One image, two parts:
#   1. The REAL dbt-fusion binary runs jaffle_shop against DuckDB,
#      with --fs-record to capture warehouse interactions into recordings.db,
#      then --fs-replay to serve everything from recordings.db (zero warehouse).
#   2. The Lean 4 mechanization of the replay guarantee (formalization-lean/,
#      a copy of papers/vldb27-revision/formalization-lean) is compiled with
#      `lake build` while the image is built, so a successful `docker build`
#      is also a machine check of the proof.
#
# Usage:
#   docker build -t dbt-rr-artifact artifact/
#   docker run --rm -v $(pwd)/artifact/output:/output dbt-rr-artifact
# ============================================================================

FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl jq sqlite3 python3 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /artifact

# ── Install dbt-fusion from CDN ─────────────────────────────────────────
ARG DBT_VERSION=2.0.0-preview.172
ARG TARGET=x86_64-unknown-linux-gnu

RUN set -eux; \
    url="https://public.cdn.getdbt.com/fs/cli/fs-v${DBT_VERSION}-${TARGET}.tar.gz"; \
    echo "Downloading dbt-fusion ${DBT_VERSION} from ${url}"; \
    curl -fsSL "$url" | tar xz -C /usr/local/bin; \
    dbt --version

# ── Install Lean 4 (via elan) and build the formalization ───────────────
# The toolchain version is pinned by formalization-lean/lean-toolchain.
# The package is pure Lean 4 core (no Mathlib, no dependencies), so
# `lake build` needs nothing beyond the toolchain.  The image build fails
# if the build fails or if any declaration uses `sorry`.
ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH

RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain none

COPY formalization-lean/lean-toolchain \
     formalization-lean/lakefile.lean \
     formalization-lean/lake-manifest.json \
     /artifact/formalization-lean/

RUN elan toolchain install "$(cat /artifact/formalization-lean/lean-toolchain)"

COPY formalization-lean/Formalization /artifact/formalization-lean/Formalization
COPY formalization-lean/README.md     /artifact/formalization-lean/README.md

RUN cd /artifact/formalization-lean \
    && status=0; lake build > lake-build.log 2>&1 || status=$?; \
    cat lake-build.log; \
    test "$status" -eq 0 \
    && ! grep -q "declaration uses 'sorry'" lake-build.log \
    && echo "Lean 4 formalization: build OK, no sorry"

# ── Copy jaffle_shop project ────────────────────────────────────────────
COPY jaffle_shop /artifact/jaffle_shop

# ── Copy artifact scripts & config ──────────────────────────────────────
COPY profiles.yml          /artifact/profiles.yml
COPY run_experiment.sh     /artifact/run_experiment.sh
COPY analyze_recordings.py /artifact/analyze_recordings.py

RUN chmod +x /artifact/run_experiment.sh

ENV ARTIFACT_OUTPUT_DIR=/output

ENTRYPOINT ["/artifact/run_experiment.sh"]
