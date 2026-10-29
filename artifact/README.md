# Record & Replay (R&R) — Artifact 

This artifact runs jaffle_shop against
DuckDB, capturing all warehouse interactions with `--fs-record` and
replaying them from `recordings.db` with `--fs-replay`.  The same image
contains the Lean 4 mechanization of the replay guarantee
(`formalization-lean/`), which is compiled with `lake build` while the
image is built, so a successful `docker build` also checks the proof.

## Quick Start

```bash
# From the record-replay-dbt repo root
docker compose -f artifact/docker-compose.yml up --build
```

Or build and run directly:

```bash
docker build -t dbt-rr-artifact artifact/
docker run --rm -v $(pwd)/artifact/output:/output dbt-rr-artifact
```

This will:

1. Install dbt-fusion from CDN and the pinned Lean 4 toolchain, and
   compile the Lean formalization (the build fails on any `sorry`)
2. **Record run**: `dbt run --fs-record` — runs jaffle_shop against DuckDB;
   every SQL query hits the warehouse AND is saved to `recordings.db`
3. **Replay run**: `dbt run --fs-replay` — serves model queries from
   `recordings.db`.  DuckDB is restored to post-seed state (the adapter
   needs it for connection init / schema listing).  We checksum DuckDB
   before and after replay: **matching checksums prove zero warehouse
   writes** — all model queries (CREATE TABLE, CREATE VIEW, …) were
   served entirely from `recordings.db`.
4. Print per-run interaction counts
5. Re-run `lake build` on the Lean formalization inside the container
   and report that every module checks with no `sorry`

Output files are written to `artifact/output/`.

## What It Measures

For each run, the script reports the number of **warehouse interactions**
(requests between dbt and DuckDB):

| Interaction type     | Description                                |
| -------------------- | ------------------------------------------ |
| `execute`          | SQL statements (CREATE, INSERT, SELECT...) |
| `get_table_schema` | Schema introspection for materialization   |

## Expected Results

jaffle_shop has 6 seeds, 6 staging views, 6 mart tables, and tests.

| Metric                    | Record run |       Replay run       |
| ------------------------- | :--------: | :---------------------: |
| Total interactions        |     N     |            N            |
| DuckDB modified?          |    yes    | **NO** (checksum) |
| Served from recordings.db |     0     |       **N**       |

(N = total interactions, reported by the experiment)

## Output Files

```
artifact/output/
├── artifact_summary.json     # Machine-readable summary (JSON)
├── analysis_report.json      # Detailed per-model analysis
├── record_trace.txt          # Full record trace (all SQL sent to warehouse)
├── replay_trace.txt          # Full replay trace (all SQL served from recordings.db)
├── record_run.log            # stdout/stderr from the record run
├── replay_run.log            # stdout/stderr from the replay run
├── deps.log                  # dbt deps output
├── lean_build.log            # lake build output for the Lean formalization
└── record_run/
    └── recordings.db         # SQLite DB with all recorded interactions
```

## Inspect recordings.db

```bash
# Count interactions by type
sqlite3 artifact/output/record_run/recordings.db \
  "SELECT record_type, COUNT(*) FROM recordings GROUP BY record_type"

# Show recorded SQL statements
sqlite3 artifact/output/record_run/recordings.db \
  "SELECT unique_id, SUBSTR(sql, 1, 80) FROM recordings WHERE record_type='execute'"

# Full analysis
python3 artifact/analyze_recordings.py artifact/output/
```

## recordings.db Schema

```sql
CREATE TABLE recordings (
    unique_id   TEXT NOT NULL,       -- e.g. "model.jaffle_shop.orders-0"
    record_type TEXT NOT NULL,       -- "execute" or "get_table_schema"
    sql         TEXT,                -- SQL sent to the warehouse
    data_base64 TEXT,                -- Base64-encoded Arrow IPC result
    error       TEXT,                -- Error message (NULL on success)
    PRIMARY KEY (unique_id, record_type)
);
```

## Architecture

```
  Record mode                          Replay mode
  ──────────                           ───────────
  dbt run --fs-record <dir>            dbt run --fs-replay <dir>

  ┌──────────┐    SQL     ┌────────┐   ┌──────────┐
  │ dbt      │───────────▶│ DuckDB │   │ dbt      │
  │ adapter  │◀───────────│        │   │ adapter  │
  └────┬─────┘  results   └────────┘   └────┬─────┘
       │                                    │
       │ write                         read │
       ▼                                    ▼
  ┌──────────────┐                ┌──────────────┐
  │recordings.db │                │recordings.db │
  │  (SQLite)    │  ─── copy ──▶  │  (SQLite)    │
  └──────────────┘                └──────────────┘
```

## Lean 4 Formalization

`formalization-lean/` is the Lean 4 mechanization of the replay guarantee
stated in the paper.  It is pure Lean 4 core with no Mathlib and no
package dependencies, and the toolchain version is pinned in
`formalization-lean/lean-toolchain`.  The image build runs `lake build`
on it and fails if the build fails or if any declaration uses `sorry`.
To rerun the check by hand:

```bash
docker run --rm --entrypoint bash dbt-rr-artifact \
  -c 'cd /artifact/formalization-lean && lake build'
```

See `formalization-lean/README.md` for the module structure and the main
theorems.

## Source Code

| Component                                    | File                                            |
| -------------------------------------------- | ----------------------------------------------- |
| R&R engine                                   | `crates/dbt-adapter/src/record_and_replay.rs` |
| Engine mode dispatch                         | `crates/dbt-adapter/src/engine/xdbc.rs`       |
| CLI flags (`--fs-record`, `--fs-replay`) | `crates/dbt-clap-core/src/lib.rs`             |
| Lean 4 formalization                         | `artifact/formalization-lean/Formalization/`    |

## File Listing

```
artifact/
├── Dockerfile              # Installs dbt-fusion and Lean 4, builds the proof
├── docker-compose.yml      # Docker Compose for artifact runner
├── run_experiment.sh       # Main experiment: record → replay → report
├── analyze_recordings.py   # Analysis tool for recordings.db
├── profiles.yml            # dbt profile for DuckDB
├── jaffle_shop/            # dbt project (bundled)
├── formalization-lean/     # Lean 4 mechanization (lake project, no Mathlib)
└── README.md               # This file
```
