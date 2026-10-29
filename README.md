# REST: Recording and Replaying for Data Engineering Pipelines

Artifact for the paper *REST: Recording and Replaying for Data Engineering Pipelines*.

## About the data

The projects used in the paper are derived from internal projects that run on
real customer datasets. These datasets may contain sensitive information about
customers and their data, so they cannot be released. The record-and-replay
infrastructure itself, at the adapter-to-driver boundary, is public as part of
the dbt code repository (<https://github.com/dbt-labs/dbt-fusion>).

Instead of the internal projects, this artifact contains:

1. A record-and-replay setup on a public dbt project, jaffle_shop, running on
   DuckDB (`artifact/`). It uses the released dbt-fusion binary.
2. The Lean 4 formalization of REST and the mechanized proof of its replay
   guarantee (`artifact/formalization-lean/`).

## Requirements

Docker with Docker Compose. Nothing else needs to be installed; dbt-fusion,
DuckDB and the Lean toolchain are pulled inside the image.

## Running

```bash
cd artifact && ./s
```

Output goes to `artifact/output/`. See `artifact/README.md` for details.

## Expected results

The record run of jaffle_shop succeeds and all its warehouse interactions
are saved to `recordings.db`. The replay run succeeds as well, with every
interaction served from `recordings.db`, and the DuckDB checksum is the same
before and after replay, i.e. replay does not touch the warehouse. The Lean
formalization builds with no `sorry`. A summary is written to
`artifact/output/artifact_summary.json`.
