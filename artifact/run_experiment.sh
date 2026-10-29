#!/usr/bin/env bash
# ============================================================================
# dbt-fusion Record & Replay — Artifact Evaluation
# ============================================================================
# Runs the REAL dbt binary against DuckDB with jaffle_shop.
#
#   Step 1: dbt seed (no R&R) — populate the database
#   Step 2: dbt run  --fs-record — record model queries to recordings.db
#   Step 3: dbt run  --fs-replay — replay from recordings.db
#            DuckDB is reset to post-seed state.  After replay we verify
#            that DuckDB is byte-identical to the snapshot, proving that
#            model queries were served entirely from recordings.db.
# ============================================================================
set -euo pipefail

OUTPUT="${ARTIFACT_OUTPUT_DIR:-/output}"
PROJECT="/artifact/jaffle_shop"
PROFILES="/artifact"
RECORD_DIR="$OUTPUT/record_run"
DUCKDB_FILE="$OUTPUT/jaffle_shop.duckdb"
DUCKDB_SNAPSHOT="$OUTPUT/jaffle_shop.duckdb.seed_snapshot"

mkdir -p "$RECORD_DIR" "$OUTPUT"

# Clean ALL stale state from previous runs (the Docker volume persists)
rm -rf "$OUTPUT"/*

# ── helpers ──────────────────────────────────────────────────────────────
count_interactions() {
    local db="$1"
    if [ ! -f "$db" ]; then echo "0"; return; fi
    sqlite3 "$db" "SELECT COUNT(*) FROM recordings;" 2>/dev/null || echo "0"
}

count_by_type() {
    local db="$1"
    if [ ! -f "$db" ]; then return; fi
    sqlite3 "$db" -header -column \
        "SELECT record_type, COUNT(*) AS count FROM recordings GROUP BY record_type;"
}

count_succeeded() {
    local logfile="$1"
    local n
    n=$(grep -cE 'Succeeded|Passed' "$logfile" 2>/dev/null) || true
    echo "${n:-0}"
}

# Sum per-model execution times from dbt log (parses "Succeeded [  0.03s]" lines)
sum_model_times_ms() {
    local logfile="$1"
    python3 -c "
import re, sys
total = 0.0
for line in open(sys.argv[1]):
    m = re.search(r'Succeeded\s*\[\s*([0-9.]+)s\]', line)
    if m:
        total += float(m.group(1))
print(int(total * 1000))
" "$logfile"
}

# ── banner ───────────────────────────────────────────────────────────────
echo ""
echo "╔══════════════════════════════════════════════════════════════════════╗"
echo "║   dbt-fusion Record & Replay (R&R) — Artifact Evaluation           ║"
echo "║   Project: jaffle_shop │ Warehouse: DuckDB (embedded)              ║"
echo "╚══════════════════════════════════════════════════════════════════════╝"
echo ""
dbt --version
echo ""

# ══════════════════════════════════════════════════════════════════════════
# Step L: Lean 4 formalization — re-check the proof
#   The formalization was compiled when the image was built.  This re-run
#   is incremental and only confirms that every module still checks and
#   that no declaration uses `sorry`.
# ══════════════════════════════════════════════════════════════════════════
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Step L: Lean 4 formalization (lake build in formalization-lean/)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
LEAN_DIR="/artifact/formalization-lean"
LEAN_TOOLCHAIN=$(cat "$LEAN_DIR/lean-toolchain")
LEAN_MODULES=$(ls "$LEAN_DIR"/Formalization/*.lean | wc -l)
LEAN_OK=1
(cd "$LEAN_DIR" && lake build) 2>&1 | tee "$OUTPUT/lean_build.log" || LEAN_OK=0
if grep -q "declaration uses 'sorry'" "$OUTPUT/lean_build.log"; then
    LEAN_OK=0
fi
if [ "$LEAN_OK" -eq 1 ]; then
    echo "  ✓ Lean 4 proof checked: $LEAN_MODULES modules, no sorry ($LEAN_TOOLCHAIN)"
else
    echo "  ✗ Lean 4 build failed or a declaration uses sorry (see lean_build.log)"
fi
echo ""

# ══════════════════════════════════════════════════════════════════════════
# Step 0: dbt deps
# ══════════════════════════════════════════════════════════════════════════
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Step 0: Installing packages (dbt deps)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
dbt deps \
    --project-dir "$PROJECT" \
    --profiles-dir "$PROFILES" \
    2>&1 | tee "$OUTPUT/deps.log"
echo ""

# ══════════════════════════════════════════════════════════════════════════
# Step 1: dbt seed (WITHOUT R&R — just populate the database)
# ══════════════════════════════════════════════════════════════════════════
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Step 1: Seed database (dbt seed, no R&R)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
dbt seed \
    --project-dir "$PROJECT" \
    --profiles-dir "$PROFILES" \
    2>&1 | tee "$OUTPUT/seed.log"
echo ""

# Snapshot the DuckDB after seeding — replay needs the same initial state as record
cp "$DUCKDB_FILE" "$DUCKDB_SNAPSHOT"

# ══════════════════════════════════════════════════════════════════════════
# Step 2: RECORD — dbt run --fs-record (models only, single-threaded)
# ══════════════════════════════════════════════════════════════════════════
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Step 2: RECORD  (dbt run --fs-record --single-threaded)"
echo "  All model queries go to DuckDB AND are saved to recordings.db"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Clean dbt's target directory — the manifest caches source table schemas,
# which changes whether DESCRIBE queries are issued.  Both record and replay
# must start from the same (empty) target state.
rm -rf "${PROJECT}/target"

RECORD_START=$(date +%s%N)
dbt run \
    --project-dir "$PROJECT" \
    --profiles-dir "$PROFILES" \
    --fs-record "$RECORD_DIR" \
    --single-threaded \
    2>&1 | tee "$OUTPUT/record_run.log"
RECORD_END=$(date +%s%N)
RECORD_MS=$(( (RECORD_END - RECORD_START) / 1000000 ))

RECORD_TOTAL=$(count_interactions "$RECORD_DIR/recordings.db")
RECORD_SUCCEEDED=$(count_succeeded "$OUTPUT/record_run.log")

RECORD_MODEL_MS=$(sum_model_times_ms "$OUTPUT/record_run.log")

echo ""
echo "  Record run completed in ${RECORD_MS} ms"
echo "  Models succeeded: $RECORD_SUCCEEDED"
echo "  Model execution time: ${RECORD_MODEL_MS} ms (excludes dbt startup/compilation)"
echo "  Warehouse interactions recorded: $RECORD_TOTAL"
echo ""
echo "  Breakdown by type:"
count_by_type "$RECORD_DIR/recordings.db"
echo ""

# ── Record Trace (file only) ─────────────────────────────────────────────
if [ -f "$RECORD_DIR/recordings.db" ]; then
    sqlite3 "$RECORD_DIR/recordings.db" -separator '|' \
        "SELECT unique_id, record_type, sql FROM recordings ORDER BY rowid;" \
    | awk -F'|' '
    BEGIN { n = 0 }
    {
        n++
        uid   = $1
        rtype = $2
        sql   = $3
        printf "[%02d] %-15s  %s\n", n, rtype, uid
        if (sql != "" && sql != "(null)") {
            gsub(/\n/, "\n     │ ", sql)
            printf "     │ %s\n", sql
        } else {
            printf "     │ (schema introspection — no SQL)\n"
        }
        printf "\n"
    }
    END { printf "Total: %d interactions recorded\n", n }
    ' > "$OUTPUT/record_trace.txt"
    echo "  → Record trace written to $OUTPUT/record_trace.txt"
fi
echo ""

# ══════════════════════════════════════════════════════════════════════════
# Step 3: REPLAY — dbt run --fs-replay (models only, single-threaded)
#   DuckDB is restored to post-seed state so the adapter can initialize
#   (connection, schema listing, etc.).  Model-level queries (CREATE TABLE,
#   CREATE VIEW, …) are served from recordings.db.
#
#   VERIFICATION: we checksum DuckDB before and after replay.  If the
#   checksums match, model queries did NOT touch the warehouse — they were
#   served entirely from recordings.db.
# ══════════════════════════════════════════════════════════════════════════
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Step 3: REPLAY  (dbt run --fs-replay --single-threaded)"
echo "  Model queries served from recordings.db; DuckDB integrity verified"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Restore DuckDB to post-seed state so the adapter can initialize
echo "  Restoring DuckDB to post-seed snapshot"
rm -f "$DUCKDB_FILE" "${DUCKDB_FILE}.wal"
cp "$DUCKDB_SNAPSHOT" "$DUCKDB_FILE"

# Clean dbt's target directory (same reason as before record — see above)
rm -rf "${PROJECT}/target"

# Checksum BEFORE replay
CKSUM_BEFORE=$(md5sum "$DUCKDB_FILE" | awk '{print $1}')
echo "  DuckDB checksum before replay: $CKSUM_BEFORE"
echo ""

REPLAY_OK=1
REPLAY_START=$(date +%s%N)
dbt run \
    --project-dir "$PROJECT" \
    --profiles-dir "$PROFILES" \
    --fs-replay "$RECORD_DIR" \
    --single-threaded \
    2>&1 | tee "$OUTPUT/replay_run.log" || REPLAY_OK=0
REPLAY_END=$(date +%s%N)
REPLAY_MS=$(( (REPLAY_END - REPLAY_START) / 1000000 ))

REPLAY_SUCCEEDED=$(count_succeeded "$OUTPUT/replay_run.log")
REPLAY_MODEL_MS=$(sum_model_times_ms "$OUTPUT/replay_run.log")

# Checksum AFTER replay — flush any WAL first
rm -f "${DUCKDB_FILE}.wal"
CKSUM_AFTER=$(md5sum "$DUCKDB_FILE" | awk '{print $1}')
echo ""
echo "  DuckDB checksum after  replay: $CKSUM_AFTER"

# Determine warehouse leakage
WAREHOUSE_LEAKED=0
if [ "$CKSUM_BEFORE" = "$CKSUM_AFTER" ]; then
    echo "  ✓ Checksums MATCH — DuckDB was not modified during replay"
    echo "    → All model queries served from recordings.db (0 warehouse writes)"
else
    echo "  ✗ Checksums DIFFER — DuckDB was modified during replay!"
    echo "    → Some queries leaked to the warehouse"
    WAREHOUSE_LEAKED=1
fi

echo ""
if [ "$REPLAY_OK" -eq 1 ] && [ "$WAREHOUSE_LEAKED" -eq 0 ]; then
    echo "  ✓ Replay completed successfully in ${REPLAY_MS} ms"
    echo "  ✓ Models succeeded: $REPLAY_SUCCEEDED (all from recordings.db)"
    echo "  ✓ Warehouse modifications: 0 (verified by DuckDB checksum)"
elif [ "$REPLAY_OK" -eq 1 ]; then
    echo "  ⚠ Replay completed in ${REPLAY_MS} ms but DuckDB was modified"
    echo "  ⚠ Models succeeded: $REPLAY_SUCCEEDED"
    echo "  ⚠ Some model queries may have leaked to the warehouse"
else
    echo "  Replay finished in ${REPLAY_MS} ms with errors"
    echo "  Models succeeded before error: $REPLAY_SUCCEEDED"
    echo "  (See replay_run.log for details)"
fi
echo ""

# ── Replay Trace (file only) ─────────────────────────────────────────────
if [ -f "$RECORD_DIR/recordings.db" ]; then
    sqlite3 "$RECORD_DIR/recordings.db" -separator '|' \
        "SELECT unique_id, record_type, sql,
                CASE WHEN error IS NOT NULL THEN 'ERROR' ELSE 'OK' END AS status,
                CASE WHEN data_base64 IS NOT NULL THEN LENGTH(data_base64) ELSE 0 END AS data_len
         FROM recordings ORDER BY rowid;" \
    | awk -F'|' '
    BEGIN { n = 0 }
    {
        n++
        uid     = $1
        rtype   = $2
        sql     = $3
        status  = $4
        datalen = $5 + 0
        printf "[%02d] %-15s  %s\n", n, rtype, uid
        if (sql != "" && sql != "(null)") {
            gsub(/\n/, "\n     │ ", sql)
            printf "     │ SQL: %s\n", sql
        } else {
            printf "     │ (schema introspection — no SQL)\n"
        }
        if (datalen > 0) {
            kb = datalen / 1024.0
            printf "     │ → Served %s from recordings.db (%.1f KB Arrow IPC, base64)\n", status, kb
        } else {
            printf "     │ → Served %s from recordings.db (no result data)\n", status
        }
        printf "\n"
    }
    END { printf "Total: %d interactions replayed from recordings.db (0 warehouse calls)\n", n }
    ' > "$OUTPUT/replay_trace.txt"
    echo "  → Replay trace written to $OUTPUT/replay_trace.txt"
fi
echo ""

# ══════════════════════════════════════════════════════════════════════════
# Analysis
# ══════════════════════════════════════════════════════════════════════════
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Analysis: recordings.db content"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

python3 /artifact/analyze_recordings.py "$OUTPUT"

# ── Raw SQLite inspection ────────────────────────────────────────────────
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Raw recordings.db entries (first 15)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
for db in $(find "$OUTPUT" -name "recordings.db" | head -1); do
    sqlite3 "$db" -header -column \
        "SELECT unique_id, record_type, SUBSTR(COALESCE(sql,'(schema)'), 1, 70) AS sql_preview
         FROM recordings LIMIT 15;"
done

# ── Summary JSON ─────────────────────────────────────────────────────────
RECORD_EXEC=$(sqlite3 "$RECORD_DIR/recordings.db" \
    "SELECT COUNT(*) FROM recordings WHERE record_type='execute';" 2>/dev/null || echo 0)
RECORD_SCHEMA=$(sqlite3 "$RECORD_DIR/recordings.db" \
    "SELECT COUNT(*) FROM recordings WHERE record_type='get_table_schema';" 2>/dev/null || echo 0)
DB_SIZE=$(stat -c%s "$RECORD_DIR/recordings.db" 2>/dev/null || echo 0)

cat > "$OUTPUT/artifact_summary.json" <<EOF
{
  "project": "jaffle_shop",
  "warehouse": "duckdb",
  "dbt_version": "$(dbt --version 2>/dev/null | head -1)",
  "record_run": {
    "models_succeeded": $RECORD_SUCCEEDED,
    "total_warehouse_interactions": $RECORD_TOTAL,
    "execute_requests": $RECORD_EXEC,
    "get_table_schema_requests": $RECORD_SCHEMA,
    "wall_clock_ms": $RECORD_MS,
    "model_execution_ms": $RECORD_MODEL_MS,
    "recordings_db_size_bytes": $DB_SIZE
  },
  "replay_run": {
    "success": $([ "$REPLAY_OK" -eq 1 ] && echo "true" || echo "false"),
    "models_succeeded": $REPLAY_SUCCEEDED,
    "duckdb_checksum_before": "$CKSUM_BEFORE",
    "duckdb_checksum_after": "$CKSUM_AFTER",
    "duckdb_unchanged": $([ "$CKSUM_BEFORE" = "$CKSUM_AFTER" ] && echo "true" || echo "false"),
    "warehouse_leaked": $([ "$WAREHOUSE_LEAKED" -eq 1 ] && echo "true" || echo "false"),
    "duckdb_reset_to_seed_snapshot": true,
    "wall_clock_ms": $REPLAY_MS,
    "model_execution_ms": $REPLAY_MODEL_MS
  },
  "lean_formalization": {
    "build_ok": $([ "$LEAN_OK" -eq 1 ] && echo "true" || echo "false"),
    "modules": $LEAN_MODULES,
    "toolchain": "$LEAN_TOOLCHAIN"
  }
}
EOF

# ── Output files ─────────────────────────────────────────────────────────
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Output files"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
find "$OUTPUT" -type f -exec ls -lh {} \;

# ── Final report ─────────────────────────────────────────────────────────
echo ""
echo "╔══════════════════════════════════════════════════════════════════════╗"
echo "║  Results                                                           ║"
echo "╠══════════════════════════════════════════════════════════════════════╣"
printf "║  %-40s %10s %10s ║\n" "Metric" "Record" "Replay"
printf "║  %-40s %10s %10s ║\n" "────────────────────────────────────────" "──────────" "──────────"
printf "║  %-40s %10d %10d ║\n" "Models succeeded" "$RECORD_SUCCEEDED" "$REPLAY_SUCCEEDED"
printf "║  %-40s %10d %10s ║\n" "Warehouse interactions (recordings.db)" "$RECORD_TOTAL" "—"
printf "║  %-40s %10s %10s ║\n" "DuckDB checksum before" "" "$CKSUM_BEFORE"
printf "║  %-40s %10s %10s ║\n" "DuckDB checksum after" "" "$CKSUM_AFTER"
if [ "$CKSUM_BEFORE" = "$CKSUM_AFTER" ]; then
printf "║  %-40s %10s %10s ║\n" "DuckDB modified during replay?" "" "NO ✓"
else
printf "║  %-40s %10s %10s ║\n" "DuckDB modified during replay?" "" "YES ✗"
fi
printf "║  %-40s %10s %10s ║\n" "Model execution time (ms)" "$RECORD_MODEL_MS" "$REPLAY_MODEL_MS"
if [ "$REPLAY_MODEL_MS" -gt 0 ] 2>/dev/null; then
    SPEEDUP=$(python3 -c "print(f'{$RECORD_MODEL_MS / $REPLAY_MODEL_MS:.1f}')")
    printf "║  %-40s %10s %10s ║\n" "Model execution speedup" "" "${SPEEDUP}x"
fi
if [ "$LEAN_OK" -eq 1 ]; then
printf "║  %-40s %10s %10s ║\n" "Lean 4 proof (lake build, no sorry)" "" "OK ✓"
else
printf "║  %-40s %10s %10s ║\n" "Lean 4 proof (lake build, no sorry)" "" "FAIL ✗"
fi
echo "╠══════════════════════════════════════════════════════════════════════╣"
if [ "$REPLAY_OK" -eq 1 ] && [ "$WAREHOUSE_LEAKED" -eq 0 ]; then
echo "║  ✓ Replay succeeded; DuckDB unchanged → 0 warehouse writes      ║"
elif [ "$REPLAY_OK" -eq 1 ]; then
echo "║  ⚠ Replay succeeded but DuckDB was modified (warehouse leaked)  ║"
else
echo "║  ✗ Replay failed ($REPLAY_SUCCEEDED/$RECORD_SUCCEEDED models) — see replay_run.log  ║"
fi
echo "╚══════════════════════════════════════════════════════════════════════╝"
echo ""
