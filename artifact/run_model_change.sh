#!/usr/bin/env bash
# ============================================================================
# dbt-fusion Record & Replay — model-change scenarios
# ============================================================================
# Two scenarios, each starting from the pristine jaffle_shop project and a
# freshly seeded DuckDB:
#
#   Scenario 1  record → change model → replay
#               The recording is stale. EXPECT: replay fails with a
#               recorded/actual query mismatch at the changed model.
#
#   Scenario 2  record → change model → re-record → replay
#               The recording matches the changed model. EXPECT: replay
#               succeeds for every model and DuckDB is untouched.
#
# Before EVERY dbt run the caches are cleared (project target/ and logs/,
# ~/.cache/com.getdbt) and DuckDB is reset to the post-seed snapshot, so no
# run can see state left behind by the previous one.
#
# The change: customers.sql gains an `avg_order_value` column.
# ============================================================================
set -uo pipefail

OUTPUT="${ARTIFACT_OUTPUT_DIR:-/output}"
PROJECT="/artifact/jaffle_shop"
PROFILES="/artifact"
MC="$OUTPUT/model_change"
PRISTINE_MODELS="$MC/.pristine_models"
SNAPSHOT="$MC/seed_snapshot.duckdb"

# Separate DuckDB file from run_experiment.sh's (profiles.yml reads DUCKDB_PATH).
export DUCKDB_PATH="$MC/jaffle_shop.duckdb"
DB="$DUCKDB_PATH"

rm -rf "$MC"
mkdir -p "$MC"

# ── helpers ──────────────────────────────────────────────────────────────
banner() {
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "  $*"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
}

clear_cache() {
    rm -rf "$PROJECT/target" "$PROJECT/logs" "$HOME/.cache/com.getdbt"
}

reset_duckdb() {
    rm -f "$DB" "$DB.wal"
    cp "$SNAPSHOT" "$DB"
}

restore_models() {
    rm -rf "$PROJECT/models"
    cp -r "$PRISTINE_MODELS" "$PROJECT/models"
}

change_model() {
    python3 - "$PROJECT/models/marts/customers.sql" <<'PY'
import sys
path = sys.argv[1]
src = open(path).read()
anchor = "        customer_orders_summary.lifetime_spend,\n"
assert anchor in src, "anchor line not found in customers.sql"
added = ("        customer_orders_summary.lifetime_spend"
         " / nullif(customer_orders_summary.count_lifetime_orders, 0)"
         " as avg_order_value,\n")
open(path, "w").write(src.replace(anchor, anchor + added, 1))
PY
}

md5() { [ -f "$1" ] && md5sum "$1" | cut -c1-32 || echo "missing"; }
rows() { sqlite3 "$1" "SELECT COUNT(*) FROM recordings;" 2>/dev/null || echo 0; }

# run_dbt <record|replay> <recordings dir> <log file>
# Sets: RUN_EXIT RUN_OK_MODELS RUN_DB_BEFORE RUN_DB_AFTER
run_dbt() {
    local mode="$1" rec="$2" log="$3"
    clear_cache
    reset_duckdb
    RUN_DB_BEFORE=$(md5 "$DB")
    echo "  cache cleared, DuckDB reset (md5 ${RUN_DB_BEFORE:0:12}); dbt run --fs-$mode $rec"
    dbt run \
        --project-dir "$PROJECT" \
        --profiles-dir "$PROFILES" \
        "--fs-$mode" "$rec" \
        --single-threaded \
        > "$log" 2>&1
    RUN_EXIT=$?
    rm -f "$DB.wal"
    RUN_DB_AFTER=$(md5 "$DB")
    RUN_OK_MODELS=$(grep -c 'Succeeded' "$log" || true)
    echo "  → exit=$RUN_EXIT, models succeeded=$RUN_OK_MODELS ($(basename "$log"))"
}

# ══════════════════════════════════════════════════════════════════════════
# Setup: deps, seed, snapshot, pristine copy of the models
# ══════════════════════════════════════════════════════════════════════════
banner "Model-change setup: deps, seed, snapshot"
cp -r "$PROJECT/models" "$PRISTINE_MODELS"
clear_cache
dbt deps --project-dir "$PROJECT" --profiles-dir "$PROFILES" > "$MC/deps.log" 2>&1
rm -f "$DB" "$DB.wal"
dbt seed --project-dir "$PROJECT" --profiles-dir "$PROFILES" > "$MC/seed.log" 2>&1 \
    || { echo "  seed failed — see $MC/seed.log"; exit 1; }
cp "$DB" "$SNAPSHOT"
echo "  seeded; snapshot at $SNAPSHOT"

# ══════════════════════════════════════════════════════════════════════════
# Scenario 1: record → change model → replay   (expect FAIL)
# ══════════════════════════════════════════════════════════════════════════
S1="$MC/scenario1_no_rerecord"
mkdir -p "$S1"
banner "Scenario 1: record → change model (no re-record) → replay   [expect FAIL]"
restore_models

echo "[1/3] record (original models)"
run_dbt record "$S1/recordings" "$S1/1_record.log"
S1_RECORD_EXIT=$RUN_EXIT
S1_MODELS=$RUN_OK_MODELS
python3 /artifact/model_change_trace.py dump "$S1/recordings/recordings.db" "$S1/record_trace.txt"
S1_REC_MD5=$(md5 "$S1/recordings/recordings.db")
S1_REC_ROWS=$(rows "$S1/recordings/recordings.db")
echo "  recordings.db: $S1_REC_ROWS interactions"

echo "[2/3] change model: customers.sql += avg_order_value (NOT re-recorded)"
change_model
diff -u "$PRISTINE_MODELS/marts/customers.sql" "$PROJECT/models/marts/customers.sql" \
    | sed "s|$PRISTINE_MODELS|models (original)|; s|$PROJECT/models|models (changed)|" \
    > "$S1/model_change.diff"

echo "[3/3] replay against the stale recording"
run_dbt replay "$S1/recordings" "$S1/3_replay.log"
S1_REPLAY_EXIT=$RUN_EXIT
S1_REPLAY_OK=$RUN_OK_MODELS
S1_DB_UNCHANGED=$([ "$RUN_DB_BEFORE" = "$RUN_DB_AFTER" ] && echo true || echo false)
S1_REC_UNCHANGED=$([ "$S1_REC_MD5" = "$(md5 "$S1/recordings/recordings.db")" ] && echo true || echo false)
S1_MISMATCH=$(grep -oE 'do not match \(unique_id: [^)]+\)' "$S1/3_replay.log" | head -1)

if [ "$S1_REPLAY_EXIT" -ne 0 ] && [ -n "$S1_MISMATCH" ]; then
    S1_VERDICT="AS EXPECTED"
else
    S1_VERDICT="UNEXPECTED"
fi
echo "  mismatch: ${S1_MISMATCH:-none}"
echo "  recordings.db unchanged by replay: $S1_REC_UNCHANGED; DuckDB unchanged: $S1_DB_UNCHANGED"
echo "  ⇒ Scenario 1: replay $([ "$S1_REPLAY_EXIT" -eq 0 ] && echo succeeded || echo failed) — $S1_VERDICT"

# ══════════════════════════════════════════════════════════════════════════
# Scenario 2: record → change model → re-record → replay   (expect SUCCESS)
# ══════════════════════════════════════════════════════════════════════════
S2="$MC/scenario2_rerecord"
mkdir -p "$S2"
banner "Scenario 2: record → change model → re-record → replay   [expect SUCCESS]"
restore_models

echo "[1/4] record (original models)"
run_dbt record "$S2/recordings" "$S2/1_record.log"
S2_RECORD_EXIT=$RUN_EXIT
python3 /artifact/model_change_trace.py dump "$S2/recordings/recordings.db" "$S2/record_trace.txt"
cp "$S2/recordings/recordings.db" "$S2/recordings_before_rerecord.db"
S2_REC_ROWS=$(rows "$S2/recordings/recordings.db")
echo "  recordings.db: $S2_REC_ROWS interactions"

echo "[2/4] change model: customers.sql += avg_order_value"
change_model
diff -u "$PRISTINE_MODELS/marts/customers.sql" "$PROJECT/models/marts/customers.sql" \
    | sed "s|$PRISTINE_MODELS|models (original)|; s|$PROJECT/models|models (changed)|" \
    > "$S2/model_change.diff"

echo "[3/4] re-record (changed models, same recordings directory)"
run_dbt record "$S2/recordings" "$S2/3_rerecord.log"
S2_RERECORD_EXIT=$RUN_EXIT
S2_MODELS=$RUN_OK_MODELS
python3 /artifact/model_change_trace.py dump "$S2/recordings/recordings.db" "$S2/rerecord_trace.txt"
python3 /artifact/model_change_trace.py compare \
    "$S2/recordings_before_rerecord.db" "$S2/recordings/recordings.db" "$S2/trace_compare.json"
diff -u "$S2/record_trace.txt" "$S2/rerecord_trace.txt" > "$S2/trace.diff"
S2_REREC_ROWS=$(rows "$S2/recordings/recordings.db")
S2_REC_MD5=$(md5 "$S2/recordings/recordings.db")

echo "[4/4] replay against the re-recorded recording"
run_dbt replay "$S2/recordings" "$S2/4_replay.log"
S2_REPLAY_EXIT=$RUN_EXIT
S2_REPLAY_OK=$RUN_OK_MODELS
S2_DB_UNCHANGED=$([ "$RUN_DB_BEFORE" = "$RUN_DB_AFTER" ] && echo true || echo false)
S2_REC_UNCHANGED=$([ "$S2_REC_MD5" = "$(md5 "$S2/recordings/recordings.db")" ] && echo true || echo false)

if [ "$S2_REPLAY_EXIT" -eq 0 ] && [ "$S2_REPLAY_OK" -eq "$S2_MODELS" ] && [ "$S2_DB_UNCHANGED" = true ]; then
    S2_VERDICT="AS EXPECTED"
else
    S2_VERDICT="UNEXPECTED"
fi
echo "  recordings.db unchanged by replay: $S2_REC_UNCHANGED; DuckDB unchanged: $S2_DB_UNCHANGED"
echo "  ⇒ Scenario 2: replay $([ "$S2_REPLAY_EXIT" -eq 0 ] && echo succeeded || echo failed) — $S2_VERDICT"

restore_models
rm -rf "$PRISTINE_MODELS"

# ══════════════════════════════════════════════════════════════════════════
# Summary
# ══════════════════════════════════════════════════════════════════════════
cat > "$MC/summary.json" <<EOF
{
  "dbt_version": "$(dbt --version 2>/dev/null | head -1)",
  "model_change": "customers.sql: added avg_order_value column",
  "cache_cleared_before_each_run": ["target/", "logs/", "~/.cache/com.getdbt", "DuckDB reset to seed snapshot"],
  "scenario1_no_rerecord": {
    "expected": "replay fails",
    "verdict": "$S1_VERDICT",
    "record_exit": $S1_RECORD_EXIT,
    "models_recorded": $S1_MODELS,
    "recorded_interactions": $S1_REC_ROWS,
    "replay_exit": $S1_REPLAY_EXIT,
    "replay_models_succeeded": $S1_REPLAY_OK,
    "replay_mismatch": "$S1_MISMATCH",
    "recordings_unchanged_by_replay": $S1_REC_UNCHANGED,
    "duckdb_unchanged_by_replay": $S1_DB_UNCHANGED
  },
  "scenario2_rerecord": {
    "expected": "replay succeeds",
    "verdict": "$S2_VERDICT",
    "record_exit": $S2_RECORD_EXIT,
    "recorded_interactions": $S2_REC_ROWS,
    "rerecord_exit": $S2_RERECORD_EXIT,
    "models_rerecorded": $S2_MODELS,
    "rerecorded_interactions": $S2_REREC_ROWS,
    "trace_changed_by_rerecord": $(python3 -c "import json;print(str(json.load(open('$S2/trace_compare.json'))['trace_changed']).lower())"),
    "replay_exit": $S2_REPLAY_EXIT,
    "replay_models_succeeded": $S2_REPLAY_OK,
    "recordings_unchanged_by_replay": $S2_REC_UNCHANGED,
    "duckdb_unchanged_by_replay": $S2_DB_UNCHANGED
  }
}
EOF

echo ""
echo "╔══════════════════════════════════════════════════════════════════════╗"
echo "║  Model-change scenarios                                             ║"
echo "╠══════════════════════════════════════════════════════════════════════╣"
printf "║  %-26s %-19s %-19s ║\n" "" "1: no re-record" "2: re-record"
printf "║  %-26s %-19s %-19s ║\n" "expected replay" "fail" "succeed"
printf "║  %-26s %-19s %-19s ║\n" "replay exit code" "$S1_REPLAY_EXIT" "$S2_REPLAY_EXIT"
printf "║  %-26s %-19s %-19s ║\n" "models succeeded" "$S1_REPLAY_OK/$S1_MODELS" "$S2_REPLAY_OK/$S2_MODELS"
printf "║  %-26s %-19s %-19s ║\n" "DuckDB unchanged" "$S1_DB_UNCHANGED" "$S2_DB_UNCHANGED"
printf "║  %-26s %-19s %-19s ║\n" "verdict" "$S1_VERDICT" "$S2_VERDICT"
echo "╚══════════════════════════════════════════════════════════════════════╝"
echo "  Details: $MC/summary.json"
echo ""

[ "$S1_VERDICT" = "AS EXPECTED" ] && [ "$S2_VERDICT" = "AS EXPECTED" ]
