# Formalization of REST's replay-soundness guarantee

A Lean 4 mechanization of the record-and-replay soundness argument
(no Mathlib dependency — pure Lean 4 core). Builds with `lake build`
from this directory; currently zero `sorry` across the whole package.

## Current state — start here

*(Last updated 2026-10-20, Module 5 added. Everything below "Structure" is historical session
narrative, kept for the record; this section alone should be enough to pick
the work back up.)*

**Verify first:** `lake build` from this directory finishes with zero `sorry`
(only deprecation/cosmetic linter warnings). `#print axioms` on any theorem
shows only `propext`/`Classical.choice`/`Quot.sound`.

### Architecture

One argument, stated once, instantiated at every boundary and every notion of
equivalence:

- **`Level`** (Module 1): a boundary's call-level semantics — call type, state
  step, answer, `target`, `reads`. `driverLevel` (calls are `Statement`s) and an
  adapter level (`AdapterSem`, calls are `AdapterCall`s) are the two instances;
  `T2₂` is the argument at the driver level, `T2₁` at an adapter level.
- **`Module1.Eqv`**: the T2 chain (`stepAgree` … `T2_of_A`), over any `Level`
  and up to an abstract equivalence (`LevelSoundT`, `~_R`, `NextTildeInsensitive`).
  Module 1's own equality theorems are the special case (`T2_of_A_eq`). The
  adapter-boundary core is `T2_adapter`: it builds adapter-level runs
  (`toAdapterT`) from recorded driver-boundary runs and a `RunLinkT` and
  transports the conclusion back, so no assumption relates two engines' `δ`.
- **Replay matches calls, never turns** (all modules). Serving a live call looks at
  the one recorded event at the cursor; a turn only groups its calls and says that
  the result served for its *last* call is the turn's result. Module 1's replay is
  generic in the call-match relation (`serveCall`/`serveCalls`, `replayEvWith`,
  `ConvergentReplayWith`, `PerTurnAlignedWith`, `callsB_agree_of_aligned_with`);
  Module 1 instantiates it at equality, Module 2 at `CVEquiv`.
- **Module 2**: normalization. Its driver-level facades (`T2_of_A`, `stepAgreeT`,
  `driverLevel_soundT`) and the `CVEquiv` instance of the replay layer
  (`ConvergentReplayT`, …); `T2_2`/`T2_1` derive `(A~)` from replay and call the
  core. The core's write-turn hypothesis `hAWrite` asks only for agreement of the
  *effect calls* (`effCalls`: the calls that have a target) of the two engines.
- **Module 3**: segments, call by call. A method map `cls : MethodName → Cls`
  classifies every call as a read or a write. A node's recording is its flat call
  stream, and a *segment number* counts the write calls before a call. Replay keeps
  one number per node, the write barriers consumed: a live write must match the
  recorded write with that barrier number; a live read may match any recorded read
  of the current segment and is never consumed (`MatchCall`). The pure layer
  (`InRec`, `MatchAll`, `ServeTurn`, `ReplaySeg`, `ConvergentReplaySeg`, `turn_serve`,
  `served_last`) is combinatorics only. The semantic layer adds `callResAt`
  (per-call recorded results), `stateAtCall`, `crossReadAgree`, and
  `replay_hAWrite`/`replay_hReadRes`, from which `T2₂`/`T2₁` follow. Two hypotheses
  are new: `ClsTruthful` (a call classified `read` has no target) and
  `SameBarrierCount` (both engines issue as many write calls for each statement;
  without it a live turn can borrow a neighbour's write barrier).
- **Module 4**: cross-node lookup (D16 rule 3), at the call level. `MatchCallX` is
  `MatchCall` with rule 3 as a fallback for reads; replay and the extraction lemmas
  are Module 3's, instantiated at it (`ReplayWith`, `replay_hAWrite_with`,
  `replay_hReadRes_with`). `StandIn L cw cn h` is the call-level definition: two arbitrary
  calls of a boundary, a wide `cw` and a narrow `cn`, and a converter `h` between their answers
  (`(ans S cw).map h ≈ ans S cn` at every state, `h` respects `~_R`); a boundary has one answer type, so
  the two answers may be relations of different schemas. `Allowed` is a set of such triples
  (`StandInSet L Allowed`: every member is valid), and `XServe` is the rule-3 predicate for one live call
  over that set, with the lookup's footprint `L.reads cn`; `xServe_hX` is the soundness step `T2₂`/`T2₁`
  consume, `xServe_sound` the sanity statement against `R₁`'s own result.
- **Module 5**: write-commutative regions ("runs"), inside one turn. A block of calls is a list of calls of
  a boundary; two blocks *commute* (`BlockCommute`) when, at every state, either order leaves `~`-equal
  states. A turn's write calls, read in the order `π`, are a valid run (`RunCert L ws π`) when they split
  into blocks that a `BlockPerm` (adjacent swaps of commuting blocks) rearranges into `permList ws π`
  (`blockPerm_fold`: this preserves the effect). Replay (`MatchCallXR`) is Module 4's matcher with the write
  clause served from the barrier `ρ s c` instead of `c`; `RunSpec` bundles the run data (`ρ` stays inside
  a turn, a write turn's order is a `RunCert`, reads are not reordered). `replay_hAWriteP` derives the T2
  core's write-turn hypothesis `WriteAgree` (Module 1; pointwise `≈` of the effect calls is its special
  case) from a convergent replay and a `RunCert`. Module 5's `T2_2`/`T2_1` are Module 4's with that
  matcher. A turn's objects live inside its own target, so a bundle reads its target (`StaticPrec`
  allows it).
- **`Example.lean`**: a small dbt project (source-existence check, catalog node with
  three reads, staging model, mart, a row-count report node, and a `dims` node that materializes two
  schema/view bundles) run under two dbt versions and two schedules.
  Both `Module5.T2_2` and `Module5.T2_1` are invoked on it with every hypothesis
  discharged (`main_T2_2`, `main_T2_1`).

### Non-vacuity

A mechanized theorem is only informative if its hypotheses are satisfiable.
`Example.lean` checks this for the headline results `Module5.T2_2` and
`Module5.T2_1` on a concrete dbt project (five nodes, four tables, two dbt versions,
two schedules):

- **Every hypothesis is discharged** by a concrete proof, not assumed
  (`main_T2_2`, `main_T2_1`).
- **The conclusion is a real equivalence, not equality.** The two final states
  differ (`final_states_differ`) — the replaying version renders rows in a
  different order — yet are equivalent under `~_R`. The schedules differ too
  (`schedules_differ`).
- **Reads are really reordered within a segment.** At the driver boundary the two
  reads of `audit` normalize to the same call, so each live read is served by the
  *other's* recorded read: the replayed history differs from the recorded one yet
  is `~` to it (`audit_reorders`).
- **Cross-node lookup (rule 3) actually fires, with two different stand-ins.** The recording version
  checks a source with `probe_relation`, the replaying version with `get_relation`; no recorded read of the
  segment matches, and without rule 3 the staging node's recording cannot be replayed at all
  (`rule3_necessary_driver`, `rule3_necessary_adapter`). Likewise the `report` node's row count
  (`select count(*)` recorded, `row_count` replayed) is served from `audit`'s recorded `select *`
  through a converter that changes the result schema (`countOf`), and is equally necessary
  (`rule3_necessary_report_driver`, `rule3_necessary_report_adapter`, `countOf_changes_schema`).
  The `Allowed` set holds both a family and a single pair (`standIns_distinct`).
- **Write-commutative runs actually fire.** The `dims` node materializes two bundles
  (`create schema k; create view k`); the recording version emits them in the order 1, 2, the replaying
  version in the order 2, 1. The calls inside a bundle do not commute (`bundle_order_matters`) but the two
  bundles do (`bundles_commute_driver`, `bundles_commute_adapter`), so the replay serves them as a run
  (`ρex`, `run_is_a_reordering`). Without runs, the recording cannot be replayed
  (`strict_replay_fails_dims_driver`, `strict_replay_fails_dims_adapter`), and the old pointwise
  write-turn hypothesis is false (`pointwise_write_agreement_fails`). The final states differ at `dim`
  (`dim_states_differ`) yet are equivalent.
- **`ClsTruthful` and `SameBarrierCount` are discharged** at both boundaries
  (`clsTruthful_driver`, `clsTruthful_adapter`, `sbc_driver`, `sbc_adapter`).

### Open

- **Where the model still differs from the Time Machine.** See
  `../implementation-deviations.md`, "TimeMachine matching": reads answered from an
  already-passed segment, the SQL-text classification of `execute`, write arguments
  validated rather than matched, the metadata-only superset cross-node rule, and
  the null return on non-deterministic nodes are not modeled.
- **Adapter answers share one type.** `Level.ans` returns a `Relation` for every call, and results are
  `Relation`s of arbitrary schema (a JSON blob is a one-column relation). Per-call result types were
  considered and not done: nothing in the proofs inspects `Relation`, so it would add bookkeeping
  without a new argument.
- **Runs: the commutation certificate is assumed, and runs lie inside one turn.** `RunCert` asks that
  the reordered bundles commute; the implementation's bundle formation and independence check
  (`../implementation-deviations.md`, "Run/bundle formation") are sufficient syntactic checks the model
  does not verify. Turns are atomic in the model (no call-level interleaving of nodes), a node's objects
  are exclusive (a schema shared across nodes by an idempotent `CREATE SCHEMA IF NOT EXISTS` is excluded),
  and a run cannot span turns; all three are recorded as deviations.
- **Reachability of `XServe`'s well-formedness in general.** The example exhibits a
  realistic instance (a recording version that checks existence with another
  call), but whether other engine differences hit the same shape is not
  established.

### Documentation conventions in force

- A module's top comment block is the only place allowed to narrate history
  ("old design", "abandoned"); comments after it describe the current code only.
- `recordingOf` (`Module1.lean`) is D7's `H(n, R₁.N+1)` — a node's statement
  history, boundary-independent — not `τ_B(R)`, which `eventsOf` computes *from*
  it. The call stream a replay is matched against is `eventsOf` (Modules 1–2) or
  `InRec` (Modules 3–4).

### File inventory

- `Formalization/Common.lean`, `Module1.lean` … `Module4.lean`, `Example.lean`.
- The `*_scratch.lean` files below are untracked working files, not part of the
  Lake package.
- `cross_node_standin_scratch.lean` — satisfiability witness for the old
  `Query`-level stand-in; superseded by `Example.lean` (kept for the record).
- `t2_2_scratch.lean` — shows `T2_2` is false if rule 3 is an unconstrained
  predicate; still the reason `XServe` carries real content.
- `fqns_refutation_scratch.lean` — stale, does not compile; documents the old
  `fqns` bug.
- `level_scratch.lean`, `eqv_scratch.lean`, `adapter_scratch.lean` — working
  files from developing the generic core; everything in them is now in
  `Module1.lean`. Safe to delete.
- `formalization.tex` — not part of the paper; Lean is the source of truth.

### Verification commands

```
cd papers/vldb27-revision/formalization-lean
lake build                                  # whole package, should be clean
grep -c sorry Formalization/*.lean          # all 0
```

## Structure

Single Lake package (`Formalization/`), connected by imports:

- `Common.lean` — D1/D2 ground truth (`Statement`, `Result`, `State`,
  `DriverCall`, `execS`).
- `Module1.lean` — D3–D9 and the baseline (exact-match) replay; the generic
  `Level` machinery; `Eqv`, the equivalence-parametrized T2 core; the
  adapter-boundary core (`AdapterSem`, `RunLinkT`, `T2_adapter`); Module 1's
  own `T2₁`/`T2₂` as the equality special case.
- `Module2.lean` — normalization (`~`): driver-level facades over `Eqv`, the
  `CVEquiv` instance of the replay layer, `T2₁`/`T2₂`.
- `Module3.lean` — segments, call by call (reads reorderable within a write-delimited
  stretch of calls), method classification, `T2₁`/`T2₂`.
- `Module4.lean` — cross-node lookup (D16 rule 3), call-level `StandIn`.
- `Module5.lean` — write-commutative regions (runs), inside one turn.
- `Example.lean` — the worked dbt project (see Architecture above).

Each module opens the previous one with `open … hiding <names>` and re-declares
only what changes. `../formalization-1.md` is the prose restatement of
Module 1; Lean is the source of truth and the prose can lag.
`../implementation-deviations.md` tracks gaps between the formal model and the
real Rust implementation (regex-based object identity, the write-independence
check, the SQL-deviation registry standing in for `~`, etc.).

## Design findings worth remembering

Each of these was found by building a witness or a proof, not by reading:

- **`StaticPrec` must be relational, not a tautology.** An early form made
  well-foundedness trivially true; it now ranges over the project's actual
  read-then-write pairs.
- **`ReadsSound` is stated per statement** (`ret S (qOf stmt)` for the statement
  supplying `reads`). A version quantifying the reads-supplying statement
  separately from the evaluated one was too strong to be satisfiable.
- **`DAGOrder` exempts same-node reader/writer pairs.** Without that, the
  "check exists, then create" idiom is unsatisfiable. The cost: cross-node serving
  needs the no-intervening-write side condition in `XServe`.
- **`ConvergentReplay` + `PerTurnAligned` replace bare consumability.** Bare
  consumability does not entail the replay reproduced the recorded history turn
  for turn (a longer turn can "borrow" a later turn's events); convergence is
  stated directly, with per-turn alignment of the event cursor.
- **Cross-node stand-in lives at the call level over `ret`/`ans`, not at an
  `fqns` predicate.** An `fqns`-per-call design is unsatisfiable (one
  `list_relations` serving two tables forces one value to equal two sets). A
  `WideSliceSound`-shaped axiom relating two recorded results directly is
  unsatisfiable for any genuine slicing (`i₁ = i₂` forces `h O r ≈ r`).
- **Rule 3 cannot be an unconstrained predicate**: `t2_2_scratch.lean` shows
  `T2₂` is false then. `XServe` (final-call, footprint-bounded, no-intervening-write)
  is what makes it sound.
- **`NextTildeInsensitive` is necessary** under normalization: histories agree
  only up to `~_Res`, so a `next` that branches on erased noise breaks T2.
