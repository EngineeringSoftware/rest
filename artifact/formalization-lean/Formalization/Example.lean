/-
# A worked dbt project, and the headline theorems on it

A small dbt project run under two versions of dbt-core, to check that `Module5.T2_2` and
`Module5.T2_1` are not vacuous: every hypothesis is discharged by a concrete proof, the conclusion is
a real equivalence, and each relaxation the theorems rely on — normalization, reordering of reads
within a segment, cross-node lookup, write-commutative runs — actually fires. Replay is matched
**call by call**: every call is classified by its method (`cls`: only `ctas` writes) and served on its
own.

**The project.** Five nodes, four tables.

* `staging` — model `stg_orders`: first checks that its source `raw.orders` exists, then
  materializes `stg_orders := select * from raw.orders`.
* `audit` — a catalog node: lists the relations of the `raw` schema (`list_relations`, one wide call
  that answers existence for every source table at once), then reads `raw` twice, as
  `select *` and as `select * ... order by ... desc`.
* `marts` — model `daily_revenue := select count(*) from stg_orders`.
* `report` — a read-only node that asks for the row count of `raw`.
* `dims` — materializes two bundles into the table `dim`: for `k = 1, 2`, `create schema k` then
  `create view k` (the view is created only if its schema exists), and finally a `verify` read.

**The two dbt versions** (`E₁` recorded, `E₂` replaying) differ in ordinary ways.

* `E₁` checks that a source exists with a `probe_relation` call, `E₂` with `get_relation`. The
  recording of `staging` holds no `get_relation`, so the live call matches no recorded read of its
  segment: only cross-node lookup (serve `staging`'s `get_relation` from `audit`'s recorded
  `list_relations`) can replay it.
* `E₁` answers a row count with a `select count(*)` query, `E₂` with a dedicated `row_count` call
  (`count_rel`). Again nothing in `report`'s recorded segment matches, and rule 3 serves it from
  `audit`'s recorded `select *`, converted by `countOf` — a *different result schema*: three rows in, a
  one-row relation out.
* `E₂` renders `select *` with an explicit `ORDER BY ... DESC`, so the rows of `stg_orders` come back in
  a different order: the two final states are *not equal*, only equivalent under the row-order-insensitive
  `~_R`.
* At the driver boundary the two reads of `audit` normalize to the same call, so each live read may be
  served by either recorded read of the segment: the replay serves each from the *other's* record.
* `E₁` emits `dims`' bundles in the order 1, 2 and `E₂` in the order 2, 1. The two calls inside a bundle
  cannot be swapped (`bundle_order_matters`), but the two bundles commute (`bundles_commute_driver`,
  `bundles_commute_adapter`), so the replay serves them as a *run*: the live writes are served from the
  recorded barriers `2, 3, 0, 1` (`ρex`, `swapRun`). The final value of `dim` is `[10, 11, 20, 21]` under
  `E₁` and `[20, 21, 10, 11]` under `E₂`: equivalent, not equal.

**The object model.** `dim`'s value holds both sub-objects (schema and view): a call updates a part of
it, so it reads its own target, which `StaticPrec` allows. Every call of the turn targets `dim`
(`TargetFaithful` as before); the node owns `dim` (`UniqueWriterGlobal`).

**Two stand-ins.** `AllowedD`/`AllowedA` list the triples `(wide call, narrow call, converter)` rule 3 may
use: the family `list_relations ↦ get_relation O` (converter `slice O`, one per target set `O`) and the
single pair `select * ↦ row_count` (converter `countOf`). `standIn_driver`/`standIn_adapter` prove every
member valid. Third-party writes between a lookup and its source are allowed (`noInterv₂`: `staging` and
`marts` write between `audit`'s `select *` and `report`'s row count); only writes by the two nodes
involved would matter.

**Two schedules.** `audit`'s turns and `staging`'s check are interleaved differently in the two runs.
-/

import Formalization.Module5

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Formalization
namespace Example

open Formalization.Module1 hiding BehEquiv T2_1 T2_2 ReadsSound
open Formalization.Module1.Eqv hiding ObsEquiv BehEquiv
open Formalization.Module2 hiding T2_1 T2_2
open Formalization.Module3 (Cls isW nw Wt RecEv InRec MatchAll ServeTurn ReplaySeg ConvergentReplaySeg
  ReplayWith recEvsOf recResOf recResOf_last SameBarrierCount ClsTruthful ResLink resLink_driver
  MatcherSpec Wt_succ_of)
open Formalization.Module4 (StandIn StandInSet XServe MatchCallX)
open Formalization.Module5 (MatchCallXR ReplayOKXR RunSpec RunCert BlockCommute BlockPerm permList
  turnBase)

/-! ## The data model -/

inductive Tbl
  | raw | stg | mart | dim
  deriving DecidableEq

inductive Node
  | audit | staging | marts | report | dims
  deriving DecidableEq

/-- A relation is its list of rows; `~_R` is "same rows, any order" (`List.Perm`). -/
abbrev Rel := List Nat

instance relSetoid : Setoid Rel where
  r := List.Perm
  iseqv := ⟨fun l => List.Perm.refl l, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

def code : Tbl → Nat
  | .raw => 0 | .stg => 1 | .mart => 2 | .dim => 3

abbrev St := State Tbl Rel

def rows (S : St) (t : Tbl) : Rel := (S t).getD []

/-- Codes of the tables of schema `raw` that currently exist (only `raw.orders`). -/
def existingRaw (S : St) : List Nat :=
  match S .raw with
  | some _ => [0]
  | none => []

/-- Driver queries. `existsIn O` is the narrow metadata lookup ("which of `O`
exist?"), `listRaw` the wide one ("list the `raw` schema"). `probeIn O` answers the same question
as `existsIn O` through a different query (the dbt version that issues it does not use
`get_relation` for the check). -/
inductive Query
  | sel (src : Tbl)
  | selDesc (src : Tbl)
  | cnt (src : Tbl)
  | listRaw
  | existsIn (O : Tbl → Prop)
  | probeIn (O : Tbl → Prop)
  | rowCount (t : Tbl)
  | build
  | addSchema (k : Nat)
  | addView (k : Nat)
  | dimCount

open Classical in
noncomputable def keep (O : Tbl → Prop) (c : Nat) : Bool := decide (∃ t, code t = c ∧ O t)

noncomputable def ret : St → Query → Rel
  | S, .sel t => rows S t
  | S, .selDesc t => (rows S t).reverse
  | S, .cnt t => [(rows S t).length]
  | S, .listRaw => existingRaw S
  | S, .existsIn O => (existingRaw S).filter (keep O)
  | S, .probeIn O => (existingRaw S).filter (keep O)
  | S, .rowCount t => [(rows S t).length]
  | S, .build => rows S .dim
  | S, .addSchema k => rows S .dim ++ [10 * k]
  | S, .addView k => if 10 * k ∈ rows S .dim then rows S .dim ++ [10 * k + 1] else rows S .dim
  | S, .dimCount => [(rows S .dim).length]

/-- Ground-truth reads of a query. `existsIn O` reads exactly `O`. -/
def readsQ : Query → Tbl → Prop
  | .sel t, o => o = t
  | .selDesc t, o => o = t
  | .cnt t, o => o = t
  | .listRaw, o => o = .raw
  | .existsIn O, o => O o
  | .probeIn O, o => O o
  | .rowCount t, o => o = t
  | .build, o => o = .dim
  | .addSchema _, o => o = .dim
  | .addView _, o => o = .dim
  | .dimCount, o => o = .dim

abbrev Stmt := Statement Tbl Query

def reads : Stmt → Tbl → Prop
  | .write _ q, o => readsQ q o
  | .read q, o => readsQ q o

/-! ## Normalization: `~_S` on statements

`select ... order by ... desc` is the same query as `select ...` up to row order. -/

def normQ : Query → Query
  | .selDesc t => .sel t
  | q => q

def key : Stmt → Option Tbl × Bool × Query
  | .write o q => (some o, true, normQ q)
  | .read q => (none, false, normQ q)

instance stmtSetoid : Setoid Stmt where
  r s s' := key s = key s'
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

inductive Method
  | getRel | listRels | ctas | runQuery | probeRel | countRel

inductive Args
  | none
  | set (O : Tbl → Prop)
  | tq (t : Tbl) (q : Query)
  | q (q : Query)

/-- Adapter-call arguments are compared literally. -/
instance argsSetoid : Setoid Args where
  r := Eq
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-! ## Semantics lemmas -/

theorem rows_perm {S S' : St} {t : Tbl} (h : OptEquiv (S t) (S' t)) : rows S t ≈ rows S' t := by
  unfold rows
  cases hs : S t with
  | none =>
    cases hs' : S' t with
    | none => exact List.Perm.refl _
    | some b => rw [hs, hs'] at h; exact h.elim
  | some a =>
    cases hs' : S' t with
    | none => rw [hs, hs'] at h; exact h.elim
    | some b => rw [hs, hs'] at h; exact h

theorem existingRaw_eq {S S' : St} (h : OptEquiv (S .raw) (S' .raw)) :
    existingRaw S = existingRaw S' := by
  unfold existingRaw
  cases hs : S .raw with
  | none =>
    cases hs' : S' .raw with
    | none => rfl
    | some b => rw [hs, hs'] at h; exact h.elim
  | some a =>
    cases hs' : S' .raw with
    | none => rw [hs, hs'] at h; exact h.elim
    | some b => rfl

open Classical in
theorem keep_zero (O : Tbl → Prop) : keep O 0 = decide (O .raw) := by
  unfold keep
  rw [decide_eq_decide]
  constructor
  · rintro ⟨t, ht, hO⟩
    cases t with
    | raw => exact hO
    | stg => simp [code] at ht
    | mart => simp [code] at ht
    | dim => simp [code] at ht
  · intro h; exact ⟨.raw, rfl, h⟩

theorem filter_existingRaw_of_not (O : Tbl → Prop) (hO : ¬ O .raw) (S : St) :
    (existingRaw S).filter (keep O) = [] := by
  unfold existingRaw
  cases S .raw with
  | none => rfl
  | some _ => simp [List.filter, keep_zero, hO]

/-- **`(reads-sound-~)`** for queries: agreement (up to `~_R`) on a query's reads
gives `~_R`-equal answers. -/
theorem ret_agree (q : Query) {S S' : St}
    (h : ∀ o, readsQ q o → OptEquiv (S o) (S' o)) : ret S q ≈ ret S' q := by
  cases q with
  | sel t => exact rows_perm (h t rfl)
  | selDesc t =>
    exact (List.reverse_perm _).trans ((rows_perm (h t rfl)).trans (List.reverse_perm _).symm)
  | cnt t => show [(rows S t).length] ≈ [(rows S' t).length]; rw [(rows_perm (h t rfl)).length_eq]; exact List.Perm.refl _
  | listRaw => show existingRaw S ≈ existingRaw S'; rw [existingRaw_eq (h .raw rfl)]; exact List.Perm.refl _
  | existsIn O =>
    show (existingRaw S).filter (keep O) ≈ (existingRaw S').filter (keep O)
    by_cases hO : O .raw
    · rw [existingRaw_eq (h .raw hO)]; exact List.Perm.refl _
    · rw [filter_existingRaw_of_not O hO, filter_existingRaw_of_not O hO]; exact List.Perm.refl _
  | probeIn O =>
    show (existingRaw S).filter (keep O) ≈ (existingRaw S').filter (keep O)
    by_cases hO : O .raw
    · rw [existingRaw_eq (h .raw hO)]; exact List.Perm.refl _
    · rw [filter_existingRaw_of_not O hO, filter_existingRaw_of_not O hO]; exact List.Perm.refl _
  | rowCount t =>
    show [(rows S t).length] ≈ [(rows S' t).length]
    rw [(rows_perm (h t rfl)).length_eq]; exact List.Perm.refl _
  | build => exact rows_perm (h .dim rfl)
  | addSchema k => exact List.Perm.append_right _ (rows_perm (h .dim rfl))
  | addView k =>
    have hp := rows_perm (h .dim rfl)
    show (if 10 * k ∈ rows S .dim then rows S .dim ++ [10 * k + 1] else rows S .dim) ≈
      (if 10 * k ∈ rows S' .dim then rows S' .dim ++ [10 * k + 1] else rows S' .dim)
    by_cases hm : 10 * k ∈ rows S .dim
    · have hm' : 10 * k ∈ rows S' .dim := hp.mem_iff.mp hm
      rw [if_pos hm, if_pos hm']; exact List.Perm.append_right _ hp
    · have hm' : ¬ 10 * k ∈ rows S' .dim := fun h' => hm (hp.mem_iff.mpr h')
      rw [if_neg hm, if_neg hm']; exact hp
  | dimCount =>
    show [(rows S .dim).length] ≈ [(rows S' .dim).length]
    rw [(rows_perm (h .dim rfl)).length_eq]; exact List.Perm.refl _

/-- Full-state version: `~`-equivalent states give `~_R`-equal answers to every query. -/
theorem ret_stateEquiv (q : Query) {S S' : St} (h : StateEquiv S S') : ret S q ≈ ret S' q :=
  ret_agree q (fun o _ => h o)

theorem ret_norm (S : St) (q : Query) : ret S q ≈ ret S (normQ q) := by
  cases q <;> first | exact List.Perm.refl _ | exact List.reverse_perm _

/-! ## The project and the two engines -/

def Oraw : Tbl → Prop := fun t => t = .raw

def sCheck : Stmt := .read (.existsIn Oraw)
def sList : Stmt := .read .listRaw
def sSel : Stmt := .read (.sel .raw)
def sSelD : Stmt := .read (.selDesc .raw)
def sStg : Stmt := .write .stg (.sel .raw)
def sMart : Stmt := .write .mart (.cnt .stg)
def sCount : Stmt := .read (.rowCount .raw)
/-- The `dims` node's statement: materialize two schema/view bundles into the table `dim`. -/
def sBuild : Stmt := .write .dim .build

/-- `next`: each node's next statement depends only on how many turns it has taken. -/
def nxtF : Node → Nat → Option Stmt
  | .staging, 0 => some sCheck
  | .staging, 1 => some sStg
  | .audit, 0 => some sList
  | .audit, 1 => some sSel
  | .audit, 2 => some sSelD
  | .marts, 0 => some sMart
  | .report, 0 => some sCount
  | .dims, 0 => some sBuild
  | _, _ => none

def P : Project Node Tbl Query Rel := ⟨fun n H => nxtF n H.length⟩

abbrev Call := AdapterCall Method Args

/-- One bundle: create the schema `k`, then the view `k` in it. The view's creation depends on the schema
(see `ret` for `addView`), so the two calls cannot be reordered; two bundles can. -/
def bundleCalls (k : Nat) : List Call :=
  [⟨.ctas, .tq .dim (.addSchema k)⟩, ⟨.ctas, .tq .dim (.addView k)⟩]

/-- The check dbt runs after a build: the table's row count. -/
def verifyCall : Call := ⟨.runQuery, .q .dimCount⟩

/-- dbt v1 emits the bundles in the order 1, 2; dbt v2 in the order 2, 1 (both then verify). -/
def buildCalls₁ : List Call := bundleCalls 1 ++ bundleCalls 2 ++ [verifyCall]
def buildCalls₂ : List Call := bundleCalls 2 ++ bundleCalls 1 ++ [verifyCall]

/-- The statement `Write dim build` is the only one that fans out into several calls. -/
def isBld : Tbl → Query → Bool
  | .dim, .build => true
  | _, _ => false

/-- dbt v1 checks that a source exists with a `probe_relation` call (not `get_relation`), and lists
the schema with `list_relations`. -/
def alpha₁ : Stmt → List Call
  | .write .dim .build => buildCalls₁
  | .write t q => [⟨.ctas, .tq t q⟩]
  | .read (.existsIn O) => [⟨.probeRel, .set O⟩]
  | .read .listRaw => [⟨.listRels, .none⟩]
  | .read (.rowCount t) => [⟨.runQuery, .q (.cnt t)⟩]
  | .read q => [⟨.runQuery, .q q⟩]

/-- dbt v2 checks that a source exists with `get_relation`. -/
def alpha₂ : Stmt → List Call
  | .write .dim .build => buildCalls₂
  | .read (.existsIn O) => [⟨.getRel, .set O⟩]
  | .read (.rowCount t) => [⟨.countRel, .q (.rowCount t)⟩]
  | s => alpha₁ s

def delta₁ : Call → List (DriverCall Tbl Query)
  | ⟨.ctas, .tq t q⟩ => [.write t q]
  | ⟨.getRel, .set O⟩ => [.read (.existsIn O)]
  | ⟨.probeRel, .set O⟩ => [.read (.probeIn O)]
  | ⟨.listRels, _⟩ => [.read .listRaw]
  | ⟨.runQuery, .q q⟩ => [.read q]
  | ⟨.countRel, .q q⟩ => [.read q]
  | _ => []

/-- dbt v2 renders `select *` with an explicit `ORDER BY ... DESC`. -/
def rend : Query → Query
  | .sel t => .selDesc t
  | q => q

def delta₂ : Call → List (DriverCall Tbl Query)
  | ⟨.ctas, .tq t q⟩ => [.write t (rend q)]
  | c => delta₁ c

def E₁ : Engine Tbl Query Method Args := ⟨alpha₁, delta₁⟩
def E₂ : Engine Tbl Query Method Args := ⟨alpha₂, delta₂⟩

theorem drv₁_write (t : Tbl) (q : Query) (h : isBld t q = false) :
    drvE E₁ (.write t q) = [.write t q] := by
  cases t <;> cases q <;> first | rfl | exact absurd h (by simp [isBld])
theorem drv₂_write (t : Tbl) (q : Query) (h : isBld t q = false) :
    drvE E₂ (.write t q) = [.write t (rend q)] := by
  cases t <;> cases q <;> first | rfl | exact absurd h (by simp [isBld])

/-- The driver calls of `Write dim build`: the bundles in each engine's order, then the verify read. -/
def buildDrv₁ : List (DriverCall Tbl Query) :=
  [.write .dim (.addSchema 1), .write .dim (.addView 1), .write .dim (.addSchema 2),
    .write .dim (.addView 2), .read .dimCount]
def buildDrv₂ : List (DriverCall Tbl Query) :=
  [.write .dim (.addSchema 2), .write .dim (.addView 2), .write .dim (.addSchema 1),
    .write .dim (.addView 1), .read .dimCount]

theorem drv₁_build : drvE E₁ (.write .dim .build) = buildDrv₁ := rfl
theorem drv₂_build : drvE E₂ (.write .dim .build) = buildDrv₂ := rfl

/-- The query dbt v1 issues for a read: the existence check goes through `probeIn`. -/
def probeQ : Query → Query
  | .existsIn O => .probeIn O
  | .rowCount t => .cnt t
  | q => q

theorem ret_probeQ (S : St) (q : Query) : ret S (probeQ q) = ret S q := by cases q <;> rfl
theorem readsQ_probeQ (q : Query) (o : Tbl) : readsQ (probeQ q) o = readsQ q o := by
  cases q <;> rfl

theorem drv₁_read (q : Query) : drvE E₁ (.read q) = [.read (probeQ q)] := by cases q <;> rfl
theorem drv₂_read (q : Query) : drvE E₂ (.read q) = [.read q] := by cases q <;> rfl

/-! ## The model-level hypotheses -/

theorem reads_qOf (s : Stmt) (o : Tbl) : reads s o = readsQ (qOf s) o := by
  cases s <;> rfl

theorem readsSound : Module2.ReadsSound reads ret := by
  intro s S S' h
  exact ret_agree (qOf s) (fun o ho => h o (by rw [reads_qOf]; exact ho))

theorem key_normQ {s s' : Stmt} (h : key s = key s') : normQ (qOf s) = normQ (qOf s') := by
  cases s <;> cases s' <;> simp [key] at h
  · exact h.2
  · exact h

theorem key_target {s s' : Stmt} (h : key s = key s') : target s = target s' := by
  cases s <;> cases s' <;> simp [key, target] at h ⊢
  · exact h.1

theorem retCongruent : RetCongruent ret := by
  intro S s s' h
  have h' : normQ (qOf s) = normQ (qOf s') := key_normQ h
  exact (ret_norm S (qOf s)).trans (h' ▸ (ret_norm S (qOf s')).symm)

theorem targetPreserving : TargetPreserving Tbl Query := fun _ _ h => key_target h

theorem write_target₁ {o o' : Tbl} {q q' : Query}
    (h : Statement.write o' q' ∈ drvE E₁ (.write o q)) : o' = o := by
  by_cases hb : isBld o q = false
  · rw [drv₁_write o q hb] at h; simp at h; exact h.1
  · cases o <;> cases q <;> simp [isBld] at hb
    rw [drv₁_build] at h
    simp [buildDrv₁] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact h

theorem write_target₂ {o o' : Tbl} {q q' : Query}
    (h : Statement.write o' q' ∈ drvE E₂ (.write o q)) : o' = o := by
  by_cases hb : isBld o q = false
  · rw [drv₂_write o q hb] at h; simp at h; exact h.1
  · cases o <;> cases q <;> simp [isBld] at hb
    rw [drv₂_build] at h
    simp [buildDrv₂] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact h

theorem targetFaithful₁ : TargetFaithful E₁ := by
  refine ⟨?_, ?_⟩
  · intro o q o' q' h
    exact write_target₁ h
  · intro q o' q' h
    rw [drv₁_read] at h
    simp at h

theorem targetFaithful₂ : TargetFaithful E₂ := by
  refine ⟨?_, ?_⟩
  · intro o q o' q' h
    exact write_target₂ h
  · intro q o' q' h
    rw [drv₂_read] at h
    simp at h

theorem readsQ_rend (q : Query) (o : Tbl) : readsQ (rend q) o = readsQ q o := by
  cases q <;> rfl

theorem compiledReadsSound₁ : CompiledReadsSound reads E₁ := by
  intro s c hc o ho
  cases s with
  | write t q =>
    by_cases hb : isBld t q = false
    · rw [drv₁_write t q hb] at hc; simp at hc; subst hc; exact ho
    · cases t <;> cases q <;> simp [isBld] at hb
      rw [drv₁_build] at hc
      simp [buildDrv₁] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact ho
  | read q =>
    rw [drv₁_read] at hc; simp at hc; subst hc
    show readsQ q o
    rw [← readsQ_probeQ]; exact ho

theorem compiledReadsSound₂ : CompiledReadsSound reads E₂ := by
  intro s c hc o ho
  cases s with
  | write t q =>
    by_cases hb : isBld t q = false
    · rw [drv₂_write t q hb] at hc; simp at hc; subst hc
      show readsQ q o
      rw [← readsQ_rend]; exact ho
    · cases t <;> cases q <;> simp [isBld] at hb
      rw [drv₂_build] at hc
      simp [buildDrv₂] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact ho
  | read q => rw [drv₂_read] at hc; simp at hc; subst hc; exact ho

/-! ## The adapter level's own semantics `A`

What each adapter call reads, writes, does to state, and returns. Calls that
issue a query are defined by the query's driver semantics. -/

inductive Kind
  | ctas (t : Tbl) (q : Query)
  | getRel (O : Tbl → Prop)
  | probeRel (O : Tbl → Prop)
  | listRels
  | runQ (q : Query)
  | countQ (q : Query)
  | inert

def kind : Call → Kind
  | ⟨.ctas, .tq t q⟩ => .ctas t q
  | ⟨.getRel, .set O⟩ => .getRel O
  | ⟨.probeRel, .set O⟩ => .probeRel O
  | ⟨.listRels, _⟩ => .listRels
  | ⟨.runQuery, .q q⟩ => .runQ q
  | ⟨.countRel, .q q⟩ => .countQ q
  | _ => .inert

def upd (S : St) (t : Tbl) (v : Rel) : St := fun o => if o = t then some v else S o

noncomputable def Astep (S : St) (c : Call) : St :=
  match kind c with
  | .ctas t q => upd S t (ret S q)
  | _ => S

noncomputable def Aret (S : St) (c : Call) : Rel :=
  match kind c with
  | .getRel O => ret S (.existsIn O)
  | .probeRel O => ret S (.probeIn O)
  | .listRels => ret S .listRaw
  | .runQ q => ret S q
  | .countQ q => ret S q
  | _ => []

def Atarget (c : Call) : Option Tbl :=
  match kind c with
  | .ctas t _ => some t
  | _ => none

def Areads (c : Call) (o : Tbl) : Prop :=
  match kind c with
  | .ctas _ q => readsQ q o
  | .getRel O => O o
  | .probeRel O => O o
  | .listRels => o = .raw
  | .runQ q => readsQ q o
  | .countQ q => readsQ q o
  | .inert => False

noncomputable def Asem : AdapterSem Tbl Rel Method Args := ⟨Astep, Aret, Atarget, Areads⟩

theorem call_eq_of_equiv {c c' : Call} (h : c ≈ c') : c = c' := by
  obtain ⟨hm, ha⟩ := h
  rcases c with ⟨m, a⟩
  rcases c' with ⟨m', a'⟩
  simp only at hm ha
  subst hm
  have ha' : a = a' := ha
  subst ha'; rfl

theorem asem_levelSoundT : LevelSoundT Asem.level where
  preserve := by
    intro c S o h
    change Astep S c o = S o
    have h' : Atarget c ≠ some o := h
    cases hk : kind c with
    | ctas t q =>
      have ht : Atarget c = some t := by simp [Atarget, hk]
      rw [ht] at h'
      have hne : o ≠ t := fun heq => h' (by rw [heq])
      simp [Astep, hk, upd, hne]
    | _ => simp [Astep, hk]
  target_pres := fun c c' h => by rw [call_eq_of_equiv h]
  reads_sound := by
    intro c S S' hag t ht
    change Atarget c = some t at ht
    cases hk : kind c with
    | ctas t₀ q =>
      have ht0 : Atarget c = some t₀ := by simp [Atarget, hk]
      rw [ht0] at ht
      have htt : t₀ = t := Option.some.inj ht
      subst htt
      change OptEquiv (Astep S c t₀) (Astep S' c t₀)
      simp only [Astep, hk, upd, ite_true]
      exact ret_agree q (fun o ho => hag o (by change Areads c o; simp [Areads, hk]; exact ho))
    | _ => simp [Atarget, hk] at ht
  ans_sound := by
    intro c S S' hag
    change OptEquiv (some (Aret S c)) (some (Aret S' c))
    cases hk : kind c with
    | ctas t q => simp [Aret, hk]; exact List.Perm.refl _
    | getRel O =>
      simp only [Aret, hk]
      exact ret_agree (.existsIn O) (fun o ho => hag o (by change Areads c o; simp [Areads, hk]; exact ho))
    | probeRel O =>
      simp only [Aret, hk]
      exact ret_agree (.probeIn O) (fun o ho => hag o (by change Areads c o; simp [Areads, hk]; exact ho))
    | listRels =>
      simp only [Aret, hk]
      exact ret_agree .listRaw (fun o ho => hag o (by change Areads c o; simp [Areads, hk]; exact ho))
    | runQ q =>
      simp only [Aret, hk]
      exact ret_agree q (fun o ho => hag o (by change Areads c o; simp [Areads, hk]; exact ho))
    | countQ q =>
      simp only [Aret, hk]
      exact ret_agree q (fun o ho => hag o (by change Areads c o; simp [Areads, hk]; exact ho))
    | inert => simp [Aret, hk]; exact List.Perm.refl _
  step_congr := fun c c' h S t _ => by rw [call_eq_of_equiv h]; exact OptEquiv.refl _
  ans_congr := fun c c' h S => by rw [call_eq_of_equiv h]; exact OptEquiv.refl _

/-! ## Hypotheses at the adapter boundary -/

theorem atarget_read₁ (q : Query) (c : Call) (h : c ∈ alpha₁ (.read q)) : Atarget c = none := by
  cases q <;> (rcases List.mem_singleton.mp h with rfl; rfl)

theorem atarget_read₂ (q : Query) (c : Call) (h : c ∈ alpha₂ (.read q)) : Atarget c = none := by
  cases q with
  | existsIn O =>
    change c ∈ [(⟨.getRel, .set O⟩ : Call)] at h
    rcases List.mem_singleton.mp h with rfl; rfl
  | sel t => exact atarget_read₁ (.sel t) c h
  | selDesc t => exact atarget_read₁ (.selDesc t) c h
  | cnt t => exact atarget_read₁ (.cnt t) c h
  | listRaw => exact atarget_read₁ .listRaw c h
  | probeIn O => exact atarget_read₁ (.probeIn O) c h
  | rowCount t =>
    change c ∈ [(⟨.countRel, .q (.rowCount t)⟩ : Call)] at h
    rcases List.mem_singleton.mp h with rfl; rfl
  | build => exact atarget_read₁ .build c h
  | addSchema k => exact atarget_read₁ (.addSchema k) c h
  | addView k => exact atarget_read₁ (.addView k) c h
  | dimCount => exact atarget_read₁ .dimCount c h

theorem mem_buildCalls₁ {c : Call} (h : c ∈ buildCalls₁) :
    c = ⟨.ctas, .tq .dim (.addSchema 1)⟩ ∨ c = ⟨.ctas, .tq .dim (.addView 1)⟩ ∨
    c = ⟨.ctas, .tq .dim (.addSchema 2)⟩ ∨ c = ⟨.ctas, .tq .dim (.addView 2)⟩ ∨ c = verifyCall := by
  simp only [buildCalls₁, bundleCalls, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at h
  exact h

theorem mem_buildCalls₂ {c : Call} (h : c ∈ buildCalls₂) :
    c = ⟨.ctas, .tq .dim (.addSchema 2)⟩ ∨ c = ⟨.ctas, .tq .dim (.addView 2)⟩ ∨
    c = ⟨.ctas, .tq .dim (.addSchema 1)⟩ ∨ c = ⟨.ctas, .tq .dim (.addView 1)⟩ ∨ c = verifyCall := by
  simp only [buildCalls₂, bundleCalls, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at h
  exact h

theorem alpha₁_write (t : Tbl) (q : Query) (h : isBld t q = false) :
    alpha₁ (.write t q) = [⟨.ctas, .tq t q⟩] := by
  cases t <;> cases q <;> first | rfl | exact absurd h (by simp [isBld])

theorem alpha₂_write (t : Tbl) (q : Query) (h : isBld t q = false) :
    alpha₂ (.write t q) = [⟨.ctas, .tq t q⟩] := by
  cases t <;> cases q <;> first | rfl | exact absurd h (by simp [isBld])

theorem targetFaithfulL₁ : TargetFaithfulL (alphaComp (Query := Query) Asem E₁) := by
  intro s c hc hne
  cases s with
  | write t q =>
    by_cases hb : isBld t q = false
    · change c ∈ alpha₁ (.write t q) at hc
      rw [alpha₁_write t q hb] at hc
      rcases List.mem_singleton.mp hc with rfl; rfl
    · cases t <;> cases q <;> simp [isBld] at hb
      change c ∈ buildCalls₁ at hc
      rcases mem_buildCalls₁ hc with rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact absurd rfl hne
  | read q =>
    exact absurd (atarget_read₁ q c hc) hne

theorem targetFaithfulL₂ : TargetFaithfulL (alphaComp (Query := Query) Asem E₂) := by
  intro s c hc hne
  cases s with
  | write t q =>
    by_cases hb : isBld t q = false
    · change c ∈ alpha₂ (.write t q) at hc
      rw [alpha₂_write t q hb] at hc
      rcases List.mem_singleton.mp hc with rfl; rfl
    · cases t <;> cases q <;> simp [isBld] at hb
      change c ∈ buildCalls₂ at hc
      rcases mem_buildCalls₂ hc with rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact absurd rfl hne
  | read q =>
    exact absurd (atarget_read₂ q c hc) hne

theorem compiledReadsSoundL₁ : CompiledReadsSoundL reads (alphaComp (Query := Query) Asem E₁) := by
  intro s c hc o ho
  cases s with
  | write t q =>
    by_cases hb : isBld t q = false
    · change c ∈ alpha₁ (.write t q) at hc
      rw [alpha₁_write t q hb] at hc
      rcases List.mem_singleton.mp hc with rfl; exact ho
    · cases t <;> cases q <;> simp [isBld] at hb
      change c ∈ buildCalls₁ at hc
      rcases mem_buildCalls₁ hc with rfl | rfl | rfl | rfl | rfl <;> exact ho
  | read q =>
    change c ∈ alpha₁ (.read q) at hc
    cases q <;> (rcases List.mem_singleton.mp hc with rfl; exact ho)

theorem compiledReadsSoundL₂ : CompiledReadsSoundL reads (alphaComp (Query := Query) Asem E₂) := by
  intro s c hc o ho
  cases s with
  | write t q =>
    by_cases hb : isBld t q = false
    · change c ∈ alpha₂ (.write t q) at hc
      rw [alpha₂_write t q hb] at hc
      rcases List.mem_singleton.mp hc with rfl; exact ho
    · cases t <;> cases q <;> simp [isBld] at hb
      change c ∈ buildCalls₂ at hc
      rcases mem_buildCalls₂ hc with rfl | rfl | rfl | rfl | rfl <;> exact ho
  | read q =>
    cases q with
    | existsIn O =>
      change c ∈ [(⟨.getRel, .set O⟩ : Call)] at hc
      rcases List.mem_singleton.mp hc with rfl; exact ho
    | sel t => exact compiledReadsSoundL₁ (.read (.sel t)) c hc o ho
    | selDesc t => exact compiledReadsSoundL₁ (.read (.selDesc t)) c hc o ho
    | cnt t => exact compiledReadsSoundL₁ (.read (.cnt t)) c hc o ho
    | listRaw => exact compiledReadsSoundL₁ (.read .listRaw) c hc o ho
    | probeIn O => exact compiledReadsSoundL₁ (.read (.probeIn O)) c hc o ho
    | rowCount t =>
      change c ∈ [(⟨.countRel, .q (.rowCount t)⟩ : Call)] at hc
      rcases List.mem_singleton.mp hc with rfl; exact ho
    | build => exact compiledReadsSoundL₁ (.read .build) c hc o ho
    | addSchema k => exact compiledReadsSoundL₁ (.read (.addSchema k)) c hc o ho
    | addView k => exact compiledReadsSoundL₁ (.read (.addView k)) c hc o ho
    | dimCount => exact compiledReadsSoundL₁ (.read .dimCount) c hc o ho

def adapterView : Call → CallView Method Args := fun c => ⟨c.method, c.args⟩

def driverView : DriverCall Tbl Query → CallView Method Args
  | .write t q => ⟨.ctas, .tq t (normQ q)⟩
  | .read q => ⟨.runQuery, .q (normQ q)⟩

theorem adapterViewFaithful : AdapterViewFaithful adapterView := fun _ _ h => h

theorem driverViewFaithful : DriverViewFaithful driverView := by
  intro c c' h
  obtain ⟨hm, ha⟩ := h
  have ha' : (driverView c).args = (driverView c').args := ha
  cases c with
  | write t q =>
    cases c' with
    | write t' q' =>
      simp [driverView] at ha'
      show key _ = key _
      simp [key, ha']
    | read q' => simp [driverView] at hm
  | read q =>
    cases c' with
    | write t' q' => simp [driverView] at hm
    | read q' =>
      simp [driverView] at ha'
      show key _ = key _
      simp [key, ha']

/-! ## The cross-node stand-ins, at both boundaries

Two stand-in pairs, with *different result schemas*: `list_relations` (a list of table codes) stands in
for `get_relation O` (the codes among `O`) through `slice O`, and `select *` (the rows of a table) stands in
for `row_count` (a one-row, one-column relation) through `countOf`. `Allowed` is the set of triples the
replay may use; it is one family (indexed by the target set `O`) and one single pair. -/

noncomputable def slice (O : Tbl → Prop) (r : Rel) : Rel := r.filter (keep O)

/-- The row-count converter: a relation of rows becomes the one-row relation holding its length. -/
def countOf (r : Rel) : Rel := [r.length]

/-- Driver boundary: the allowed triples `(wide call, narrow call, converter)`. -/
def AllowedD (cw cn : Stmt) (h : Rel → Rel) : Prop :=
  (∃ O, cw = .read .listRaw ∧ cn = .read (.existsIn O) ∧ h = slice O) ∨
  (cw = .read (.sel .raw) ∧ cn = .read (.rowCount .raw) ∧ h = countOf)

/-- Adapter boundary: the same two stand-ins, over adapter calls. -/
def AllowedA (cw cn : Call) (h : Rel → Rel) : Prop :=
  (∃ O, cw = ⟨.listRels, .none⟩ ∧ cn = ⟨.getRel, .set O⟩ ∧ h = slice O) ∨
  (cw = ⟨.runQuery, .q (.sel .raw)⟩ ∧ cn = ⟨.countRel, .q (.rowCount .raw)⟩ ∧ h = countOf)

theorem countOf_congr {x y : Rel} (h : x ≈ y) : countOf x ≈ countOf y := by
  show [x.length] ≈ [y.length]
  rw [(show List.Perm x y from h).length_eq]; exact List.Perm.refl _

theorem standIn_driver : StandInSet (driverLevel ret reads) AllowedD := by
  rintro cw cn h (⟨O, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
  · exact ⟨fun _ => OptEquiv.refl _, fun _ _ h => List.Perm.filter _ h⟩
  · exact ⟨fun _ => OptEquiv.refl _, fun _ _ h => countOf_congr h⟩

theorem standIn_adapter : StandInSet Asem.level AllowedA := by
  rintro cw cn h (⟨O, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
  · exact ⟨fun _ => OptEquiv.refl _, fun _ _ h => List.Perm.filter _ h⟩
  · exact ⟨fun _ => OptEquiv.refl _, fun _ _ h => countOf_congr h⟩

/-! ## The project's structural hypotheses -/

theorem nxtF_write {n : Node} {k : Nat} {o : Tbl} {q : Query}
    (h : nxtF n k = some (.write o q)) :
    (n = .staging ∧ o = .stg) ∨ (n = .marts ∧ o = .mart) ∨ (n = .dims ∧ o = .dim) := by
  cases n <;> rcases k with _ | _ | _ | k <;>
    simp [nxtF, sCheck, sStg, sList, sSel, sSelD, sMart, sCount, sBuild] at h <;>
    first
      | (left; exact ⟨rfl, h.1.symm⟩)
      | (right; left; exact ⟨rfl, h.1.symm⟩)
      | (right; right; exact ⟨rfl, h.1.symm⟩)

theorem uniqueWriter : UniqueWriterGlobal P := by
  intro o n₁ n₂ H₁ H₂ q₁ q₂ h₁ h₂
  have a := nxtF_write h₁
  have b := nxtF_write h₂
  rcases a with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases b with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;>
    first | rfl | (exact absurd hb (by decide))

theorem nti : NextTildeInsensitive P := by
  intro n H H' h
  have : H.length = H'.length := LForall₂.length_eq h
  show nxtF n H.length = nxtF n H'.length
  rw [this]

def rank : Tbl → Nat
  | .raw => 0 | .stg => 1 | .mart => 2 | .dim => 0

theorem rank_lt_stg : rank .raw < rank .stg := by decide
theorem rank_lt_mart : rank .stg < rank .mart := by decide

theorem staticAcyclic : WellFounded (StaticPrec reads P) := by
  refine Subrelation.wf (r := InvImage (· < ·) rank) ?_ (InvImage.wf rank Nat.lt_wfRel.wf)
  intro o₁ o₂ h
  obtain ⟨hne, n, ⟨H, stmt, hs, hr⟩, ⟨H', q, hw⟩⟩ := h
  have hn := nxtF_write (n := n) (k := H'.length) hw
  change nxtF n H.length = some stmt at hs
  change nxtF n H'.length = some (.write o₂ q) at hw
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hk : H.length with _ | _ | k <;> rw [hk] at hs <;> simp [nxtF] at hs <;> subst hs <;>
      simp [reads, readsQ, sCheck, sStg, Oraw] at hr <;> subst hr <;> exact rank_lt_stg
  · rcases hk : H.length with _ | k <;> rw [hk] at hs <;> simp [nxtF] at hs <;> subst hs <;>
      simp [reads, readsQ, sMart] at hr <;> subst hr <;> exact rank_lt_mart
  · rcases hk : H.length with _ | k <;> rw [hk] at hs <;> simp [nxtF] at hs <;> subst hs <;>
      simp [reads, readsQ, sBuild] at hr <;> exact absurd hr hne

/-! ## Evaluation lemmas -/

theorem rE_read₁ (S : St) (q : Query) : rE ret E₁ S (.read q) = some (.rel (ret S q)) := by
  simp only [rE, drv₁_read]
  show some (Result.rel (ret S (probeQ q))) = _
  rw [ret_probeQ]

theorem rE_read₂ (S : St) (q : Query) : rE ret E₂ S (.read q) = some (.rel (ret S q)) := by
  simp only [rE, drv₂_read]; rfl

theorem execE_read₁ (S : St) (q : Query) : execE ret E₁ S (.read q) = S := by
  simp only [execE, drv₁_read]; rfl

theorem execE_read₂ (S : St) (q : Query) : execE ret E₂ S (.read q) = S := by
  simp only [execE, drv₂_read]; rfl

theorem execE_write₁ (S : St) (t : Tbl) (q : Query) (h : isBld t q = false) :
    execE ret E₁ S (.write t q) = upd S t (ret S q) := by
  simp only [execE, drv₁_write t q h]; rfl

theorem execE_write₂ (S : St) (t : Tbl) (q : Query) (h : isBld t q = false) :
    execE ret E₂ S (.write t q) = upd S t (ret S (rend q)) := by
  simp only [execE, drv₂_write t q h]; rfl

def S₀ : St := fun t => match t with | .raw => some [1, 2, 3] | _ => none

open Classical in
theorem ret_check : ret S₀ (.existsIn Oraw) = [0] := by
  show (existingRaw S₀).filter (keep Oraw) = [0]
  have h0 : existingRaw S₀ = [0] := rfl
  rw [h0]
  have hk : keep Oraw 0 = true := by
    rw [keep_zero]; exact decide_eq_true rfl
  simp [List.filter, hk]

theorem ret_list : ret S₀ .listRaw = [0] := rfl

theorem ret_selRaw : ret S₀ (.sel .raw) = [1, 2, 3] := rfl
theorem ret_selDescRaw : ret S₀ (.selDesc .raw) = [3, 2, 1] := rfl

/-! ## The two runs (different engines, different schedules) -/

def node₁ : Nat → Node
  | 1 => .staging | 2 => .audit | 3 => .audit | 4 => .audit | 5 => .staging | 6 => .marts
  | 7 => .report | _ => .dims
def stmt₁ : Nat → Stmt
  | 1 => sCheck | 2 => sList | 3 => sSel | 4 => sSelD | 5 => sStg | 6 => sMart | 7 => sCount
  | _ => sBuild
def res₁ : Nat → Result Rel
  | 1 => .rel [0] | 2 => .rel [0] | 3 => .rel [1, 2, 3] | 4 => .rel [3, 2, 1] | 5 => .ok
  | 6 => .ok | 7 => .rel [3] | _ => .ok
def node₂ : Nat → Node
  | 1 => .report | 2 => .audit | 3 => .audit | 4 => .staging | 5 => .audit | 6 => .staging
  | 7 => .marts | _ => .dims
def stmt₂ : Nat → Stmt
  | 1 => sCount | 2 => sList | 3 => sSel | 4 => sCheck | 5 => sSelD | 6 => sStg | 7 => sMart
  | _ => sBuild
def res₂ : Nat → Result Rel
  | 1 => .rel [3] | 2 => .rel [0] | 3 => .rel [1, 2, 3] | 4 => .rel [0] | 5 => .rel [3, 2, 1]
  | _ => .ok

theorem stateAt_succ' (E : Engine Tbl Query Method Args) (stmt : Nat → Stmt) (m : Nat)
    (hm : 1 ≤ m) :
    stateAt stmt ret E S₀ (m + 1) = execE ret E (stateAt stmt ret E S₀ m) (stmt m) :=
  Formalization.Module1.Gen.stateAt_succ (L := driverLevel ret reads) (comp := drvE E) stmt S₀ m hm

theorem stateAt_one (E : Engine Tbl Query Method Args) (stmt : Nat → Stmt) :
    stateAt stmt ret E S₀ 1 = S₀ := rfl

def Sstg₁ : St := upd S₀ .stg [1, 2, 3]
def Sfin₁ : St := upd Sstg₁ .mart [3]
def Sstg₂ : St := upd S₀ .stg [3, 2, 1]
def Sfin₂ : St := upd Sstg₂ .mart [3]
/-- After the `dims` turn: engine 1 built the bundles in the order 1, 2, engine 2 in the order 2, 1. -/
def Sdim₁ : St := upd Sfin₁ .dim [10, 11, 20, 21]
def Sdim₂ : St := upd Sfin₂ .dim [20, 21, 10, 11]

theorem execE_build₁ (S : St) :
    execE ret E₁ S sBuild = upd S .dim (rows S .dim ++ [10, 11, 20, 21]) := by
  funext o
  by_cases ho : o = .dim
  · subst ho
    simp [execE, sBuild, drv₁_build, buildDrv₁, List.foldl, execS, upd, ret, rows]
  · simp [execE, sBuild, drv₁_build, buildDrv₁, List.foldl, execS, upd, ho]

theorem execE_build₂ (S : St) :
    execE ret E₂ S sBuild = upd S .dim (rows S .dim ++ [20, 21, 10, 11]) := by
  funext o
  by_cases ho : o = .dim
  · subst ho
    simp [execE, sBuild, drv₂_build, buildDrv₂, List.foldl, execS, upd, ret, rows]
  · simp [execE, sBuild, drv₂_build, buildDrv₂, List.foldl, execS, upd, ho]

/-- In the first run, positions 1–4 are reads. -/
theorem st₁_read (k : Nat) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
    stateAt stmt₁ ret E₁ S₀ (k + 1) = S₀ := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [stateAt_succ' E₁ stmt₁ 1 (by decide), stateAt_one]; exact execE_read₁ S₀ _
    · rw [stateAt_succ' E₁ stmt₁ (m + 1) (by omega), ih hm (by omega)]
      have : ∃ q, stmt₁ (m + 1) = .read q := by
        rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      obtain ⟨q, hq⟩ := this
      rw [hq]; exact execE_read₁ S₀ q

theorem st₁_5 : stateAt stmt₁ ret E₁ S₀ 5 = S₀ := st₁_read 4 (by decide) (by decide)
theorem st₁_6 : stateAt stmt₁ ret E₁ S₀ 6 = Sstg₁ := by
  rw [stateAt_succ' E₁ stmt₁ 5 (by decide), st₁_5]
  exact execE_write₁ S₀ .stg (.sel .raw) rfl
theorem st₁_7 : stateAt stmt₁ ret E₁ S₀ 7 = Sfin₁ := by
  rw [stateAt_succ' E₁ stmt₁ 6 (by decide), st₁_6]
  exact execE_write₁ Sstg₁ .mart (.cnt .stg) rfl
theorem st₁_8 : stateAt stmt₁ ret E₁ S₀ 8 = Sfin₁ := by
  rw [stateAt_succ' E₁ stmt₁ 7 (by decide), st₁_7]
  exact execE_read₁ Sfin₁ (.rowCount .raw)

/-- In the second run, positions 1–5 are reads. -/
theorem st₂_read (k : Nat) (hk : 1 ≤ k) (hk5 : k ≤ 5) :
    stateAt stmt₂ ret E₂ S₀ (k + 1) = S₀ := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [stateAt_succ' E₂ stmt₂ 1 (by decide), stateAt_one]; exact execE_read₂ S₀ _
    · rw [stateAt_succ' E₂ stmt₂ (m + 1) (by omega), ih hm (by omega)]
      have : ∃ q, stmt₂ (m + 1) = .read q := by
        rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl <;>
          exact ⟨_, rfl⟩
      obtain ⟨q, hq⟩ := this
      rw [hq]; exact execE_read₂ S₀ q

theorem st₂_6 : stateAt stmt₂ ret E₂ S₀ 6 = S₀ := st₂_read 5 (by decide) (by decide)
theorem st₂_7 : stateAt stmt₂ ret E₂ S₀ 7 = Sstg₂ := by
  rw [stateAt_succ' E₂ stmt₂ 6 (by decide), st₂_6]
  exact execE_write₂ S₀ .stg (.sel .raw) rfl
theorem st₂_8 : stateAt stmt₂ ret E₂ S₀ 8 = Sfin₂ := by
  rw [stateAt_succ' E₂ stmt₂ 7 (by decide), st₂_7]
  exact execE_write₂ Sstg₂ .mart (.cnt .stg) rfl

theorem st₁_9 : stateAt stmt₁ ret E₁ S₀ 9 = Sdim₁ := by
  rw [stateAt_succ' E₁ stmt₁ 8 (by decide), st₁_8]
  exact execE_build₁ Sfin₁
theorem st₂_9 : stateAt stmt₂ ret E₂ S₀ 9 = Sdim₂ := by
  rw [stateAt_succ' E₂ stmt₂ 8 (by decide), st₂_8]
  exact execE_build₂ Sfin₂

theorem eight (i : Nat) (h1 : 1 ≤ i) (h2 : i ≤ 8) :
    i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega

theorem ret_countRaw : ret S₀ (.rowCount .raw) = [3] := rfl

def run₁ : LiveRun P E₁ ret S₀ where
  N := 8
  node := node₁
  stmt := stmt₁
  res := res₁
  stmt_eq := by
    intro i h1 h2
    show nxtF (node₁ i) (histAt node₁ stmt₁ res₁ (node₁ i) i).length = some (stmt₁ i)
    rw [turnCount_eq_length node₁ stmt₁ res₁]
    rcases eight i h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  res_eq := by
    intro i h1 h2
    rcases eight i h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show rE ret E₁ S₀ (.read (.existsIn Oraw)) = some (.rel [0])
      rw [rE_read₁, ret_check]
    · show rE ret E₁ (stateAt stmt₁ ret E₁ S₀ 2) (.read .listRaw) = some (.rel [0])
      rw [st₁_read 1 (by decide) (by decide), rE_read₁, ret_list]
    · show rE ret E₁ (stateAt stmt₁ ret E₁ S₀ 3) (.read (.sel .raw)) = some (.rel [1, 2, 3])
      rw [st₁_read 2 (by decide) (by decide), rE_read₁, ret_selRaw]
    · show rE ret E₁ (stateAt stmt₁ ret E₁ S₀ 4) (.read (.selDesc .raw)) = some (.rel [3, 2, 1])
      rw [st₁_read 3 (by decide) (by decide), rE_read₁, ret_selDescRaw]
    · rfl
    · rfl
    · show rE ret E₁ (stateAt stmt₁ ret E₁ S₀ 7) (.read (.rowCount .raw)) = some (.rel [3])
      rw [st₁_7, rE_read₁]; rfl
    · rfl
  valid2 := by
    intro n
    show nxtF n (histAt node₁ stmt₁ res₁ n (8 + 1)).length = none
    rw [turnCount_eq_length node₁ stmt₁ res₁]
    cases n <;> rfl

def run₂ : LiveRun P E₂ ret S₀ where
  N := 8
  node := node₂
  stmt := stmt₂
  res := res₂
  stmt_eq := by
    intro i h1 h2
    show nxtF (node₂ i) (histAt node₂ stmt₂ res₂ (node₂ i) i).length = some (stmt₂ i)
    rw [turnCount_eq_length node₂ stmt₂ res₂]
    rcases eight i h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  res_eq := by
    intro i h1 h2
    rcases eight i h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show rE ret E₂ S₀ (.read (.rowCount .raw)) = some (.rel [3])
      rw [rE_read₂, ret_countRaw]
    · show rE ret E₂ (stateAt stmt₂ ret E₂ S₀ 2) (.read .listRaw) = some (.rel [0])
      rw [st₂_read 1 (by decide) (by decide), rE_read₂, ret_list]
    · show rE ret E₂ (stateAt stmt₂ ret E₂ S₀ 3) (.read (.sel .raw)) = some (.rel [1, 2, 3])
      rw [st₂_read 2 (by decide) (by decide), rE_read₂, ret_selRaw]
    · show rE ret E₂ (stateAt stmt₂ ret E₂ S₀ 4) (.read (.existsIn Oraw)) = some (.rel [0])
      rw [st₂_read 3 (by decide) (by decide), rE_read₂, ret_check]
    · show rE ret E₂ (stateAt stmt₂ ret E₂ S₀ 5) (.read (.selDesc .raw)) = some (.rel [3, 2, 1])
      rw [st₂_read 4 (by decide) (by decide), rE_read₂, ret_selDescRaw]
    · rfl
    · rfl
    · rfl
  valid2 := by
    intro n
    show nxtF n (histAt node₂ stmt₂ res₂ n (8 + 1)).length = none
    rw [turnCount_eq_length node₂ stmt₂ res₂]
    cases n <;> rfl

theorem dag₁ : DAGOrder reads run₁ := by
  intro j' h1 h2 o hr j hj1 hj2 hn ht
  have h8 : j' ≤ 8 := h2
  have hj8 : j ≤ 8 := hj2
  rcases eight j' h1 h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases eight j hj1 hj8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [run₁, node₁, stmt₁, reads, readsQ, sCheck, sList, sSel, sSelD, sStg, sMart, sCount,
      sBuild, Oraw, target] at hr hn ht ⊢ <;>
    first | omega | (subst hr; cases ht) | simp_all

theorem dag₂ : DAGOrder reads run₂ := by
  intro j' h1 h2 o hr j hj1 hj2 hn ht
  have h8 : j' ≤ 8 := h2
  have hj8 : j ≤ 8 := hj2
  rcases eight j' h1 h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases eight j hj1 hj8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [run₂, node₂, stmt₂, reads, readsQ, sCheck, sList, sSel, sSelD, sStg, sMart, sCount,
      sBuild, Oraw, target] at hr hn ht ⊢ <;>
    first | omega | (subst hr; cases ht) | simp_all

/-! ## Linking the adapter level to the driver level along each run -/

theorem stateEquiv_refl (S : St) : StateEquiv S S := fun _ => OptEquiv.refl _

theorem ret_rend (S : St) (q : Query) : ret S q ≈ ret S (rend q) := by
  cases q with
  | sel t => exact (List.reverse_perm _).symm
  | _ => exact List.Perm.refl _

theorem execL_read₁ (S : St) (q : Query) :
    execL (alphaComp (Query := Query) Asem E₁) S (.read q) = S := by
  cases q <;> rfl
theorem execL_read₂ (S : St) (q : Query) :
    execL (alphaComp (Query := Query) Asem E₂) S (.read q) = S := by
  cases q <;> rfl
theorem execL_write₁ (S : St) (t : Tbl) (q : Query) (h : isBld t q = false) :
    execL (alphaComp (Query := Query) Asem E₁) S (.write t q) = upd S t (ret S q) := by
  show List.foldl Astep S (alpha₁ (.write t q)) = _
  rw [alpha₁_write t q h]; rfl
theorem execL_write₂ (S : St) (t : Tbl) (q : Query) (h : isBld t q = false) :
    execL (alphaComp (Query := Query) Asem E₂) S (.write t q) = upd S t (ret S q) := by
  show List.foldl Astep S (alpha₂ (.write t q)) = _
  rw [alpha₂_write t q h]; rfl

theorem rL_read₁ (S : St) (q : Query) :
    rL (alphaComp (Query := Query) Asem E₁) S (.read q) = some (.rel (ret S q)) := by
  cases q <;> rfl
theorem rL_read₂ (S : St) (q : Query) :
    rL (alphaComp (Query := Query) Asem E₂) S (.read q) = some (.rel (ret S q)) := by
  cases q <;> rfl

theorem upd_equiv {S S' : St} (h : StateEquiv S S') (t : Tbl) {a b : Rel} (hab : a ≈ b) :
    StateEquiv (upd S t a) (upd S' t b) := by
  intro o
  unfold upd
  by_cases ho : o = t
  · simp [ho]; exact hab
  · simp [ho]; exact h o

theorem execL_build₁ (S : St) :
    execL (alphaComp (Query := Query) Asem E₁) S sBuild = upd S .dim (rows S .dim ++ [10, 11, 20, 21]) := by
  show List.foldl Astep S buildCalls₁ = _
  funext o
  by_cases ho : o = .dim
  · subst ho
    simp [buildCalls₁, bundleCalls, verifyCall, List.foldl, Astep, kind, upd, ret, rows]
  · simp [buildCalls₁, bundleCalls, verifyCall, List.foldl, Astep, kind, upd, ho]

theorem execL_build₂ (S : St) :
    execL (alphaComp (Query := Query) Asem E₂) S sBuild = upd S .dim (rows S .dim ++ [20, 21, 10, 11]) := by
  show List.foldl Astep S buildCalls₂ = _
  funext o
  by_cases ho : o = .dim
  · subst ho
    simp [buildCalls₂, bundleCalls, verifyCall, List.foldl, Astep, kind, upd, ret, rows]
  · simp [buildCalls₂, bundleCalls, verifyCall, List.foldl, Astep, kind, upd, ho]

theorem exec_coh₁ {S S' : St} (h : StateEquiv S S') (stmt : Stmt) :
    StateEquiv (execL (alphaComp (Query := Query) Asem E₁) S stmt) (execE ret E₁ S' stmt) := by
  cases stmt with
  | write t q =>
    by_cases hb : isBld t q = false
    · rw [execL_write₁ _ _ _ hb, execE_write₁ _ _ _ hb]
      exact upd_equiv h t (ret_stateEquiv q h)
    · cases t <;> cases q <;> simp [isBld] at hb
      show StateEquiv (execL (alphaComp (Query := Query) Asem E₁) S sBuild) (execE ret E₁ S' sBuild)
      rw [execL_build₁, execE_build₁]
      exact upd_equiv h .dim (List.Perm.append_right _ (rows_perm (h .dim)))
  | read q => rw [execL_read₁, execE_read₁]; exact h

theorem exec_coh₂ {S S' : St} (h : StateEquiv S S') (stmt : Stmt) :
    StateEquiv (execL (alphaComp (Query := Query) Asem E₂) S stmt) (execE ret E₂ S' stmt) := by
  cases stmt with
  | write t q =>
    by_cases hb : isBld t q = false
    · rw [execL_write₂ _ _ _ hb, execE_write₂ _ _ _ hb]
      exact upd_equiv h t ((ret_stateEquiv q h).trans (ret_rend S' q))
    · cases t <;> cases q <;> simp [isBld] at hb
      show StateEquiv (execL (alphaComp (Query := Query) Asem E₂) S sBuild) (execE ret E₂ S' sBuild)
      rw [execL_build₂, execE_build₂]
      exact upd_equiv h .dim (List.Perm.append_right _ (rows_perm (h .dim)))
  | read q => rw [execL_read₂, execE_read₂]; exact h

theorem rL_coh₁ {S S' : St} (h : StateEquiv S S') (stmt : Stmt) (r' : Result Rel)
    (hr : rE ret E₁ S' stmt = some r') :
    ∃ r, rL (alphaComp (Query := Query) Asem E₁) S stmt = some r ∧ ResEquiv r r' := by
  cases stmt with
  | write t q =>
    have : r' = .ok := (Option.some.inj hr).symm
    subst this; exact ⟨.ok, rfl, trivial⟩
  | read q =>
    rw [rE_read₁] at hr
    have hr' := Option.some.inj hr
    subst hr'
    exact ⟨.rel (ret S q), rL_read₁ S q, ret_stateEquiv q h⟩

theorem rL_coh₂ {S S' : St} (h : StateEquiv S S') (stmt : Stmt) (r' : Result Rel)
    (hr : rE ret E₂ S' stmt = some r') :
    ∃ r, rL (alphaComp (Query := Query) Asem E₂) S stmt = some r ∧ ResEquiv r r' := by
  cases stmt with
  | write t q =>
    have : r' = .ok := (Option.some.inj hr).symm
    subst this; exact ⟨.ok, rfl, trivial⟩
  | read q =>
    rw [rE_read₂] at hr
    have hr' := Option.some.inj hr
    subst hr'
    exact ⟨.rel (ret S q), rL_read₂ S q, ret_stateEquiv q h⟩

theorem runLink₁ : RunLinkT Asem run₁ := by
  have sl : ∀ i, StateEquiv (stateAtL (alphaComp (Query := Query) Asem E₁) run₁.stmt S₀ i)
      (stateAt run₁.stmt ret E₁ S₀ i) := by
    intro i
    induction i with
    | zero => exact stateEquiv_refl _
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact stateEquiv_refl _
      · rw [Formalization.Module1.Gen.stateAt_succ (L := Asem.level)
          (comp := alphaComp (Query := Query) Asem E₁) run₁.stmt S₀ m hm,
          stateAt_succ' E₁ run₁.stmt m hm]
        exact exec_coh₁ ih (run₁.stmt m)
  exact ⟨sl, fun i h1 h2 => rL_coh₁ (sl i) (run₁.stmt i) (run₁.res i) (run₁.res_eq i h1 h2)⟩

theorem runLink₂ : RunLinkT Asem run₂ := by
  have sl : ∀ i, StateEquiv (stateAtL (alphaComp (Query := Query) Asem E₂) run₂.stmt S₀ i)
      (stateAt run₂.stmt ret E₂ S₀ i) := by
    intro i
    induction i with
    | zero => exact stateEquiv_refl _
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact stateEquiv_refl _
      · rw [Formalization.Module1.Gen.stateAt_succ (L := Asem.level)
          (comp := alphaComp (Query := Query) Asem E₂) run₂.stmt S₀ m hm,
          stateAt_succ' E₂ run₂.stmt m hm]
        exact exec_coh₂ ih (run₂.stmt m)
  exact ⟨sl, fun i h1 h2 => rL_coh₂ (sl i) (run₂.stmt i) (run₂.res i) (run₂.res_eq i h1 h2)⟩


/-! ## The method classification

Which methods are reads (reorderable within a segment, never consumed) and which are writes (barriers):
only `ctas` mutates. -/

def cls : Method → Cls
  | .ctas => .write
  | _ => .read

/-- **The classification is truthful** at the driver boundary: a call the map classifies as a read
(every driver `Read`, whose view's method is `runQuery`) has no target. -/
theorem clsTruthful_driver : ClsTruthful (driverLevel ret reads) cls driverView := by
  intro c hc
  cases c with
  | write t q => simp [driverView, cls] at hc
  | read q => rfl

/-- … and at the adapter boundary: every call whose method is not `ctas` has no target. -/
theorem clsTruthful_adapter : ClsTruthful Asem.level cls adapterView := by
  intro c hc
  rcases c with ⟨m, a⟩
  cases m <;> simp [adapterView, cls] at hc <;> cases a <;> rfl

/-- **The two engines issue as many write calls for every statement** (at the driver boundary). -/
theorem sbc_driver : SameBarrierCount cls (callsB E₂ adapterView driverView Boundary.adapterDriver)
    (callsB E₁ adapterView driverView Boundary.adapterDriver) run₁.N run₁.stmt := by
  intro j _ _
  show nw cls ((drvE E₂ (run₁.stmt j)).map driverView) = nw cls ((drvE E₁ (run₁.stmt j)).map driverView)
  cases run₁.stmt j with
  | write t q =>
    by_cases hb : isBld t q = false
    · rw [drv₁_write t q hb, drv₂_write t q hb]; rfl
    · cases t <;> cases q <;> simp [isBld] at hb
      rw [drv₁_build, drv₂_build]; rfl
  | read q => rw [drv₁_read, drv₂_read]; rfl

/-- … and at the adapter boundary. -/
theorem sbc_adapter : SameBarrierCount cls (callsB E₂ adapterView driverView Boundary.coreAdapter)
    (callsB E₁ adapterView driverView Boundary.coreAdapter) run₁.N run₁.stmt := by
  intro j _ _
  show nw cls ((alpha₂ (run₁.stmt j)).map adapterView) = nw cls ((alpha₁ (run₁.stmt j)).map adapterView)
  cases run₁.stmt j with
  | write t q =>
    by_cases hb : isBld t q = false
    · rw [alpha₁_write t q hb, alpha₂_write t q hb]
    · cases t <;> cases q <;> simp [isBld] at hb
      rfl
  | read q => cases q <;> rfl

/-! ## The recorded histories, and replay convergence node by node -/

abbrev Hist := History Tbl Query Rel

def Lstaging : Hist := [(sCheck, .rel [0]), (sStg, .ok)]
def Laudit : Hist := [(sList, .rel [0]), (sSel, .rel [1, 2, 3]), (sSelD, .rel [3, 2, 1])]
def Lmarts : Hist := [(sMart, .ok)]
def Lreport : Hist := [(sCount, .rel [3])]
def Ldims : Hist := [(sBuild, .ok)]

theorem rec_staging : recordingOf run₁ .staging = Lstaging := rfl
theorem rec_audit : recordingOf run₁ .audit = Laudit := rfl
theorem rec_marts : recordingOf run₁ .marts = Lmarts := rfl
theorem rec_report : recordingOf run₁ .report = Lreport := rfl
theorem rec_dims : recordingOf run₁ .dims = Ldims := rfl

theorem histEquiv_refl : ∀ H : Hist, HistEquiv H H
  | [] => LForall₂.nil
  | _ :: l => LForall₂.cons ⟨rfl, ResEquiv.refl _⟩ (histEquiv_refl l)

/-- Every recorded call is built from a turn and a call index of the recorded history. -/
theorem inRec_mk {recV : Stmt → List (CallView Method Args)} {cr : Nat → Nat → Result Rel}
    {L : Hist} {t : Nat} {s : Stmt} {r : Result Rel} {k : Nat} {v : CallView Method Args}
    (hL : L[t]? = some (s, r)) (hk : (recV s)[k]? = some v) :
    InRec cls recV cr L ⟨v, cr t k, Wt cls recV L t + nw cls ((recV s).take k)⟩ :=
  ⟨t, s, r, k, v, hL, hk, rfl⟩

/-- One served turn consisting of a single call: a write served by the barrier `e`. -/
theorem serve_write {F : RecEv Method Args Rel → Prop}
    {XS : Stmt → CallView Method Args → Result Rel → Prop} {s : Stmt} {c : Nat}
    {v : CallView Method Args} (hv : isW cls v = true) (e : RecEv Method Args Rel) (hF : F e)
    (hew : isW cls e.view = true) (hseg : e.seg = c) (hm : CVEquiv v e.view) :
    ServeTurn (MatchCallX cls CVEquiv F XS s) c [v] e.res (c + 1) :=
  ⟨[], v, c, rfl, MatchAll.nil, ⟨fun _ => ⟨e, hF, hew, hseg, hm, rfl, rfl⟩,
    fun h => by rw [hv] at h; cases h⟩⟩

/-- … a read served locally by the recorded read `e` of the segment. -/
theorem serve_read {F : RecEv Method Args Rel → Prop}
    {XS : Stmt → CallView Method Args → Result Rel → Prop} {s : Stmt} {c : Nat}
    {v : CallView Method Args} (hv : isW cls v = false) (e : RecEv Method Args Rel) (hF : F e)
    (hew : isW cls e.view = false) (hseg : e.seg = c) (hm : CVEquiv v e.view) :
    ServeTurn (MatchCallX cls CVEquiv F XS s) c [v] e.res c :=
  ⟨[], v, c, rfl, MatchAll.nil, ⟨(fun h => by rw [hv] at h; cases h),
    fun _ => Or.inl ⟨e, hF, hew, hseg, hm, rfl, rfl⟩⟩⟩

/-- … a read with no local candidate, served by rule 3. -/
theorem serve_read_x {F : RecEv Method Args Rel → Prop}
    {XS : Stmt → CallView Method Args → Result Rel → Prop} {s : Stmt} {c : Nat}
    {v : CallView Method Args} {r : Result Rel} (hv : isW cls v = false)
    (hno : ¬ ∃ e, F e ∧ isW cls e.view = false ∧ e.seg = c ∧ CVEquiv v e.view)
    (hx : XS s v r) :
    ServeTurn (MatchCallX cls CVEquiv F XS s) c [v] r c :=
  ⟨[], v, c, rfl, MatchAll.nil, ⟨(fun h => by rw [hv] at h; cases h),
    fun _ => Or.inr ⟨hno, hx, rfl⟩⟩⟩

/-! The matcher of Module 5, for a statement whose write calls are served from the barrier `ρ s c`. -/

/-- One write call, served by the recorded write `e` whose barrier number is `ρ s c`. -/
theorem serveR_write {F : RecEv Method Args Rel → Prop}
    {XS : Stmt → CallView Method Args → Result Rel → Prop} {ρ : Stmt → Nat → Nat} {s : Stmt}
    {c : Nat} {v : CallView Method Args} (hv : isW cls v = true) (e : RecEv Method Args Rel)
    (hF : F e) (hew : isW cls e.view = true) (hseg : e.seg = ρ s c) (hm : CVEquiv v e.view) :
    MatchCallXR cls CVEquiv F XS ρ s c v e.res (c + 1) :=
  ⟨fun _ => ⟨e, hF, hew, hseg, hm, rfl, rfl⟩, fun h => by rw [hv] at h; cases h⟩

/-- One read call, served by the recorded read `e` of the current segment. -/
theorem serveR_read {F : RecEv Method Args Rel → Prop}
    {XS : Stmt → CallView Method Args → Result Rel → Prop} {ρ : Stmt → Nat → Nat} {s : Stmt}
    {c : Nat} {v : CallView Method Args} (hv : isW cls v = false) (e : RecEv Method Args Rel)
    (hF : F e) (hew : isW cls e.view = false) (hseg : e.seg = c) (hm : CVEquiv v e.view) :
    MatchCallXR cls CVEquiv F XS ρ s c v e.res c :=
  ⟨(fun h => by rw [hv] at h; cases h), fun _ => Or.inl ⟨e, hF, hew, hseg, hm, rfl, rfl⟩⟩

theorem nw_single_read {v : CallView Method Args} (h : isW cls v = false) : nw cls [v] = 0 := by
  simp [nw, List.filter, h]

theorem nw_single_write {v : CallView Method Args} (h : isW cls v = true) : nw cls [v] = 1 := by
  simp [nw, List.filter, h]

/-! ### `marts`: one write -/

theorem conv_marts (recV liveV : Stmt → List (CallView Method Args)) (cr : Nat → Nat → Result Rel)
    (XS : Stmt → CallView Method Args → Result Rel → Prop) (L : Hist) (hL : L = Lmarts)
    (vm vm' : CallView Method Args) (hrec : recV sMart = [vm']) (hlive : liveV sMart = [vm])
    (hm : CVEquiv vm vm') (hw : isW cls vm = true) (hw' : isW cls vm' = true)
    (hcr : cr 0 0 = .ok) :
    ConvergentReplaySeg cls P .marts liveV (MatchCallX cls CVEquiv (InRec cls recV cr L) XS)
      (InRec cls recV cr L) L := by
  subst hL
  refine ⟨1, Lmarts, 1, ?_, histEquiv_refl _, rfl, ?_⟩
  · have hk : (recV sMart)[0]? = some vm' := by rw [hrec]; rfl
    have he := inRec_mk (cr := cr) (L := Lmarts) (t := 0) (s := sMart) (r := .ok) (k := 0) rfl hk
    refine ReplaySeg.step (k := 0) (H := []) (c := 0) (c' := 1) (stmt := sMart) (r := .ok)
      ReplaySeg.zero rfl ?_
    rw [hlive]
    have := serve_write (XS := XS) (s := sMart) (c := 0) hw _ he hw' rfl hm
    have this' : ServeTurn (MatchCallX cls CVEquiv (InRec cls recV cr Lmarts) XS sMart) 0 [vm]
        (cr 0 0) 1 := this
    rw [hcr] at this'
    exact this'
  · rintro e ⟨t, s, r, k, v, hLt, hk, rfl⟩ hwv
    rcases t with _ | t
    · simp only [Lmarts, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hLt
      obtain ⟨rfl, -⟩ := hLt
      rw [hrec] at hk
      rcases k with _ | k
      · simp [Wt, nw]
      · simp at hk
    · simp [Lmarts] at hLt

/-! ### `audit`: three reads in one segment -/

theorem audit_reads (recV : Stmt → List (CallView Method Args)) (L : Hist) (hL : L = Laudit)
    (r0 r1 r2 : CallView Method Args) (hrec0 : recV sList = [r0]) (hrec1 : recV sSel = [r1])
    (hrec2 : recV sSelD = [r2]) (hr0 : isW cls r0 = false) (hr1 : isW cls r1 = false)
    (hr2 : isW cls r2 = false) :
    ∀ (t : Nat) (s : Stmt) (r : Result Rel) (k : Nat) (v : CallView Method Args),
      L[t]? = some (s, r) → (recV s)[k]? = some v → isW cls v = false ∧
        (∀ t' ≤ t, Wt cls recV L t' = 0) := by
  subst hL
  have hW : ∀ t', t' ≤ 3 → Wt cls recV Laudit t' = 0 := by
    intro t' ht'
    have h1 : Wt cls recV Laudit 1 = 0 := by
      rw [Wt_succ_of cls recV Laudit 0 (sList, .rel [0]) rfl, hrec0, nw_single_read hr0]; rfl
    have h2 : Wt cls recV Laudit 2 = 0 := by
      rw [Wt_succ_of cls recV Laudit 1 (sSel, .rel [1, 2, 3]) rfl, hrec1, nw_single_read hr1, h1]
    have h3 : Wt cls recV Laudit 3 = 0 := by
      rw [Wt_succ_of cls recV Laudit 2 (sSelD, .rel [3, 2, 1]) rfl, hrec2, nw_single_read hr2, h2]
    rcases (by omega : t' = 0 ∨ t' = 1 ∨ t' = 2 ∨ t' = 3) with rfl | rfl | rfl | rfl
    · rfl
    · exact h1
    · exact h2
    · exact h3
  intro t s r k v hLt hk
  have ht3 : t < 3 := by
    have := (List.getElem?_eq_some_iff.mp hLt).1
    simpa [Laudit] using this
  refine ⟨?_, fun t' ht' => hW t' (by omega)⟩
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · simp only [Laudit, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hLt
    obtain ⟨rfl, -⟩ := hLt
    rw [hrec0] at hk
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; rw [← hk]; exact hr0
    · simp at hk
  · simp only [Laudit, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hLt
    obtain ⟨rfl, -⟩ := hLt
    rw [hrec1] at hk
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; rw [← hk]; exact hr1
    · simp at hk
  · simp only [Laudit, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hLt
    obtain ⟨rfl, -⟩ := hLt
    rw [hrec2] at hk
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; rw [← hk]; exact hr2
    · simp at hk

/-- The replay of `audit` in which the live turns `sSel` and `sSelD` are served by each other's
recorded read: both compile (after normalization) to the same call, so each may be served by either
recorded read of the segment. -/
theorem replay_audit_swap (recV liveV : Stmt → List (CallView Method Args))
    (cr : Nat → Nat → Result Rel) (XS : Stmt → CallView Method Args → Result Rel → Prop)
    (L : Hist) (hL : L = Laudit)
    (r0 r1 r2 l0 l1 l2 : CallView Method Args)
    (hrec0 : recV sList = [r0]) (hrec1 : recV sSel = [r1]) (hrec2 : recV sSelD = [r2])
    (hlive0 : liveV sList = [l0]) (hlive1 : liveV sSel = [l1]) (hlive2 : liveV sSelD = [l2])
    (h0 : CVEquiv l0 r0) (h1 : CVEquiv l1 r2) (h2 : CVEquiv l2 r1)
    (hr0 : isW cls r0 = false) (hr1 : isW cls r1 = false) (hr2 : isW cls r2 = false)
    (hl0 : isW cls l0 = false) (hl1 : isW cls l1 = false) (hl2 : isW cls l2 = false)
    (hc0 : cr 0 0 = .rel [0]) (hc1 : cr 1 0 = .rel [1, 2, 3]) (hc2 : cr 2 0 = .rel [3, 2, 1]) :
    ReplaySeg P .audit liveV (MatchCallX cls CVEquiv (InRec cls recV cr L) XS) 3
      [(sList, .rel [0]), (sSel, .rel [3, 2, 1]), (sSelD, .rel [1, 2, 3])] 0 := by
  have hA := audit_reads recV L hL r0 r1 r2 hrec0 hrec1 hrec2 hr0 hr1 hr2
  subst hL
  have hk0 : (recV sList)[0]? = some r0 := by rw [hrec0]; rfl
  have hk1 : (recV sSel)[0]? = some r1 := by rw [hrec1]; rfl
  have hk2 : (recV sSelD)[0]? = some r2 := by rw [hrec2]; rfl
  have e0 := inRec_mk (cr := cr) (L := Laudit) (t := 0) (s := sList) (r := .rel [0]) (k := 0) rfl hk0
  have e1 := inRec_mk (cr := cr) (L := Laudit) (t := 1) (s := sSel) (r := .rel [1, 2, 3]) (k := 0)
    rfl hk1
  have e2 := inRec_mk (cr := cr) (L := Laudit) (t := 2) (s := sSelD) (r := .rel [3, 2, 1]) (k := 0)
    rfl hk2
  have hW1 := (hA 0 sList (.rel [0]) 0 r0 rfl hk0).2
  have hW2 := (hA 1 sSel (.rel [1, 2, 3]) 0 r1 rfl hk1).2
  have hW3 := (hA 2 sSelD (.rel [3, 2, 1]) 0 r2 rfl hk2).2
  have s0 : (⟨r0, cr 0 0, Wt cls recV Laudit 0 + nw cls ((recV sList).take 0)⟩ :
      RecEv Method Args Rel).seg = 0 := rfl
  have s1 : (⟨r1, cr 1 0, Wt cls recV Laudit 1 + nw cls ((recV sSel).take 0)⟩ :
      RecEv Method Args Rel).seg = 0 := by
    show Wt cls recV Laudit 1 + nw cls ((recV sSel).take 0) = 0
    rw [hW2 1 (by omega)]; rfl
  have s2 : (⟨r2, cr 2 0, Wt cls recV Laudit 2 + nw cls ((recV sSelD).take 0)⟩ :
      RecEv Method Args Rel).seg = 0 := by
    show Wt cls recV Laudit 2 + nw cls ((recV sSelD).take 0) = 0
    rw [hW3 2 (by omega)]; rfl
  refine ReplaySeg.step (k := 2) (H := [(sList, .rel [0]), (sSel, .rel [3, 2, 1])]) (c := 0)
    (c' := 0) (stmt := sSelD) (r := .rel [1, 2, 3]) ?_ rfl ?_
  · refine ReplaySeg.step (k := 1) (H := [(sList, .rel [0])]) (c := 0) (c' := 0) (stmt := sSel)
      (r := .rel [3, 2, 1]) ?_ rfl ?_
    · refine ReplaySeg.step (k := 0) (H := []) (c := 0) (c' := 0) (stmt := sList)
        (r := .rel [0]) ReplaySeg.zero rfl ?_
      rw [hlive0]
      have := serve_read (XS := XS) (s := sList) (c := 0) hl0 _ e0 hr0 s0 h0
      have this' : ServeTurn (MatchCallX cls CVEquiv (InRec cls recV cr Laudit) XS sList) 0 [l0]
          (cr 0 0) 0 := this
      rw [hc0] at this'; exact this'
    · rw [hlive1]
      have := serve_read (XS := XS) (s := sSel) (c := 0) hl1 _ e2 hr2 s2 h1
      have this' : ServeTurn (MatchCallX cls CVEquiv (InRec cls recV cr Laudit) XS sSel) 0 [l1]
          (cr 2 0) 0 := this
      rw [hc2] at this'; exact this'
  · rw [hlive2]
    have := serve_read (XS := XS) (s := sSelD) (c := 0) hl2 _ e1 hr1 s1 h2
    have this' : ServeTurn (MatchCallX cls CVEquiv (InRec cls recV cr Laudit) XS sSelD) 0 [l2]
        (cr 1 0) 0 := this
    rw [hc1] at this'; exact this'

theorem conv_audit_swap (recV liveV : Stmt → List (CallView Method Args))
    (cr : Nat → Nat → Result Rel) (XS : Stmt → CallView Method Args → Result Rel → Prop)
    (L : Hist) (hL : L = Laudit)
    (r0 r1 r2 l0 l1 l2 : CallView Method Args)
    (hrec0 : recV sList = [r0]) (hrec1 : recV sSel = [r1]) (hrec2 : recV sSelD = [r2])
    (hlive0 : liveV sList = [l0]) (hlive1 : liveV sSel = [l1]) (hlive2 : liveV sSelD = [l2])
    (h0 : CVEquiv l0 r0) (h1 : CVEquiv l1 r2) (h2 : CVEquiv l2 r1)
    (hr0 : isW cls r0 = false) (hr1 : isW cls r1 = false) (hr2 : isW cls r2 = false)
    (hl0 : isW cls l0 = false) (hl1 : isW cls l1 = false) (hl2 : isW cls l2 = false)
    (hc0 : cr 0 0 = .rel [0]) (hc1 : cr 1 0 = .rel [1, 2, 3]) (hc2 : cr 2 0 = .rel [3, 2, 1]) :
    ConvergentReplaySeg cls P .audit liveV (MatchCallX cls CVEquiv (InRec cls recV cr L) XS)
      (InRec cls recV cr L) L := by
  have hA := audit_reads recV L hL r0 r1 r2 hrec0 hrec1 hrec2 hr0 hr1 hr2
  have hrep := replay_audit_swap recV liveV cr XS L hL r0 r1 r2 l0 l1 l2 hrec0 hrec1 hrec2 hlive0
    hlive1 hlive2 h0 h1 h2 hr0 hr1 hr2 hl0 hl1 hl2 hc0 hc1 hc2
  subst hL
  refine ⟨3, _, 0, hrep, ?_, rfl, ?_⟩
  · refine LForall₂.cons ⟨rfl, ResEquiv.refl _⟩ (LForall₂.cons ⟨rfl, ?_⟩
      (LForall₂.cons ⟨rfl, ?_⟩ LForall₂.nil))
    · show List.Perm [3, 2, 1] [1, 2, 3]; decide
    · show List.Perm [1, 2, 3] [3, 2, 1]; decide
  · rintro e ⟨t, s, r, k, v, hLt, hk, rfl⟩ hwv
    have := (hA t s r k v hLt hk).1
    rw [this] at hwv; cases hwv

theorem conv_audit_id (recV liveV : Stmt → List (CallView Method Args))
    (cr : Nat → Nat → Result Rel) (XS : Stmt → CallView Method Args → Result Rel → Prop)
    (L : Hist) (hL : L = Laudit)
    (r0 r1 r2 l0 l1 l2 : CallView Method Args)
    (hrec0 : recV sList = [r0]) (hrec1 : recV sSel = [r1]) (hrec2 : recV sSelD = [r2])
    (hlive0 : liveV sList = [l0]) (hlive1 : liveV sSel = [l1]) (hlive2 : liveV sSelD = [l2])
    (h0 : CVEquiv l0 r0) (h1 : CVEquiv l1 r1) (h2 : CVEquiv l2 r2)
    (hr0 : isW cls r0 = false) (hr1 : isW cls r1 = false) (hr2 : isW cls r2 = false)
    (hl0 : isW cls l0 = false) (hl1 : isW cls l1 = false) (hl2 : isW cls l2 = false)
    (hc0 : cr 0 0 = .rel [0]) (hc1 : cr 1 0 = .rel [1, 2, 3]) (hc2 : cr 2 0 = .rel [3, 2, 1]) :
    ConvergentReplaySeg cls P .audit liveV (MatchCallX cls CVEquiv (InRec cls recV cr L) XS)
      (InRec cls recV cr L) L := by
  have hA := audit_reads recV L hL r0 r1 r2 hrec0 hrec1 hrec2 hr0 hr1 hr2
  subst hL
  have hk0 : (recV sList)[0]? = some r0 := by rw [hrec0]; rfl
  have hk1 : (recV sSel)[0]? = some r1 := by rw [hrec1]; rfl
  have hk2 : (recV sSelD)[0]? = some r2 := by rw [hrec2]; rfl
  have e0 := inRec_mk (cr := cr) (L := Laudit) (t := 0) (s := sList) (r := .rel [0]) (k := 0) rfl hk0
  have e1 := inRec_mk (cr := cr) (L := Laudit) (t := 1) (s := sSel) (r := .rel [1, 2, 3]) (k := 0)
    rfl hk1
  have e2 := inRec_mk (cr := cr) (L := Laudit) (t := 2) (s := sSelD) (r := .rel [3, 2, 1]) (k := 0)
    rfl hk2
  have hW2 := (hA 1 sSel (.rel [1, 2, 3]) 0 r1 rfl hk1).2
  have hW3 := (hA 2 sSelD (.rel [3, 2, 1]) 0 r2 rfl hk2).2
  have s0 : (⟨r0, cr 0 0, Wt cls recV Laudit 0 + nw cls ((recV sList).take 0)⟩ :
      RecEv Method Args Rel).seg = 0 := rfl
  have s1 : (⟨r1, cr 1 0, Wt cls recV Laudit 1 + nw cls ((recV sSel).take 0)⟩ :
      RecEv Method Args Rel).seg = 0 := by
    show Wt cls recV Laudit 1 + nw cls ((recV sSel).take 0) = 0
    rw [hW2 1 (by omega)]; rfl
  have s2 : (⟨r2, cr 2 0, Wt cls recV Laudit 2 + nw cls ((recV sSelD).take 0)⟩ :
      RecEv Method Args Rel).seg = 0 := by
    show Wt cls recV Laudit 2 + nw cls ((recV sSelD).take 0) = 0
    rw [hW3 2 (by omega)]; rfl
  refine ⟨3, Laudit, 0, ?_, histEquiv_refl _, rfl, ?_⟩
  · refine ReplaySeg.step (k := 2) (H := [(sList, .rel [0]), (sSel, .rel [1, 2, 3])]) (c := 0)
      (c' := 0) (stmt := sSelD) (r := .rel [3, 2, 1]) ?_ rfl ?_
    · refine ReplaySeg.step (k := 1) (H := [(sList, .rel [0])]) (c := 0) (c' := 0) (stmt := sSel)
        (r := .rel [1, 2, 3]) ?_ rfl ?_
      · refine ReplaySeg.step (k := 0) (H := []) (c := 0) (c' := 0) (stmt := sList)
          (r := .rel [0]) ReplaySeg.zero rfl ?_
        rw [hlive0]
        have := serve_read (XS := XS) (s := sList) (c := 0) hl0 _ e0 hr0 s0 h0
        have this' : ServeTurn (MatchCallX cls CVEquiv (InRec cls recV cr Laudit) XS sList) 0 [l0]
            (cr 0 0) 0 := this
        rw [hc0] at this'; exact this'
      · rw [hlive1]
        have := serve_read (XS := XS) (s := sSel) (c := 0) hl1 _ e1 hr1 s1 h1
        have this' : ServeTurn (MatchCallX cls CVEquiv (InRec cls recV cr Laudit) XS sSel) 0 [l1]
            (cr 1 0) 0 := this
        rw [hc1] at this'; exact this'
    · rw [hlive2]
      have := serve_read (XS := XS) (s := sSelD) (c := 0) hl2 _ e2 hr2 s2 h2
      have this' : ServeTurn (MatchCallX cls CVEquiv (InRec cls recV cr Laudit) XS sSelD) 0 [l2]
          (cr 2 0) 0 := this
      rw [hc2] at this'; exact this'
  · rintro e ⟨t, s, r, k, v, hLt, hk, rfl⟩ hwv
    have := (hA t s r k v hLt hk).1
    rw [this] at hwv; cases hwv

/-! ### `staging`: a read with no local candidate, then a write -/

/-- The recorded calls of `staging`, read off its history: its check is a read (`rc`), its
materialization a write (`rs`); nothing else. -/
theorem staging_calls (recV : Stmt → List (CallView Method Args)) (L : Hist) (hL : L = Lstaging)
    (rc rs : CallView Method Args) (hrecC : recV sCheck = [rc]) (hrecS : recV sStg = [rs])
    (hrc : isW cls rc = false) (hrs : isW cls rs = true) :
    (Wt cls recV L 0 = 0 ∧ Wt cls recV L 1 = 0 ∧ Wt cls recV L 2 = 1) ∧
    ∀ (t : Nat) (s : Stmt) (r : Result Rel) (k : Nat) (v : CallView Method Args),
      L[t]? = some (s, r) → (recV s)[k]? = some v →
        (t = 0 ∧ k = 0 ∧ v = rc) ∨ (t = 1 ∧ k = 0 ∧ v = rs) := by
  subst hL
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · rw [Wt_succ_of cls recV Lstaging 0 (sCheck, .rel [0]) rfl, hrecC, nw_single_read hrc]; rfl
  · rw [Wt_succ_of cls recV Lstaging 1 (sStg, .ok) rfl,
      Wt_succ_of cls recV Lstaging 0 (sCheck, .rel [0]) rfl, hrecC, hrecS, nw_single_read hrc,
      nw_single_write hrs]; rfl
  · intro t s r k v hLt hk
    rcases t with _ | _ | t
    · simp only [Lstaging, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hLt
      obtain ⟨rfl, -⟩ := hLt
      rw [hrecC] at hk
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        exact Or.inl ⟨rfl, rfl, hk.symm⟩
      · simp at hk
    · simp only [Lstaging, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hLt
      obtain ⟨rfl, -⟩ := hLt
      rw [hrecS] at hk
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        exact Or.inr ⟨rfl, rfl, hk.symm⟩
      · simp at hk
    · simp [Lstaging] at hLt

/-- If the live check has no local candidate — nothing recorded in the segment is `~` it — rule 3
serves it, and then the write is served by the node's own barrier. -/
theorem conv_staging (recV liveV : Stmt → List (CallView Method Args))
    (cr : Nat → Nat → Result Rel) (XS : Stmt → CallView Method Args → Result Rel → Prop)
    (L : Hist) (hL : L = Lstaging) (rc lc rs ls : CallView Method Args)
    (hrecC : recV sCheck = [rc]) (hliveC : liveV sCheck = [lc])
    (hrecS : recV sStg = [rs]) (hliveS : liveV sStg = [ls])
    (hno : ¬ CVEquiv lc rc) (hx : XS sCheck lc (.rel [0])) (hms : CVEquiv ls rs)
    (hrc : isW cls rc = false) (hlc : isW cls lc = false) (hrs : isW cls rs = true)
    (hls : isW cls ls = true) (hc1 : cr 1 0 = .ok) :
    ConvergentReplaySeg cls P .staging liveV (MatchCallX cls CVEquiv (InRec cls recV cr L) XS)
      (InRec cls recV cr L) L := by
  obtain ⟨⟨hW0, hW1, hW2⟩, hcalls⟩ := staging_calls recV L hL rc rs hrecC hrecS hrc hrs
  subst hL
  have hkC : (recV sCheck)[0]? = some rc := by rw [hrecC]; rfl
  have hkS : (recV sStg)[0]? = some rs := by rw [hrecS]; rfl
  have eS := inRec_mk (cr := cr) (L := Lstaging) (t := 1) (s := sStg) (r := .ok) (k := 0) rfl hkS
  have sS : (⟨rs, cr 1 0, Wt cls recV Lstaging 1 + nw cls ((recV sStg).take 0)⟩ :
      RecEv Method Args Rel).seg = 0 := by
    show Wt cls recV Lstaging 1 + nw cls ((recV sStg).take 0) = 0
    rw [hW1]; rfl
  refine ⟨2, Lstaging, 1, ?_, histEquiv_refl _, rfl, ?_⟩
  · refine ReplaySeg.step (k := 1) (H := [(sCheck, .rel [0])]) (c := 0) (c' := 1) (stmt := sStg)
      (r := .ok) ?_ rfl ?_
    · refine ReplaySeg.step (k := 0) (H := []) (c := 0) (c' := 0) (stmt := sCheck)
        (r := .rel [0]) ReplaySeg.zero rfl ?_
      rw [hliveC]
      refine serve_read_x (XS := XS) (s := sCheck) (c := 0) hlc ?_ hx
      rintro ⟨e, ⟨t, s, r, k, v, hLt, hk, rfl⟩, hew, hseg, hm⟩
      rcases hcalls t s r k v hLt hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact hno hm
      · rw [hrs] at hew; cases hew
    · rw [hliveS]
      have := serve_write (XS := XS) (s := sStg) (c := 0) hls _ eS hrs sS hms
      have this' : ServeTurn (MatchCallX cls CVEquiv (InRec cls recV cr Lstaging) XS sStg) 0 [ls]
          (cr 1 0) 1 := this
      rw [hc1] at this'; exact this'
  · rintro e ⟨t, s, r, k, v, hLt, hk, rfl⟩ hwv
    rcases hcalls t s r k v hLt hk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [hrc] at hwv; cases hwv
    · show Wt cls recV Lstaging 1 + nw cls ((recV sStg).take 0) < 1
      rw [hW1]; simp [nw]

/-- **Rule 3 is necessary.** Without it (the matcher has no second route), `staging`'s recorded
history cannot be replayed against the second dbt version: the only recorded read of its segment is
the first version's `probe_relation`, which the live `get_relation` does not match. -/
theorem rule3_necessary (recV liveV : Stmt → List (CallView Method Args))
    (cr : Nat → Nat → Result Rel) (rc lc rs : CallView Method Args)
    (hrecC : recV sCheck = [rc]) (hliveC : liveV sCheck = [lc]) (hrecS : recV sStg = [rs])
    (hno : ¬ CVEquiv lc rc) (hlc : isW cls lc = false) (hrc : isW cls rc = false)
    (hrs : isW cls rs = true) :
    ¬ ConvergentReplaySeg cls P .staging liveV
      (MatchCallX cls CVEquiv (InRec cls recV cr Lstaging) (fun _ _ _ => False))
      (InRec cls recV cr Lstaging) Lstaging := by
  obtain ⟨-, hcalls⟩ := staging_calls recV Lstaging rfl rc rs hrecC hrecS hrc hrs
  rintro ⟨K, H, c, hrep, hHE, -, -⟩
  have hlenH : H.length = K := ReplaySeg.length hrep
  have hlen : H.length = Lstaging.length := LForall₂.length_eq hHE
  have hK : 1 ≤ K := by
    have : Lstaging.length = 2 := rfl
    omega
  obtain ⟨c', hpre⟩ := ReplaySeg.prefix hrep 1 hK
  obtain ⟨H₀, c₀, stmt, r₀, hrep0, hnxt, hserve, -⟩ := ReplaySeg.step_inv hpre
  cases hrep0
  have hs : stmt = sCheck := by
    change nxtF .staging 0 = some stmt at hnxt
    simp [nxtF] at hnxt; exact hnxt.symm
  subst hs
  obtain ⟨vs₀, v, c₁, hvs, hall, hml⟩ := hserve
  rw [hliveC] at hvs
  obtain ⟨rfl, rfl⟩ : vs₀ = [] ∧ v = lc := by
    rcases List.append_eq_singleton_iff.mp hvs.symm with ⟨rfl, hv⟩ | ⟨hv, hv'⟩
    · exact ⟨rfl, by simpa using hv⟩
    · simp at hv'
  cases hall
  rcases hml.2 hlc with ⟨e, ⟨t, s, r, k, v, hLt, hk, rfl⟩, hew, hseg, hm, -⟩ | ⟨-, hx, -⟩
  · rcases hcalls t s r k v hLt hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact hno hm
    · rw [hrs] at hew; cases hew
  · exact hx

/-! ### `report`: a single read with no local candidate -/

/-- The only recorded call of `report` is its row-count read (`rc`). -/
theorem report_calls (recV : Stmt → List (CallView Method Args)) (rc : CallView Method Args)
    (hrecC : recV sCount = [rc]) :
    ∀ (t : Nat) (s : Stmt) (r : Result Rel) (k : Nat) (v : CallView Method Args),
      Lreport[t]? = some (s, r) → (recV s)[k]? = some v → v = rc := by
  intro t s r k v hLt hk
  rcases t with _ | t
  · simp only [Lreport, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hLt
    obtain ⟨rfl, -⟩ := hLt
    rw [hrecC] at hk
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; exact hk.symm
    · simp at hk
  · simp [Lreport] at hLt

/-- `report`'s one call matches nothing in its own segment — nothing recorded is `~` it — so rule 3
serves it. -/
theorem conv_report (recV liveV : Stmt → List (CallView Method Args))
    (cr : Nat → Nat → Result Rel) (XS : Stmt → CallView Method Args → Result Rel → Prop)
    (L : Hist) (hL : L = Lreport) (rc lc : CallView Method Args)
    (hrecC : recV sCount = [rc]) (hliveC : liveV sCount = [lc])
    (hno : ¬ CVEquiv lc rc) (hx : XS sCount lc (.rel [3]))
    (hrc : isW cls rc = false) (hlc : isW cls lc = false) :
    ConvergentReplaySeg cls P .report liveV (MatchCallX cls CVEquiv (InRec cls recV cr L) XS)
      (InRec cls recV cr L) L := by
  have hcalls := report_calls recV rc hrecC
  subst hL
  refine ⟨1, [(sCount, .rel [3])], 0, ?_, ?_, rfl, ?_⟩
  · refine ReplaySeg.step (k := 0) (H := []) (c := 0) (c' := 0) (stmt := sCount)
      (r := .rel [3]) ReplaySeg.zero rfl ?_
    rw [hliveC]
    refine serve_read_x (XS := XS) (s := sCount) (c := 0) hlc ?_ hx
    rintro ⟨e, ⟨t, s, r, k, v, hLt, hk, rfl⟩, hew, hseg, hm⟩
    rw [hcalls t s r k v hLt hk] at hm
    exact hno hm
  · exact histEquiv_refl _
  · rintro e ⟨t, s, r, k, v, hLt, hk, rfl⟩ hwv
    rw [hcalls t s r k v hLt hk, hrc] at hwv; cases hwv

/-- **Rule 3 is necessary for `report` too.** -/
theorem rule3_necessary_report (recV liveV : Stmt → List (CallView Method Args))
    (cr : Nat → Nat → Result Rel) (rc lc : CallView Method Args)
    (hrecC : recV sCount = [rc]) (hliveC : liveV sCount = [lc])
    (hno : ¬ CVEquiv lc rc) (hlc : isW cls lc = false) :
    ¬ ConvergentReplaySeg cls P .report liveV
      (MatchCallX cls CVEquiv (InRec cls recV cr Lreport) (fun _ _ _ => False))
      (InRec cls recV cr Lreport) Lreport := by
  have hcalls := report_calls recV rc hrecC
  rintro ⟨K, H, c, hrep, hHE, -, -⟩
  have hlenH : H.length = K := ReplaySeg.length hrep
  have hlen : H.length = Lreport.length := LForall₂.length_eq hHE
  have hK : 1 ≤ K := by
    have : Lreport.length = 1 := rfl
    omega
  obtain ⟨c', hpre⟩ := ReplaySeg.prefix hrep 1 hK
  obtain ⟨H₀, c₀, stmt, r₀, hrep0, hnxt, hserve, -⟩ := ReplaySeg.step_inv hpre
  cases hrep0
  have hs : stmt = sCount := by
    change nxtF .report 0 = some stmt at hnxt
    simp [nxtF] at hnxt; exact hnxt.symm
  subst hs
  obtain ⟨vs₀, v, c₁, hvs, hall, hml⟩ := hserve
  rw [hliveC] at hvs
  obtain ⟨rfl, rfl⟩ : vs₀ = [] ∧ v = lc := by
    rcases List.append_eq_singleton_iff.mp hvs.symm with ⟨rfl, hv⟩ | ⟨hv, hv'⟩
    · exact ⟨rfl, by simpa using hv⟩
    · simp at hv'
  cases hall
  rcases hml.2 hlc with ⟨e, ⟨t, s, r, k, v, hLt, hk, rfl⟩, hew, hseg, hm, -⟩ | ⟨-, hx, -⟩
  · rw [hcalls t s r k v hLt hk] at hm
    exact hno hm
  · exact hx

/-! ### `dims`: two bundles served in the other order, then a read

The recording engine emitted the bundles in the order 1, 2, the replaying engine emits 2, 1. The run
permutation `ρ` serves the live writes `u = 0..3` from the recorded barriers `2, 3, 0, 1`: the bundles are
swapped, and the two calls inside each bundle keep their order. -/

/-- Swap the two bundles: barriers `0, 1` and `2, 3` exchange places. -/
def swapRun (c : Nat) : Nat := if c < 2 then c + 2 else if c < 4 then c - 2 else c

/-- The barrier permutation node `n` applies to a live statement `s`: the `dims` node's write turn is a
run; every other turn, and every read, is served in its recorded order. -/
def ρex (n : Node) (s : Stmt) (c : Nat) : Nat :=
  match n, target s with
  | .dims, some _ => swapRun c
  | _, _ => c

theorem ρex_nodims (n : Node) (s : Stmt) (h : n ≠ .dims) (c : Nat) : ρex n s c = c := by
  cases n <;> first | rfl | exact absurd rfl h

theorem conv_dims (recV liveV : Stmt → List (CallView Method Args)) (cr : Nat → Nat → Result Rel)
    (XS : Stmt → CallView Method Args → Result Rel → Prop) (L : Hist) (hL : L = Ldims)
    (r0 r1 r2 r3 rv l0 l1 l2 l3 lv : CallView Method Args)
    (hrec : recV sBuild = [r0, r1, r2, r3, rv]) (hlive : liveV sBuild = [l0, l1, l2, l3, lv])
    (h0 : CVEquiv l0 r2) (h1 : CVEquiv l1 r3) (h2 : CVEquiv l2 r0) (h3 : CVEquiv l3 r1)
    (hv : CVEquiv lv rv)
    (hr0 : isW cls r0 = true) (hr1 : isW cls r1 = true) (hr2 : isW cls r2 = true)
    (hr3 : isW cls r3 = true) (hrv : isW cls rv = false)
    (hl0 : isW cls l0 = true) (hl1 : isW cls l1 = true) (hl2 : isW cls l2 = true)
    (hl3 : isW cls l3 = true) (hlv : isW cls lv = false)
    (hcr : cr 0 4 = .ok) :
    ConvergentReplaySeg cls P .dims liveV (MatchCallXR cls CVEquiv (InRec cls recV cr L) XS (ρex .dims))
      (InRec cls recV cr L) L := by
  subst hL
  have g0 : (recV sBuild)[0]? = some r0 := by rw [hrec]; rfl
  have g1 : (recV sBuild)[1]? = some r1 := by rw [hrec]; rfl
  have g2 : (recV sBuild)[2]? = some r2 := by rw [hrec]; rfl
  have g3 : (recV sBuild)[3]? = some r3 := by rw [hrec]; rfl
  have g4 : (recV sBuild)[4]? = some rv := by rw [hrec]; rfl
  have n1 : nw cls ((recV sBuild).take 1) = 1 := by rw [hrec]; simp [nw, List.filter, hr0]
  have n2 : nw cls ((recV sBuild).take 2) = 2 := by rw [hrec]; simp [nw, List.filter, hr0, hr1]
  have n3 : nw cls ((recV sBuild).take 3) = 3 := by
    rw [hrec]; simp [nw, List.filter, hr0, hr1, hr2]
  have n4 : nw cls ((recV sBuild).take 4) = 4 := by
    rw [hrec]; simp [nw, List.filter, hr0, hr1, hr2, hr3]
  have e0 := inRec_mk (cr := cr) (L := Ldims) (t := 0) (s := sBuild) (r := .ok) (k := 0) rfl g0
  have e1 := inRec_mk (cr := cr) (L := Ldims) (t := 0) (s := sBuild) (r := .ok) (k := 1) rfl g1
  have e2 := inRec_mk (cr := cr) (L := Ldims) (t := 0) (s := sBuild) (r := .ok) (k := 2) rfl g2
  have e3 := inRec_mk (cr := cr) (L := Ldims) (t := 0) (s := sBuild) (r := .ok) (k := 3) rfl g3
  have e4 := inRec_mk (cr := cr) (L := Ldims) (t := 0) (s := sBuild) (r := .ok) (k := 4) rfl g4
  have W0 : Wt cls recV Ldims 0 = 0 := rfl
  refine ⟨1, Ldims, 4, ?_, histEquiv_refl _, rfl, ?_⟩
  · refine ReplaySeg.step (k := 0) (H := []) (c := 0) (c' := 4) (stmt := sBuild) (r := .ok)
      ReplaySeg.zero rfl ?_
    rw [hlive]
    have s4 := serveR_read (XS := XS) (ρ := ρex .dims) (s := sBuild) (c := 4) hlv _ e4 hrv
      (by show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 4) = 4; rw [W0, n4]) hv
    rw [show (⟨rv, cr 0 4, Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 4)⟩ :
      RecEv Method Args Rel).res = cr 0 4 from rfl, hcr] at s4
    refine ⟨[l0, l1, l2, l3], lv, 4, rfl, ?_, s4⟩
    refine MatchAll.cons (c₁ := 1) (serveR_write (XS := XS) (ρ := ρex .dims)
      (s := sBuild) (c := 0) hl0 _ e2 hr2 (by
        show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 2) = swapRun 0
        rw [W0, n2]; rfl) h0) ?_
    refine MatchAll.cons (c₁ := 2) (serveR_write (XS := XS) (ρ := ρex .dims)
      (s := sBuild) (c := 1) hl1 _ e3 hr3 (by
        show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 3) = swapRun 1
        rw [W0, n3]; rfl) h1) ?_
    refine MatchAll.cons (c₁ := 3) (serveR_write (XS := XS) (ρ := ρex .dims)
      (s := sBuild) (c := 2) hl2 _ e0 hr0 (by
        show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 0) = swapRun 2
        rw [W0]; rfl) h2) ?_
    refine MatchAll.cons (c₁ := 4) (serveR_write (XS := XS) (ρ := ρex .dims)
      (s := sBuild) (c := 3) hl3 _ e1 hr1 (by
        show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 1) = swapRun 3
        rw [W0, n1]; rfl) h3) ?_
    exact MatchAll.nil
  · rintro e ⟨t, s, r, k, v, hLt, hk', rfl⟩ hwv
    rcases t with _ | t
    · simp only [Ldims, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hLt
      obtain ⟨rfl, -⟩ := hLt
      rw [hrec] at hk'
      rcases k with _ | _ | _ | _ | _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
        show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 0) < 4
        rw [W0]; simp [nw]
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk'
        show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 1) < 4
        rw [W0, n1]; omega
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk'
        show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 2) < 4
        rw [W0, n2]; omega
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk'
        show Wt cls recV Ldims 0 + nw cls ((recV sBuild).take 3) < 4
        rw [W0, n3]; omega
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk'
        rw [← hk', hrv] at hwv; cases hwv
      · simp at hk'
    · simp [Ldims] at hLt

/-- **Runs are necessary.** If every write is served from the barrier with its own number (`ρ = id`, as in
Modules 3–4), `dims`' recorded history cannot be replayed against the second dbt version: its first live
write is the *second* bundle's `create schema`, and the recording's barrier 0 is the first bundle's. -/
theorem strict_dims (recV liveV : Stmt → List (CallView Method Args)) (cr : Nat → Nat → Result Rel)
    (XS : Stmt → CallView Method Args → Result Rel → Prop)
    (r0 r1 r2 r3 rv l0 l1 l2 l3 lv : CallView Method Args)
    (hrec : recV sBuild = [r0, r1, r2, r3, rv]) (hlive : liveV sBuild = [l0, l1, l2, l3, lv])
    (hno : ¬ CVEquiv l0 r0)
    (hr0 : isW cls r0 = true) (hr1 : isW cls r1 = true) (hr2 : isW cls r2 = true)
    (hr3 : isW cls r3 = true) (hl0 : isW cls l0 = true) :
    ¬ ConvergentReplaySeg cls P .dims liveV
      (MatchCallXR cls CVEquiv (InRec cls recV cr Ldims) XS (fun _ c => c))
      (InRec cls recV cr Ldims) Ldims := by
  rintro ⟨K, H, c, hrep, hHE, -, -⟩
  have hlenH : H.length = K := ReplaySeg.length hrep
  have hlen : H.length = Ldims.length := LForall₂.length_eq hHE
  have hK : 1 ≤ K := by
    have : Ldims.length = 1 := rfl
    omega
  obtain ⟨c', hpre⟩ := ReplaySeg.prefix hrep 1 hK
  obtain ⟨H₀, c₀, stmt, r₀, hrep0, hnxt, hserve, -⟩ := ReplaySeg.step_inv hpre
  cases hrep0
  have hs : stmt = sBuild := by
    change nxtF .dims 0 = some stmt at hnxt
    simp [nxtF] at hnxt; exact hnxt.symm
  subst hs
  obtain ⟨vs₀, v, c₁, hvs, hall, hml⟩ := hserve
  rw [hlive] at hvs
  cases vs₀ with
  | nil => simp at hvs
  | cons a as =>
    simp only [List.cons_append, List.cons.injEq] at hvs
    obtain ⟨rfl, -⟩ := hvs
    cases hall with
    | cons hm hrest =>
      obtain ⟨e, ⟨t, s, r, k, w, hLt, hk, rfl⟩, hew, hseg, hmv, -⟩ := hm.1 hl0
      have W0 : Wt cls recV Ldims 0 = 0 := rfl
      rcases t with _ | t
      · simp only [Ldims, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hLt
        obtain ⟨rfl, -⟩ := hLt
        rw [hrec] at hk
        simp only [W0] at hseg
        rcases k with _ | _ | _ | _ | _ | k
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          exact hno (hk ▸ hmv)
        · simp [hrec, nw, List.filter, hr0] at hseg
        · simp [hrec, nw, List.filter, hr0, hr1] at hseg
        · simp [hrec, nw, List.filter, hr0, hr1, hr2] at hseg
        · simp [hrec, nw, List.filter, hr0, hr1, hr2, hr3] at hseg
        · simp at hk
      · simp [Ldims] at hLt

/-! ## The cross-node serve: why local matching fails, and why rule 3 licenses it -/

open Classical in
theorem slice_raw : slice Oraw [0] = [0] := by
  have hk : keep Oraw 0 = true := by
    rw [keep_zero]; exact decide_eq_true rfl
  simp [slice, List.filter, hk]

/-- No write by `staging` or `audit` falls between `staging`'s check (position 1)
and `audit`'s listing (position 2). -/
theorem noInterv₁ : ∀ q p o, 1 ≤ q → q ≤ run₁.N → run₁.node q = .staging →
    run₁.stmt q = sCheck → (run₁.node p = .staging ∨ run₁.node p = run₁.node 2) →
    ((q ≤ p ∧ p < 2) ∨ (2 ≤ p ∧ p < q)) → target (run₁.stmt p) = some o → ¬ Oraw o := by
  intro q p o hq1 hq7 hqn hqs hp hrng ht hO
  have hq : q = 1 := by
    rcases eight q hq1 hq7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (simp [run₁, node₁, stmt₁, sStg, sCheck] at hqn hqs)
  subst hq
  have : p = 1 := by rcases hrng with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  subst this
  simp [run₁, stmt₁, sCheck, target] at ht

/-- No write by `report` or `audit` falls between `audit`'s `select *` (position 3) and `report`'s
row count (position 7) — though `staging` and `marts` do write in between (third parties never matter). -/
theorem noInterv₂ : ∀ q p o, 1 ≤ q → q ≤ run₁.N → run₁.node q = .report →
    run₁.stmt q = sCount → (run₁.node p = .report ∨ run₁.node p = run₁.node 3) →
    ((q ≤ p ∧ p < 3) ∨ (3 ≤ p ∧ p < q)) → target (run₁.stmt p) = some o →
    ¬ (o = Tbl.raw) := by
  intro q p o hq1 hq7 hqn hqs hp hrng ht hO
  have hq : q = 7 := by
    rcases eight q hq1 hq7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (simp [run₁, node₁] at hqn hqs)
  subst hq
  rcases hrng with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · have hp7 : p ≤ 7 := by omega
    rcases eight p (by omega) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [run₁, node₁, stmt₁, sList, sSel, sSelD, sCount, target] at hp ht h1 h2

theorem hx_driver : XServe (L := driverLevel ret reads) (drvE E₁) driverView reads run₁ AllowedD
    .staging sCheck (driverView (.read (.existsIn Oraw))) (.rel [0]) := by
  refine ⟨.read .listRaw, .read (.existsIn Oraw), slice Oraw, 2, [0],
    Or.inl ⟨Oraw, rfl, rfl, rfl⟩, rfl, fun _ h => h, by decide, by decide, by decide,
    ⟨.listRaw, rfl⟩, fun _ h => h, rfl, noInterv₁, rfl, ?_⟩
  show Result.rel [0] = Result.rel (slice Oraw [0])
  rw [slice_raw]

theorem hx_adapter : XServe (L := Asem.level) (alphaComp (Query := Query) Asem E₁) adapterView
    reads run₁ AllowedA .staging sCheck (adapterView ⟨.getRel, .set Oraw⟩) (.rel [0]) := by
  refine ⟨⟨.listRels, .none⟩, ⟨.getRel, .set Oraw⟩, slice Oraw, 2, [0],
    Or.inl ⟨Oraw, rfl, rfl, rfl⟩, rfl, fun _ h => h, by decide, by decide, by decide,
    ⟨.listRaw, rfl⟩, fun _ h => h, rfl, noInterv₁, rfl, ?_⟩
  show Result.rel [0] = Result.rel (slice Oraw [0])
  rw [slice_raw]

/-- `report`'s row count is served from `audit`'s recorded `select *` (position 3), converted by
`countOf` — a relation of rows becomes a one-row relation, a different schema. -/
theorem hx_report_driver : XServe (L := driverLevel ret reads) (drvE E₁) driverView reads run₁
    AllowedD .report sCount (driverView (.read (.rowCount .raw))) (.rel [3]) := by
  refine ⟨.read (.sel .raw), .read (.rowCount .raw), countOf, 3, [1, 2, 3],
    Or.inr ⟨rfl, rfl, rfl⟩, rfl, fun _ h => h, by decide, by decide, by decide,
    ⟨.sel .raw, rfl⟩, fun _ h => h, rfl, noInterv₂, rfl, rfl⟩

theorem hx_report_adapter : XServe (L := Asem.level) (alphaComp (Query := Query) Asem E₁)
    adapterView reads run₁ AllowedA .report sCount
    (adapterView ⟨.countRel, .q (.rowCount .raw)⟩) (.rel [3]) := by
  refine ⟨⟨.runQuery, .q (.sel .raw)⟩, ⟨.countRel, .q (.rowCount .raw)⟩, countOf, 3, [1, 2, 3],
    Or.inr ⟨rfl, rfl, rfl⟩, rfl, fun _ h => h, by decide, by decide, by decide,
    ⟨.sel .raw, rfl⟩, fun _ h => h, rfl, noInterv₂, rfl, rfl⟩

/-! ## The recorded call results -/

/-- The recorded result of call `k` of the turn at position `j`, at the driver boundary; `k` is the
turn's last call. -/
theorem crD (n : Node) (j k : Nat) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (hn : node₁ j = n)
    (hlast : k + 1 = (drvE E₁ (stmt₁ j)).length) :
    recResOf (L := driverLevel ret reads) (drvE E₁) run₁.node run₁.stmt run₁.res S₀ run₁.N n
      (turnCount node₁ n j) k = res₁ j :=
  recResOf_last (L := driverLevel ret reads) (drvE E₁) run₁.node run₁.stmt run₁.res S₀ run₁.N n j k
    hj1 hj8 hn hlast

/-- … and at the adapter boundary. -/
theorem crA (n : Node) (j k : Nat) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (hn : node₁ j = n)
    (hlast : k + 1 = (alphaComp (Query := Query) Asem E₁ (stmt₁ j)).length) :
    recResOf (L := Asem.level) (alphaComp (Query := Query) Asem E₁) run₁.node run₁.stmt run₁.res
      S₀ run₁.N n (turnCount node₁ n j) k = res₁ j :=
  recResOf_last (L := Asem.level) (alphaComp (Query := Query) Asem E₁) run₁.node run₁.stmt run₁.res
    S₀ run₁.N n j k hj1 hj8 hn hlast

/-! ## Replay convergence, node by node, at each boundary -/

theorem hno_driver : ¬ CVEquiv (driverView (.read (.existsIn Oraw)))
    (driverView (.read (.probeIn Oraw))) := by
  intro hm
  have h : Args.q (Query.existsIn Oraw) = Args.q (Query.probeIn Oraw) := hm.2
  cases h

theorem hno_adapter : ¬ CVEquiv (adapterView (⟨.getRel, .set Oraw⟩ : Call))
    (adapterView (⟨.probeRel, .set Oraw⟩ : Call)) := by
  intro hm
  have h : Method.getRel = Method.probeRel := hm.1
  cases h

theorem hno_report_driver : ¬ CVEquiv (driverView (.read (.rowCount .raw)))
    (driverView (.read (.cnt .raw))) := by
  intro hm
  have h : Args.q (Query.rowCount .raw) = Args.q (Query.cnt .raw) := hm.2
  cases h

theorem hno_report_adapter : ¬ CVEquiv (adapterView (⟨.countRel, .q (.rowCount .raw)⟩ : Call))
    (adapterView (⟨.runQuery, .q (.cnt .raw)⟩ : Call)) := by
  intro hm
  have h : Method.countRel = Method.runQuery := hm.1
  cases h

/-- **Driver boundary.** `audit`'s live reads `sSel` and `sSelD` are served by each other's recorded
read (after normalization their calls coincide); `staging`'s check, which no recorded read of its
segment matches, is served by rule 3 from `audit`'s `list_relations`; the writes match by barrier. -/
theorem hCS_driver : ReplayOKXR (L := driverLevel ret reads) cls (drvE E₁) (drvE E₂) driverView
    reads run₁ AllowedD ρex := by
  intro n
  cases n with
  | audit =>
    exact conv_audit_swap (fun s => (drvE E₁ s).map driverView) (fun s => (drvE E₂ s).map driverView)
      _ _ (recordingOf run₁ .audit) rec_audit
      (driverView (.read .listRaw)) (driverView (.read (.sel .raw)))
      (driverView (.read (.selDesc .raw))) (driverView (.read .listRaw))
      (driverView (.read (.sel .raw))) (driverView (.read (.selDesc .raw)))
      rfl rfl rfl rfl rfl rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
      (crD .audit 2 0 (by decide) (by decide) rfl rfl) (crD .audit 3 0 (by decide) (by decide) rfl rfl)
      (crD .audit 4 0 (by decide) (by decide) rfl rfl)
  | staging =>
    exact conv_staging (fun s => (drvE E₁ s).map driverView) (fun s => (drvE E₂ s).map driverView)
      _ _ (recordingOf run₁ .staging) rec_staging
      (driverView (.read (.probeIn Oraw))) (driverView (.read (.existsIn Oraw)))
      (driverView (.write .stg (.sel .raw))) (driverView (.write .stg (rend (.sel .raw))))
      rfl rfl rfl rfl hno_driver hx_driver ⟨rfl, rfl⟩ rfl rfl rfl rfl
      (crD .staging 5 0 (by decide) (by decide) rfl rfl)
  | marts =>
    exact conv_marts (fun s => (drvE E₁ s).map driverView) (fun s => (drvE E₂ s).map driverView)
      _ _ (recordingOf run₁ .marts) rec_marts
      (driverView (.write .mart (rend (.cnt .stg)))) (driverView (.write .mart (.cnt .stg)))
      rfl rfl ⟨rfl, rfl⟩ rfl rfl (crD .marts 6 0 (by decide) (by decide) rfl rfl)
  | report =>
    exact conv_report (fun s => (drvE E₁ s).map driverView) (fun s => (drvE E₂ s).map driverView)
      _ _ (recordingOf run₁ .report) rec_report
      (driverView (.read (.cnt .raw))) (driverView (.read (.rowCount .raw)))
      rfl rfl hno_report_driver hx_report_driver rfl rfl
  | dims =>
    exact conv_dims (fun s => (drvE E₁ s).map driverView) (fun s => (drvE E₂ s).map driverView)
      _ _ (recordingOf run₁ .dims) rec_dims
      (driverView (.write .dim (.addSchema 1))) (driverView (.write .dim (.addView 1)))
      (driverView (.write .dim (.addSchema 2))) (driverView (.write .dim (.addView 2)))
      (driverView (.read .dimCount))
      (driverView (.write .dim (.addSchema 2))) (driverView (.write .dim (.addView 2)))
      (driverView (.write .dim (.addSchema 1))) (driverView (.write .dim (.addView 1)))
      (driverView (.read .dimCount))
      rfl rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (crD .dims 8 4 (by decide) (by decide) rfl rfl)

/-- **Adapter boundary.** The same, over the adapter calls `α` issues; the views are literal, so the
reads of `audit` match their own recorded read, and `staging`'s `get_relation` (the recording has a
`probe_relation`) is served from `audit`'s `list_relations`. -/
theorem hCS_adapter : ReplayOKXR (L := Asem.level) cls (alphaComp (Query := Query) Asem E₁)
    (alphaComp (Query := Query) Asem E₂) adapterView reads run₁
    AllowedA ρex := by
  intro n
  cases n with
  | audit =>
    exact conv_audit_id (fun s => (alphaComp (Query := Query) Asem E₁ s).map adapterView)
      (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
      _ _ (recordingOf run₁ .audit) rec_audit
      (adapterView ⟨.listRels, .none⟩) (adapterView ⟨.runQuery, .q (.sel .raw)⟩)
      (adapterView ⟨.runQuery, .q (.selDesc .raw)⟩) (adapterView ⟨.listRels, .none⟩)
      (adapterView ⟨.runQuery, .q (.sel .raw)⟩) (adapterView ⟨.runQuery, .q (.selDesc .raw)⟩)
      rfl rfl rfl rfl rfl rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
      (crA .audit 2 0 (by decide) (by decide) rfl rfl) (crA .audit 3 0 (by decide) (by decide) rfl rfl)
      (crA .audit 4 0 (by decide) (by decide) rfl rfl)
  | staging =>
    exact conv_staging (fun s => (alphaComp (Query := Query) Asem E₁ s).map adapterView)
      (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
      _ _ (recordingOf run₁ .staging) rec_staging
      (adapterView ⟨.probeRel, .set Oraw⟩) (adapterView ⟨.getRel, .set Oraw⟩)
      (adapterView ⟨.ctas, .tq .stg (.sel .raw)⟩) (adapterView ⟨.ctas, .tq .stg (.sel .raw)⟩)
      rfl rfl rfl rfl hno_adapter hx_adapter ⟨rfl, rfl⟩ rfl rfl rfl rfl
      (crA .staging 5 0 (by decide) (by decide) rfl rfl)
  | marts =>
    exact conv_marts (fun s => (alphaComp (Query := Query) Asem E₁ s).map adapterView)
      (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
      _ _ (recordingOf run₁ .marts) rec_marts
      (adapterView ⟨.ctas, .tq .mart (.cnt .stg)⟩) (adapterView ⟨.ctas, .tq .mart (.cnt .stg)⟩)
      rfl rfl ⟨rfl, rfl⟩ rfl rfl (crA .marts 6 0 (by decide) (by decide) rfl rfl)
  | report =>
    exact conv_report (fun s => (alphaComp (Query := Query) Asem E₁ s).map adapterView)
      (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
      _ _ (recordingOf run₁ .report) rec_report
      (adapterView ⟨.runQuery, .q (.cnt .raw)⟩) (adapterView ⟨.countRel, .q (.rowCount .raw)⟩)
      rfl rfl hno_report_adapter hx_report_adapter rfl rfl
  | dims =>
    exact conv_dims (fun s => (alphaComp (Query := Query) Asem E₁ s).map adapterView)
      (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
      _ _ (recordingOf run₁ .dims) rec_dims
      (adapterView ⟨.ctas, .tq .dim (.addSchema 1)⟩) (adapterView ⟨.ctas, .tq .dim (.addView 1)⟩)
      (adapterView ⟨.ctas, .tq .dim (.addSchema 2)⟩) (adapterView ⟨.ctas, .tq .dim (.addView 2)⟩)
      (adapterView ⟨.runQuery, .q .dimCount⟩)
      (adapterView ⟨.ctas, .tq .dim (.addSchema 2)⟩) (adapterView ⟨.ctas, .tq .dim (.addView 2)⟩)
      (adapterView ⟨.ctas, .tq .dim (.addSchema 1)⟩) (adapterView ⟨.ctas, .tq .dim (.addView 1)⟩)
      (adapterView ⟨.runQuery, .q .dimCount⟩)
      rfl rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (crA .dims 8 4 (by decide) (by decide) rfl rfl)

/-! ## Runs: the two bundles commute, so serving them in either order is a valid run

A bundle is `create schema k; create view k`. Its two calls do not commute (the view is created only if the
schema exists: `bundle_order_matters`), but the two bundles do. -/

/-- The driver calls of bundle `k`. -/
def bundleD (k : Nat) : List (DriverCall Tbl Query) :=
  [.write .dim (.addSchema k), .write .dim (.addView k)]

theorem rows_upd (S : St) (v : Rel) : rows (upd S .dim v) .dim = v := by simp [rows, upd]

theorem upd_upd (S : St) (a b : Rel) : upd (upd S .dim a) .dim b = upd S .dim b := by
  funext o; by_cases ho : o = .dim <;> simp [upd, ho]

/-- Running bundle `k` appends the schema and then the view. -/
theorem bundleD_eff (S : St) (k : Nat) :
    List.foldl (execS ret) S (bundleD k) = upd S .dim (rows S .dim ++ [10 * k, 10 * k + 1]) := by
  funext o
  by_cases ho : o = .dim
  · subst ho; simp [bundleD, List.foldl, execS, upd, ret, rows]
  · simp [bundleD, List.foldl, execS, upd, ho]

/-- **The two bundles commute**, at every state, up to `~`: they append disjoint pieces of the table. -/
theorem bundles_commute_driver : BlockCommute (driverLevel ret reads) (bundleD 1) (bundleD 2) := by
  intro S
  show StateEquiv (List.foldl (execS ret) (List.foldl (execS ret) S (bundleD 1)) (bundleD 2))
    (List.foldl (execS ret) (List.foldl (execS ret) S (bundleD 2)) (bundleD 1))
  simp only [bundleD_eff, rows_upd, upd_upd]
  refine upd_equiv (stateEquiv_refl S) .dim ?_
  show List.Perm _ _
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left _ (by decide)

/-- … and at the adapter boundary: the adapter calls of a bundle act as its driver calls. -/
theorem bundles_commute_adapter :
    BlockCommute Asem.level (bundleCalls 1) (bundleCalls 2) := by
  intro S
  have e : ∀ (S : St) (k : Nat), List.foldl Astep S (bundleCalls k) =
      List.foldl (execS ret) S (bundleD k) := fun _ _ => rfl
  show StateEquiv (List.foldl Astep (List.foldl Astep S (bundleCalls 1)) (bundleCalls 2))
    (List.foldl Astep (List.foldl Astep S (bundleCalls 2)) (bundleCalls 1))
  simp only [e]
  exact bundles_commute_driver S

/-- **The order inside a bundle matters**: creating the view before its schema leaves the table
without the view. So a run's bundles are indivisible; only whole bundles may be reordered. -/
theorem bundle_order_matters :
    ¬ StateEquiv (List.foldl (execS ret) S₀ [.write .dim (.addView 1), .write .dim (.addSchema 1)])
      (List.foldl (execS ret) S₀ (bundleD 1)) := by
  intro h
  have h' := h .dim
  have e1 : List.foldl (execS ret) S₀ [.write .dim (.addView 1), .write .dim (.addSchema 1)] .dim =
      some [10] := by simp [List.foldl, execS, ret, rows, S₀]
  have e2 : List.foldl (execS ret) S₀ (bundleD 1) .dim = some [10, 11] := by
    simp [bundleD, List.foldl, execS, ret, rows, S₀]
  rw [e1, e2] at h'
  have h'' : List.Perm [10] [10, 11] := h'
  have := h''.length_eq
  simp at this

/-- **`RunSpec` at the driver boundary.** `ρex` keeps barriers inside their turn, and for the `dims` turn the
order in which its writes are served is the swap of the two bundles, a valid run. -/
theorem runSpec_driver : RunSpec (L := driverLevel ret reads) cls (drvE E₁) driverView run₁ ρex where
  readId := fun n s h c => by cases n <;> simp [ρex, h]
  range := by
    intro j hj1 hjN hne c hlo hhi
    rcases eight j hj1 hjN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact ⟨hlo, hhi⟩
    · exact ⟨hlo, hhi⟩
    · exact (hne rfl).elim
    · have hc4 : c < 4 := hhi
      have hs : swapRun c < 4 := by unfold swapRun; split <;> omega
      exact ⟨Nat.zero_le _, hs⟩
  cert := by
    intro j hj1 hjN hne
    rcases eight j hj1 hjN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact RunCert.of_id _ _ (fun u => by
        rw [ρex_nodims (run₁.node 5) (run₁.stmt 5) (by decide)]; exact Nat.add_sub_cancel_left _ _)
    · exact RunCert.of_id _ _ (fun u => by
        rw [ρex_nodims (run₁.node 6) (run₁.stmt 6) (by decide)]; exact Nat.add_sub_cancel_left _ _)
    · exact (hne rfl).elim
    · exact ⟨[bundleD 1, bundleD 2], [bundleD 2, bundleD 1], rfl, rfl,
        BlockPerm.swap (L := driverLevel ret reads) [] [] (bundleD 1) (bundleD 2)
          bundles_commute_driver⟩

/-- **`RunSpec` at the adapter boundary.** -/
theorem runSpec_adapter : RunSpec (L := Asem.level) cls (alphaComp (Query := Query) Asem E₁)
    adapterView run₁ ρex where
  readId := fun n s h c => by cases n <;> simp [ρex, h]
  range := by
    intro j hj1 hjN hne c hlo hhi
    rcases eight j hj1 hjN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact ⟨hlo, hhi⟩
    · exact ⟨hlo, hhi⟩
    · exact (hne rfl).elim
    · have hc4 : c < 4 := hhi
      have hs : swapRun c < 4 := by unfold swapRun; split <;> omega
      exact ⟨Nat.zero_le _, hs⟩
  cert := by
    intro j hj1 hjN hne
    rcases eight j hj1 hjN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact (hne rfl).elim
    · exact RunCert.of_id _ _ (fun u => by
        rw [ρex_nodims (run₁.node 5) (run₁.stmt 5) (by decide)]; exact Nat.add_sub_cancel_left _ _)
    · exact RunCert.of_id _ _ (fun u => by
        rw [ρex_nodims (run₁.node 6) (run₁.stmt 6) (by decide)]; exact Nat.add_sub_cancel_left _ _)
    · exact (hne rfl).elim
    · exact ⟨[bundleCalls 1, bundleCalls 2], [bundleCalls 2, bundleCalls 1], rfl, rfl,
        BlockPerm.swap (L := Asem.level) [] [] (bundleCalls 1) (bundleCalls 2)
          bundles_commute_adapter⟩

/-! ## The headline theorems, instantiated -/

/-- **`T2₂` on the example** (adapter→driver recording): the two dbt versions, run on two schedules,
end in equivalent states and report equivalent observations. -/
theorem main_T2_2 :
    StateEquiv (SFinal run₁) (SFinal run₂) ∧ Module2.ObsEquiv run₁ run₂ ∧
      Module2.BehEquiv run₁ run₂ :=
  Formalization.Module5.T2_2 (reads := reads) readsSound compiledReadsSound₁
    compiledReadsSound₂ retCongruent targetPreserving run₁ run₂ targetFaithful₁
    targetFaithful₂ uniqueWriter dag₁ dag₂ staticAcyclic nti
    (adapterView := adapterView) (driverView := driverView) driverViewFaithful
    standIn_driver cls clsTruthful_driver sbc_driver ρex runSpec_driver hCS_driver

/-- **`T2₁` on the example** (core→adapter recording): the same conclusion from the adapter-call-level
recording, with the adapter semantics `Asem` linked to each run. -/
theorem main_T2_1 :
    StateEquiv (SFinal run₁) (SFinal run₂) ∧ Module2.ObsEquiv run₁ run₂ ∧
      Module2.BehEquiv run₁ run₂ :=
  Formalization.Module5.T2_1 (reads := reads) Asem asem_levelSoundT compiledReadsSoundL₁
    compiledReadsSoundL₂ run₁ run₂ runLink₁ runLink₂ targetFaithfulL₁ targetFaithfulL₂
    uniqueWriter dag₁ dag₂ staticAcyclic nti
    (adapterView := adapterView) (driverView := driverView) adapterViewFaithful
    standIn_adapter cls clsTruthful_adapter sbc_adapter ρex runSpec_adapter hCS_adapter

/-! ## The theorems are not vacuous

1. The conclusion is a genuine equivalence, not equality: the final states differ
   (`stg_orders` has its rows in a different order), though they are `~`-equivalent.
2. The two runs really are different schedules.
3. Reads really are reordered: the replayed history of `audit` differs from the recorded one — each
   of two reads is served by the other's recorded read — yet is equivalent to it.
4. Cross-node lookup is load-bearing: without it, replay of `staging`'s source-existence check, or of
   `report`'s row count, cannot converge at all.
5. The converters change the schema (`countOf_changes_schema`), and the two stand-ins are distinct
   (`standIns_distinct`).
6. Runs are load-bearing: with every write served from its own barrier (Modules 3–4), `dims`' recording
   cannot be replayed (`strict_replay_fails_dims_driver`, `strict_replay_fails_dims_adapter`), and the
   two engines' effect calls for the turn are not pointwise `≈` (`pointwise_write_agreement_fails`), so
   the T2 core's old hypothesis is false here. The permutation is a real reordering
   (`run_is_a_reordering`), the final states of the two runs differ at `dim`
   (`dim_states_differ`) yet are `~`-equivalent, and the swap is valid only because the bundles commute
   (`bundles_commute_*`) while the calls inside a bundle do not (`bundle_order_matters`). -/

theorem final₁ : SFinal run₁ = Sdim₁ := st₁_9
theorem final₂ : SFinal run₂ = Sdim₂ := st₂_9

theorem final_states_differ : SFinal run₁ ≠ SFinal run₂ := by
  intro h
  have h' := congrFun h .stg
  rw [final₁, final₂] at h'
  have e1 : Sdim₁ .stg = some [1, 2, 3] := rfl
  have e2 : Sdim₂ .stg = some [3, 2, 1] := rfl
  rw [e1, e2] at h'
  simp at h'

/-- The `dims` node ends up with the same rows in a different order. -/
theorem dim_states_differ : SFinal run₁ .dim ≠ SFinal run₂ .dim := by
  rw [final₁, final₂]
  have e1 : Sdim₁ .dim = some [10, 11, 20, 21] := rfl
  have e2 : Sdim₂ .dim = some [20, 21, 10, 11] := rfl
  rw [e1, e2]
  simp

theorem mart_agrees : SFinal run₁ .mart = SFinal run₂ .mart := by
  rw [final₁, final₂]; rfl

theorem schedules_differ : run₁.node ≠ run₂.node := by
  intro h
  have h' := congrFun h 1
  simp [run₁, run₂, node₁, node₂] at h'

/-- At the driver boundary, `audit`'s replay serves `sSel` and `sSelD` from each other's recorded read:
the replayed history is not the recorded one, but is `~` to it. -/
theorem audit_reorders :
    ∃ H : Hist, H ≠ Laudit ∧ HistEquiv H Laudit ∧
      ReplaySeg P .audit (fun s => (drvE E₂ s).map driverView)
        (MatchCallX cls CVEquiv
          (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView run₁ .audit)
          (fun s v r => XServe (L := driverLevel ret reads) (drvE E₁) driverView reads run₁
            AllowedD .audit s v r)) 3 H 0 := by
  refine ⟨[(sList, .rel [0]), (sSel, .rel [3, 2, 1]), (sSelD, .rel [1, 2, 3])], ?_, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun H : Hist => (H[1]?).map Prod.snd) h
    simp [Laudit] at h'
  · refine LForall₂.cons ⟨rfl, ResEquiv.refl _⟩ (LForall₂.cons ⟨rfl, ?_⟩
      (LForall₂.cons ⟨rfl, ?_⟩ LForall₂.nil))
    · show List.Perm [3, 2, 1] [1, 2, 3]; decide
    · show List.Perm [1, 2, 3] [3, 2, 1]; decide
  · exact replay_audit_swap (fun s => (drvE E₁ s).map driverView)
      (fun s => (drvE E₂ s).map driverView) _ _ (recordingOf run₁ .audit) rec_audit
      (driverView (.read .listRaw)) (driverView (.read (.sel .raw)))
      (driverView (.read (.selDesc .raw))) (driverView (.read .listRaw))
      (driverView (.read (.sel .raw))) (driverView (.read (.selDesc .raw)))
      rfl rfl rfl rfl rfl rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
      (crD .audit 2 0 (by decide) (by decide) rfl rfl) (crD .audit 3 0 (by decide) (by decide) rfl rfl)
      (crD .audit 4 0 (by decide) (by decide) rfl rfl)

/-- Without rule 3 (matcher with no second route), `staging`'s recorded history is *not* replayable
against the second dbt version at the driver boundary. -/
theorem rule3_necessary_driver :
    ¬ ConvergentReplaySeg cls P .staging (fun s => (drvE E₂ s).map driverView)
      (MatchCallX cls CVEquiv
        (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView run₁ .staging)
        (fun _ _ _ => False))
      (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView run₁ .staging)
      (recordingOf run₁ .staging) := by
  rw [rec_staging]
  exact rule3_necessary (fun s => (drvE E₁ s).map driverView) (fun s => (drvE E₂ s).map driverView)
    _ (driverView (.read (.probeIn Oraw))) (driverView (.read (.existsIn Oraw)))
    (driverView (.write .stg (.sel .raw))) rfl rfl rfl hno_driver rfl rfl rfl

/-- … and likewise at the adapter boundary. -/
theorem rule3_necessary_adapter :
    ¬ ConvergentReplaySeg cls P .staging (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
      (MatchCallX cls CVEquiv
        (recEvsOf (L := Asem.level) cls (alphaComp (Query := Query) Asem E₁) adapterView run₁ .staging)
        (fun _ _ _ => False))
      (recEvsOf (L := Asem.level) cls (alphaComp (Query := Query) Asem E₁) adapterView run₁ .staging)
      (recordingOf run₁ .staging) := by
  rw [rec_staging]
  exact rule3_necessary (fun s => (alphaComp (Query := Query) Asem E₁ s).map adapterView)
    (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
    _ (adapterView ⟨.probeRel, .set Oraw⟩) (adapterView ⟨.getRel, .set Oraw⟩)
    (adapterView ⟨.ctas, .tq .stg (.sel .raw)⟩) rfl rfl rfl hno_adapter rfl rfl rfl

/-- Without rule 3, `report`'s recorded history is not replayable either (driver boundary). -/
theorem rule3_necessary_report_driver :
    ¬ ConvergentReplaySeg cls P .report (fun s => (drvE E₂ s).map driverView)
      (MatchCallX cls CVEquiv
        (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView run₁ .report)
        (fun _ _ _ => False))
      (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView run₁ .report)
      (recordingOf run₁ .report) := by
  rw [rec_report]
  exact rule3_necessary_report (fun s => (drvE E₁ s).map driverView)
    (fun s => (drvE E₂ s).map driverView) _ (driverView (.read (.cnt .raw)))
    (driverView (.read (.rowCount .raw))) rfl rfl hno_report_driver rfl

/-- … and at the adapter boundary. -/
theorem rule3_necessary_report_adapter :
    ¬ ConvergentReplaySeg cls P .report (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
      (MatchCallX cls CVEquiv
        (recEvsOf (L := Asem.level) cls (alphaComp (Query := Query) Asem E₁) adapterView run₁ .report)
        (fun _ _ _ => False))
      (recEvsOf (L := Asem.level) cls (alphaComp (Query := Query) Asem E₁) adapterView run₁ .report)
      (recordingOf run₁ .report) := by
  rw [rec_report]
  exact rule3_necessary_report (fun s => (alphaComp (Query := Query) Asem E₁ s).map adapterView)
    (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView) _
    (adapterView ⟨.runQuery, .q (.cnt .raw)⟩) (adapterView ⟨.countRel, .q (.rowCount .raw)⟩) rfl rfl
    hno_report_adapter rfl

/-- The two stand-ins return *different schemas*: the wide answer `audit` recorded is a three-row
relation, and the converter turns it into the one-row relation `report` asked for. The converter is
not the identity, and not a slice of the input. -/
theorem countOf_changes_schema : countOf [1, 2, 3] = [3] ∧ countOf [1, 2, 3] ≠ [1, 2, 3] := by
  refine ⟨rfl, ?_⟩
  intro h; simp [countOf] at h

/-- Both stand-in pairs are really in use in `Allowed`: the slicing family serves `staging`, the
count pair serves `report`, and the two pairs do not overlap. -/
theorem standIns_distinct (O : Tbl → Prop) (h : Rel → Rel) :
    ¬ (AllowedD (.read .listRaw) (.read (.rowCount .raw)) h) ∧
    ¬ (AllowedD (.read (.sel .raw)) (.read (.existsIn O)) h) := by
  constructor
  · rintro (⟨O', -, h2, -⟩ | ⟨h1, -, -⟩)
    · cases h2
    · cases h1
  · rintro (⟨O', h1, -, -⟩ | ⟨-, h2, -⟩)
    · cases h1
    · cases h2

/-- Without runs, `dims`' recorded history is not replayable against the second dbt version
(driver boundary): this is why Module 5 is needed. -/
theorem strict_replay_fails_dims_driver :
    ¬ ConvergentReplaySeg cls P .dims (fun s => (drvE E₂ s).map driverView)
      (MatchCallXR cls CVEquiv
        (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView run₁ .dims)
        (fun _ _ _ => False) (fun _ c => c))
      (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView run₁ .dims)
      (recordingOf run₁ .dims) := by
  rw [rec_dims]
  refine strict_dims (fun s => (drvE E₁ s).map driverView) (fun s => (drvE E₂ s).map driverView)
    _ (fun _ _ _ => False) (driverView (.write .dim (.addSchema 1))) (driverView (.write .dim (.addView 1)))
    (driverView (.write .dim (.addSchema 2))) (driverView (.write .dim (.addView 2)))
    (driverView (.read .dimCount)) (driverView (.write .dim (.addSchema 2)))
    (driverView (.write .dim (.addView 2))) (driverView (.write .dim (.addSchema 1)))
    (driverView (.write .dim (.addView 1))) (driverView (.read .dimCount)) rfl rfl ?_ rfl rfl rfl rfl
    rfl
  intro hm
  have h : Args.tq .dim (Query.addSchema 2) = Args.tq .dim (Query.addSchema 1) := hm.2
  simp at h

/-- … and at the adapter boundary. -/
theorem strict_replay_fails_dims_adapter :
    ¬ ConvergentReplaySeg cls P .dims
      (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
      (MatchCallXR cls CVEquiv
        (recEvsOf (L := Asem.level) cls (alphaComp (Query := Query) Asem E₁) adapterView run₁ .dims)
        (fun _ _ _ => False) (fun _ c => c))
      (recEvsOf (L := Asem.level) cls (alphaComp (Query := Query) Asem E₁) adapterView run₁ .dims)
      (recordingOf run₁ .dims) := by
  rw [rec_dims]
  refine strict_dims (fun s => (alphaComp (Query := Query) Asem E₁ s).map adapterView)
    (fun s => (alphaComp (Query := Query) Asem E₂ s).map adapterView)
    _ (fun _ _ _ => False) (adapterView ⟨.ctas, .tq .dim (.addSchema 1)⟩)
    (adapterView ⟨.ctas, .tq .dim (.addView 1)⟩) (adapterView ⟨.ctas, .tq .dim (.addSchema 2)⟩)
    (adapterView ⟨.ctas, .tq .dim (.addView 2)⟩) (adapterView ⟨.runQuery, .q .dimCount⟩)
    (adapterView ⟨.ctas, .tq .dim (.addSchema 2)⟩) (adapterView ⟨.ctas, .tq .dim (.addView 2)⟩)
    (adapterView ⟨.ctas, .tq .dim (.addSchema 1)⟩) (adapterView ⟨.ctas, .tq .dim (.addView 1)⟩)
    (adapterView ⟨.runQuery, .q .dimCount⟩) rfl rfl ?_ rfl rfl rfl rfl rfl
  intro hm
  have h : Args.tq .dim (Query.addSchema 2) = Args.tq .dim (Query.addSchema 1) := hm.2
  simp at h

/-- **Module 3–4's hypothesis on write turns is false here.** The two engines' effect calls for the
`dims` turn are not pointwise `≈` (the bundles come in opposite orders); Module 5's `WriteAgree`, derived
from the run, is what the T2 core uses instead. -/
theorem pointwise_write_agreement_fails :
    ¬ LForall₂ (· ≈ ·) (effCalls (driverLevel ret reads) (drvE E₁ sBuild))
      (effCalls (driverLevel ret reads) (drvE E₂ sBuild)) := by
  intro h
  have e1 : effCalls (driverLevel ret reads) (drvE E₁ sBuild) =
      [.write .dim (.addSchema 1), .write .dim (.addView 1), .write .dim (.addSchema 2),
        .write .dim (.addView 2)] := rfl
  have e2 : effCalls (driverLevel ret reads) (drvE E₂ sBuild) =
      [.write .dim (.addSchema 2), .write .dim (.addView 2), .write .dim (.addSchema 1),
        .write .dim (.addView 1)] := rfl
  rw [e1, e2] at h
  cases h with
  | cons hab _ =>
    have hk : key (.write .dim (.addSchema 1)) = key (.write .dim (.addSchema 2)) := hab
    simp [key, normQ] at hk

/-- The run is a real reordering: the replay serves the live writes from the barriers `2, 3, 0, 1`. -/
theorem run_is_a_reordering :
    (ρex .dims sBuild 0, ρex .dims sBuild 1, ρex .dims sBuild 2, ρex .dims sBuild 3) = (2, 3, 0, 1) :=
  rfl

end Example
end Formalization
