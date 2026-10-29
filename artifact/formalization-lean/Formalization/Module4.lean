/-
Module 4: cross-node lookup (D16 rule 3), **matched call by call**.

Module 3 serves a live read call from a recorded read of the *same node's* current segment. Module 4
adds the second relaxation: when a live read call cannot be served locally, the engine may search
*other nodes'* recordings for a call whose answer covers what is needed, and serve a projection of it.

**The stand-in, at the call level.** `StandIn L cw cn h` is stated over two arbitrary calls of a boundary
`L` (`Level`): a *wide* call `cw`, a *narrow* call `cn`, and a converter `h` between their answers. It says
that at *every* state, converting the wide answer reproduces the narrow answer
(`(ans S cw).map h ≈ ans S cn`), and that `h` respects `~_R`. A boundary has a single answer type
`Relation`, so the two calls' answers may be relations of different schemas, and `h` is the adapter between
them. The triple is a property of the boundary, not of any engine or run, and the same definitions serve
both boundaries: at `driverLevel` the calls are `Statement.read`s, at an adapter level they are
`AdapterCall`s such as `list_relations` (wide) and `get_relation` (narrow). `StandInSet L Allowed` says
every triple in the set `Allowed` is a valid stand-in, so a run may use many pairs at once.

`XServe` is D16's rule 3, for **one live call**: node `n`'s statement `stmt` issues a read call whose view is
that of an allowed narrow call `cn`, and the wide call `cw` of that allowed triple was recorded at the final
call of some *other* node's read turn `t'`; the served value is `h` of that recorded wide answer. The footprint
of the lookup is `cn`'s own declared reads. The side condition that no write by `n` or by `t'`'s node falls
between the two positions keeps the answer from being read at a state a write has since invalidated.
`xServe_hX` shows that when the *last* call of a read turn is served this way, the served value is
`~_Res` to the value a second live run computes — which is how `T2₂`/`T2₁` consume it. `xServe_sound` shows
that if the recording engine issued the same narrow call, the served value is `~_Res` to `R₁`'s own result.

The matcher `MatchCallX` is Module 3's `MatchCall` with rule 3 as a *fallback* for reads, tried only
once the local segment has no candidate. Replay, convergence and the extraction lemmas are Module 3's,
instantiated at this matcher (`ReplayWith`, `replay_hAWrite_with`, `replay_hReadRes_with`).

**History (the only place this file narrates it).** An earlier design fixed one wide call `f` and a
narrow family `g O` indexed by a target set `O` (`CrossNodeStandIn`, with a side condition
`GFamilyReads`); it is the special case `cw = f`, `cn = g O`, `h := h O` of the above. An earlier
design still stated the wide/narrow relation
over `AdapterCall`-level `fqns` predicates, which was unsatisfiable (one `list_relations` call serving
two tables' existence checks forced one `fqns` value to equal two sets at once). A
`FqnsSound`-shaped axiom relating two recorded results directly (`WideSliceSound`) was also tried and
found unsatisfiable for any genuine slicing: instantiating `i₁ = i₂` forces `h O r ≈ r` for every
recorded answer. `t2_2_scratch.lean` shows `T2₂` is simply false if rule 3 is left as an unconstrained
predicate, which is why `XServe` carries real content.
-/

import Formalization.Module3

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Formalization
namespace Module4

open Formalization.Module1 hiding BehEquiv T2_1 T2_2 ReadsSound
open Formalization.Module1.Eqv hiding ObsEquiv BehEquiv
open Formalization.Module2 hiding T2_1 T2_2
open Formalization.Module3 hiding T2_1 T2_2

/-! ## Cross-node stand-in (ground truth), at any boundary -/

/-- **`StandIn`.** The wide call `cw` is a valid stand-in for the narrow call `cn`, via the converter `h`:
at every state, converting `cw`'s answer with `h` reproduces `cn`'s answer, and `h` respects `~_R`. The
two calls are arbitrary calls of the boundary `L`, and `h` is an adapter between their answers; since a
boundary has one answer type `Relation`, the two answers may be relations of different schemas. -/
structure StandIn {FQN Relation : Type} [Setoid Relation] (L : Level FQN Relation)
    (cw cn : L.Call) (h : Relation → Relation) : Prop where
  slice : ∀ S : State FQN Relation, OptEquiv ((L.ans S cw).map h) (L.ans S cn)
  congr : ∀ x y : Relation, x ≈ y → h x ≈ h y

/-- A set of stand-in triples `(cw, cn, h)` all of whose members are valid. -/
abbrev StandInSet {FQN Relation : Type} [Setoid Relation] (L : Level FQN Relation)
    (Allowed : L.Call → L.Call → (Relation → Relation) → Prop) : Prop :=
  ∀ cw cn h, Allowed cw cn h → StandIn L cw cn h

/-- **D16 rule 3 (cross-node serving), for one live call.** `stmt` is a live `Read` turn of node `n`,
and the live call being served has the view of a narrow call `cn` whose declared reads (`O := L.reads cn`)
`stmt` genuinely depends on. `t'` is the raw position of some *other* node's `Read` turn whose own
compilation ends in a wide call `cw`, where `(cw, cn, h)` is an `Allowed` stand-in. The served value is
`h (R₁.res t')`.

**The no-intervening-write side condition.** Node `n` running the classic "check exists, then create"
idiom reads `o`'s existence at turn `j'` and writes `o` at a *later* turn of its own. `DAGOrder` exempts
same-node reader/writer pairs (needed for that idiom to be satisfiable at all), so nothing stops another
node's turn `t'`, whose wide answer covers `o`, from sitting strictly *between* `j'` and `n`'s own later
write; serving `j'` from `t'` would then answer with `o`'s state *after* that write. The same risk exists
for `t'`'s own node writing `o` between the two positions. Third-party writers are never a problem:
`DAGOrder`'s cross-node clause already orders them before both `j'` and `t'` whenever either reads the
written FQN. So a legitimate serve requires that no write by `n` or by `t'`'s node lands between (any
occurrence of) `stmt` at `n` and `t'`. -/
def XServe {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] {L : Level FQN Relation}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (comp₁ : Comp FQN Query Relation L) (view : L.Call → CallView MethodName Args)
    (reads : Statement FQN Query → FQN → Prop)
    (R₁ : LiveRun P E₁ ret S₀)
    (Allowed : L.Call → L.Call → (Relation → Relation) → Prop)
    (n : Nodes) (stmt : Statement FQN Query) (v : CallView MethodName Args)
    (r : Result Relation) : Prop :=
  ∃ (cw cn : L.Call) (h : Relation → Relation) (t' : Nat) (r' : Relation),
    Allowed cw cn h ∧ v = view cn ∧
    (∀ o, L.reads cn o → reads stmt o) ∧
    1 ≤ t' ∧ t' ≤ R₁.N ∧ R₁.node t' ≠ n ∧
    (∃ q', R₁.stmt t' = Statement.read q') ∧
    (∀ o, L.reads cn o → reads (R₁.stmt t') o) ∧
    (comp₁ (R₁.stmt t')).getLast? = some cw ∧
    (∀ q p o, 1 ≤ q → q ≤ R₁.N → R₁.node q = n → R₁.stmt q = stmt →
      (R₁.node p = n ∨ R₁.node p = R₁.node t') →
      ((q ≤ p ∧ p < t') ∨ (t' ≤ p ∧ p < q)) →
      target (R₁.stmt p) = some o → ¬ L.reads cn o) ∧
    R₁.res t' = Result.rel r' ∧
    r = Result.rel (h r')

/-- The within-`R₁` state agreement `XServe`'s witness data licenses: `t'`'s state agrees with `j'`'s
on every FQN of `O`. Uses only the no-intervening-write side condition and `R₁`'s own `DAGOrder`. -/
theorem xServe_stateAgree {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] {L : Level FQN Relation}
    {comp₁ : Comp FQN Query Relation L}
    {reads : Statement FQN Query → FQN → Prop}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (hLP : LevelPreserve L) (hTF1 : TargetFaithfulL comp₁)
    (hDAG : DAGOrder reads R₁)
    (n : Nodes) (j' t' : Nat) (hj'1 : 1 ≤ j') (hj'N : j' ≤ R₁.N) (hj'node : R₁.node j' = n)
    (ht'1 : 1 ≤ t') (ht'N : t' ≤ R₁.N)
    (O : FQN → Prop) (hOreads : ∀ o, O o → reads (R₁.stmt j') o)
    (hOreads' : ∀ o, O o → reads (R₁.stmt t') o)
    (hnointer : ∀ q p o, 1 ≤ q → q ≤ R₁.N → R₁.node q = n → R₁.stmt q = R₁.stmt j' →
      (R₁.node p = n ∨ R₁.node p = R₁.node t') →
      ((q ≤ p ∧ p < t') ∨ (t' ≤ p ∧ p < q)) →
      target (R₁.stmt p) = some o → ¬ O o) :
    ∀ o, O o →
      OptEquiv (stateAtL comp₁ R₁.stmt S₀ j' o) (stateAtL comp₁ R₁.stmt S₀ t' o) := by
  intro o ho
  rcases Nat.le_total j' t' with hle | hle
  · have hnw : ∀ p, j' ≤ p → p < t' → R₁.node p = R₁.node j' →
        target (R₁.stmt p) ≠ some o := by
      intro p hp1 hp2 hpnode heq
      rw [hj'node] at hpnode
      exact hnointer j' p o hj'1 hj'N hj'node rfl (Or.inl hpnode) (Or.inl ⟨hp1, hp2⟩) heq ho
    have := stateAt_agree_of_DAG R₁ hLP hTF1 hDAG hj'1 hj'N hle (by omega) o (hOreads o ho) hnw
    rw [this]; exact OptEquiv.refl _
  · have hnw : ∀ p, t' ≤ p → p < j' → R₁.node p = R₁.node t' →
        target (R₁.stmt p) ≠ some o := by
      intro p hp1 hp2 hpnode heq
      exact hnointer j' p o hj'1 hj'N hj'node rfl (Or.inr hpnode) (Or.inr ⟨hp1, hp2⟩) heq ho
    have := stateAt_agree_of_DAG R₁ hLP hTF1 hDAG ht'1 ht'N hle (by omega) o (hOreads' o ho) hnw
    rw [this]; exact OptEquiv.refl _

/-- The recorded wide answer at `t'`, in the boundary's own terms: the last call of `t'`'s compilation
is `f`, which answers `x ≈ r'` at `t'`'s state. -/
theorem xServe_wide {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] {L : Level FQN Relation}
    {comp₁ : Comp FQN Query Relation L}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (hLink : ResLink comp₁ R₁)
    {f : L.Call} (t' : Nat) (ht'1 : 1 ≤ t') (ht'N : t' ≤ R₁.N) (q' : Query)
    (hq' : R₁.stmt t' = Statement.read q') (r' : Relation)
    (hrt' : R₁.res t' = Result.rel r')
    (hf : (comp₁ (R₁.stmt t')).getLast? = some f) :
    ∃ x, L.ans (stateAtL comp₁ R₁.stmt S₀ t') f = some x ∧ x ≈ r' := by
  obtain ⟨rt, hrt, ert⟩ := hLink t' ht'1 ht'N
  rw [hq'] at hrt hf
  simp only [rL, hf, Option.map_eq_some_iff] at hrt
  obtain ⟨x, hx1, rfl⟩ := hrt
  rw [hrt'] at ert
  exact ⟨x, hx1, ert⟩

/-- The narrow call's answer at `j'`, in the boundary's own terms. -/
theorem xServe_narrow {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] {L : Level FQN Relation}
    {comp₁ : Comp FQN Query Relation L}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (hLink : ResLink comp₁ R₁)
    {c : L.Call} (j' : Nat) (hj'1 : 1 ≤ j') (hj'N : j' ≤ R₁.N) (qj' : Query)
    (hqj' : R₁.stmt j' = Statement.read qj')
    (hc : (comp₁ (R₁.stmt j')).getLast? = some c) :
    ∃ y, L.ans (stateAtL comp₁ R₁.stmt S₀ j') c = some y ∧
      ResEquiv (Result.rel y) (R₁.res j') := by
  obtain ⟨rj, hrj, erj⟩ := hLink j' hj'1 hj'N
  rw [hqj'] at hrj hc
  simp only [rL, hc, Option.map_eq_some_iff] at hrj
  obtain ⟨y, hy1, rfl⟩ := hrj
  exact ⟨y, hy1, erj⟩

/-- **Cross-node lookup is semantically sound.** When the recording engine issued the same narrow
call, whatever value `XServe` licenses serving for `R₁`'s own turn `j'` is `~_Res`-related to `R₁`'s own
recorded result at that turn. Chains `StandIn` (at `t'`'s own state) with `xServe_stateAgree` +
reads-soundness (bridging `t'`'s state to `j'`'s, within `R₁`). -/
theorem xServe_sound {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid Args]
    {L : Level FQN Relation} [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    {comp₁ : Comp FQN Query Relation L} {view : L.Call → CallView MethodName Args}
    {R₁ : LiveRun P E₁ ret S₀}
    (hL : LevelSoundT L) (hLink : ResLink comp₁ R₁)
    (hFaith : ∀ c c' : L.Call, CVEquiv (view c) (view c') → c ≈ c')
    (hTF1 : TargetFaithfulL comp₁) (hDAG : DAGOrder reads R₁)
    {Allowed : L.Call → L.Call → (Relation → Relation) → Prop}
    (hAllowed : StandInSet L Allowed)
    (n : Nodes) (j' : Nat) (hj'1 : 1 ≤ j') (hj'N : j' ≤ R₁.N) (hj'node : R₁.node j' = n)
    (qj' : Query) (hqj' : R₁.stmt j' = Statement.read qj')
    {c₁ : L.Call} (hc₁ : (comp₁ (R₁.stmt j')).getLast? = some c₁)
    (r : Result Relation)
    (hx : XServe comp₁ view reads R₁ Allowed n (R₁.stmt j') (view c₁) r) :
    ResEquiv r (R₁.res j') := by
  obtain ⟨cw, cn, h, t', r', hAl, hv, hOreads, ht'1, ht'N, ht'node, ⟨q', hq'eq⟩, hOreads', hqE1,
    hnointer, hrt', hrserve⟩ := hx
  have hCNS := hAllowed cw cn h hAl
  have hbg : c₁ ≈ cn := hFaith c₁ cn (by rw [hv]; exact ⟨rfl, Setoid.refl _⟩)
  have hSt := xServe_stateAgree R₁ hL.preserve hTF1 hDAG n j' t' hj'1 hj'N hj'node ht'1 ht'N
    (L.reads cn) hOreads hOreads' hnointer
  obtain ⟨x, hx1, hxr⟩ := xServe_wide R₁ hLink t' ht'1 ht'N q' hq'eq r' hrt' hqE1
  obtain ⟨y, hy1, erj⟩ := xServe_narrow R₁ hLink j' hj'1 hj'N qj' hqj' hc₁
  have hslice := hCNS.slice (stateAtL comp₁ R₁.stmt S₀ t')
  rw [hx1] at hslice
  simp only [Option.map_some] at hslice
  have hmid : OptEquiv (L.ans (stateAtL comp₁ R₁.stmt S₀ t') cn)
      (L.ans (stateAtL comp₁ R₁.stmt S₀ j') cn) :=
    hL.ans_sound cn _ _ (fun o ho => OptEquiv.symm (hSt o ho))
  have hcong : OptEquiv (L.ans (stateAtL comp₁ R₁.stmt S₀ j') cn)
      (L.ans (stateAtL comp₁ R₁.stmt S₀ j') c₁) :=
    OptEquiv.symm (hL.ans_congr c₁ cn hbg _)
  have hchain := OptEquiv.trans hslice (OptEquiv.trans hmid hcong)
  rw [hy1] at hchain
  rw [hrserve]
  exact ResEquiv.trans
    (show ResEquiv (Result.rel (h r')) (Result.rel (h x)) from
      Setoid.symm (hCNS.congr x r' hxr))
    (ResEquiv.trans (show ResEquiv (Result.rel (h x)) (Result.rel y) from hchain) erj)

/-- **Cross-node read agreement for a last call, feeding `T2₂`/`T2₁` directly.** Where Module 3's
`crossReadAgree` bridges two recorded calls of the *same node's segment*, this bridges a cross-node
*wide* call (within `R₁`'s own recording) to a genuinely different *live* run's own narrow value:
`StandIn` at `R₁`'s state at `t'`, then reads-soundness across to the live run, twice (`t'` to
`j'` within `R₁`, then `R₁` at `j'` to the live run via `hSagree`). Both applications are over `cn`'s own
reads. -/
theorem xServe_hX {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid Args]
    {L : Level FQN Relation} [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    {comp₁ : Comp FQN Query Relation L} {view : L.Call → CallView MethodName Args}
    {R₁ : LiveRun P E₁ ret S₀}
    (hL : LevelSoundT L) (hLink : ResLink comp₁ R₁)
    (hFaith : ∀ c c' : L.Call, CVEquiv (view c) (view c') → c ≈ c')
    (hTF1 : TargetFaithfulL comp₁) (hDAG : DAGOrder reads R₁)
    {Allowed : L.Call → L.Call → (Relation → Relation) → Prop}
    (hAllowed : StandInSet L Allowed)
    (j : Nat) (S₂ : State FQN Relation) (b : L.Call) (yb : Relation) (r' : Result Relation)
    (hj1 : 1 ≤ j) (hjN : j ≤ R₁.N)
    (hSagree : ∀ o, reads (R₁.stmt j) o →
      OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o) (S₂ o))
    (hyb : L.ans S₂ b = some yb) (hconv : ResEquiv r' (R₁.res j))
    (hx : XServe comp₁ view reads R₁ Allowed (R₁.node j) (R₁.stmt j) (view b) r') :
    ResEquiv (R₁.res j) (Result.rel yb) := by
  obtain ⟨cw, cn, h, t', r'', hAl, hv, hOreads, ht'1, ht'N, ht'node, ⟨q', hq'eq⟩, hOreads', hqE1,
    hnointer, hrt', hrserve⟩ := hx
  have hCNS := hAllowed cw cn h hAl
  have hbg : b ≈ cn := hFaith b cn (by rw [hv]; exact ⟨rfl, Setoid.refl _⟩)
  have hSt := xServe_stateAgree R₁ hL.preserve hTF1 hDAG (R₁.node j) j t' hj1 hjN rfl ht'1 ht'N
    (L.reads cn) hOreads hOreads' hnointer
  obtain ⟨x, hx1, hxr⟩ := xServe_wide R₁ hLink t' ht'1 ht'N q' hq'eq r'' hrt' hqE1
  have hslice := hCNS.slice (stateAtL comp₁ R₁.stmt S₀ t')
  rw [hx1] at hslice
  simp only [Option.map_some] at hslice
  have hmid : OptEquiv (L.ans (stateAtL comp₁ R₁.stmt S₀ t') cn)
      (L.ans (stateAtL comp₁ R₁.stmt S₀ j) cn) :=
    hL.ans_sound cn _ _ (fun o ho => OptEquiv.symm (hSt o ho))
  have hfar : OptEquiv (L.ans (stateAtL comp₁ R₁.stmt S₀ j) cn) (L.ans S₂ cn) :=
    hL.ans_sound cn _ _ (fun o ho => hSagree o (hOreads o ho))
  have hcong : OptEquiv (L.ans S₂ cn) (L.ans S₂ b) :=
    OptEquiv.symm (hL.ans_congr b cn hbg S₂)
  have hchain := OptEquiv.trans hslice (OptEquiv.trans hmid (OptEquiv.trans hfar hcong))
  rw [hyb] at hchain
  rw [hrserve] at hconv
  exact ResEquiv.trans (ResEquiv.symm hconv)
    (ResEquiv.trans
      (show ResEquiv (Result.rel (h r'')) (Result.rel (h x)) from
        Setoid.symm (hCNS.congr x r'' hxr))
      (show ResEquiv (Result.rel (h x)) (Result.rel yb) from hchain))

/-! ## D16 with rule 3: the call matcher -/

section Matcher

variable {FQN Query Relation MethodName Args : Type}

/-- **The call matcher with rule 3.** Module 3's `MatchCall`, whose `Read` clause gains rule 3 as a
*fallback*, tried only once the local segment has no candidate at all. -/
def MatchCallX (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop)
    (XS : Statement FQN Query → CallView MethodName Args → Result Relation → Prop)
    (stmt : Statement FQN Query) (c : Nat) (v : CallView MethodName Args)
    (r : Result Relation) (c' : Nat) : Prop :=
  (isW cls v = true → ∃ e, F e ∧ isW cls e.view = true ∧ e.seg = c ∧ m v e.view ∧
      r = e.res ∧ c' = c + 1) ∧
  (isW cls v = false →
    (∃ e, F e ∧ isW cls e.view = false ∧ e.seg = c ∧ m v e.view ∧ r = e.res ∧ c' = c) ∨
    ((¬ ∃ e, F e ∧ isW cls e.view = false ∧ e.seg = c ∧ m v e.view) ∧ XS stmt v r ∧ c' = c))

theorem MatchCallX.spec (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop)
    (XS : Statement FQN Query → CallView MethodName Args → Result Relation → Prop)
    (stmt : Statement FQN Query) :
    MatcherSpec cls m F (MatchCallX cls m F XS stmt) where
  write := fun c v r c' h hw => h.1 hw
  read := fun c v r c' h hw => by
    rcases h.2 hw with ⟨-, -, -, -, -, -, hc'⟩ | ⟨-, -, hc'⟩ <;> exact hc'

end Matcher

/-- The replay of Module 4: the matcher is `MatchCallX`, with rule 3 given by `XServe` over the
`Allowed` stand-in triples. -/
abbrev ReplayOKX {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid Args]
    {L : Level FQN Relation} (cls : MethodName → Cls)
    (comp₁ comp₂ : Comp FQN Query Relation L) (view : L.Call → CallView MethodName Args)
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (reads : Statement FQN Query → FQN → Prop)
    (R₁ : LiveRun P E₁ ret S₀)
    (Allowed : L.Call → L.Call → (Relation → Relation) → Prop) : Prop :=
  ReplayWith cls comp₁ comp₂ view R₁ (fun n stmt =>
    MatchCallX cls CVEquiv (recEvsOf cls comp₁ view R₁ n)
      (fun s v r => XServe comp₁ view reads R₁ Allowed n s v r) stmt)

/-! ### T2₂ / T2₁

`hAWrite` and `hReadRes` come from Module 3's extraction lemmas at the matcher `MatchCallX`. `hAWrite`
needs only the matcher's write branch. `hReadRes` has Module 3's local case, unchanged, and one more:
a last call served through rule 3, which `xServe_hX` closes via `StandIn` instead
of view-matching. `T2₂` runs it at the driver boundary and `T2₁` at an adapter boundary; the lemmas are
the same. -/

theorem T2_2 {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid Args]
    [Setoid (Statement FQN Query)]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (hRS : ReadsSound reads ret) (hCRS1 : CompiledReadsSound reads E₁)
    (hCRS2 : CompiledReadsSound reads E₂) (hRC : RetCongruent ret)
    (hTP : TargetPreserving FQN Query)
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hTF1 : TargetFaithful E₁) (hTF2 : TargetFaithful E₂)
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P)) (hNTI : NextTildeInsensitive P)
    {adapterView : AdapterCall MethodName Args → CallView MethodName Args}
    {driverView : DriverCall FQN Query → CallView MethodName Args}
    (hDVF : DriverViewFaithful driverView)
    {Allowed : (driverLevel ret reads).Call → (driverLevel ret reads).Call →
      (Relation → Relation) → Prop}
    (hAllowed : StandInSet (driverLevel ret reads) Allowed)
    (cls : MethodName → Cls) (hCT : ClsTruthful (driverLevel ret reads) cls driverView)
    (hSBC : SameBarrierCount cls (callsB E₂ adapterView driverView Boundary.adapterDriver)
      (callsB E₁ adapterView driverView Boundary.adapterDriver) R₁.N R₁.stmt)
    (hCS : ReplayOKX (L := driverLevel ret reads) cls (drvE E₁) (drvE E₂) driverView reads R₁
      Allowed) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have hLT := driverLevel_soundT hRS hRC hTP
  have hCRS1L := driverLevel_compiledReadsSound (ret := ret) hCRS1
  have hCRS2L := driverLevel_compiledReadsSound (ret := ret) hCRS2
  have hTF1L := driverLevel_targetFaithful (ret := ret) (reads := reads) hTF1
  have hLink : ResLink (L := driverLevel ret reads) (drvE E₁) R₁ := resLink_driver R₁
  have hspec : ∀ n s, MatcherSpec cls CVEquiv
      (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView R₁ n)
      (MatchCallX cls CVEquiv (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView R₁ n)
        (fun s v r => XServe (L := driverLevel ret reads) (drvE E₁) driverView reads R₁ Allowed n s v
          r) s) :=
    fun n s => MatchCallX.spec cls CVEquiv _ _ s
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      LForall₂ (· ≈ ·) (effCalls (driverLevel ret reads) (drvE E₁ (R₁.stmt j)))
        (effCalls (driverLevel ret reads) (drvE E₂ (R₁.stmt j))) :=
    fun j hj1 hjN _ => replay_hAWrite_with (L := driverLevel ret reads) hLT hCT hDVF R₁ hNTI
      hspec hSBC hCS j hj1 hjN
  have hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAt R₁.stmt ret E₁ S₀ j o') (stateAt R₂.stmt ret E₂ S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i) := by
    intro j i hj1 hjN hi1 hiN hstmt_eq hw hSagree
    have h2 : rL (L := driverLevel ret reads) (drvE E₂) (stateAt R₂.stmt ret E₂ S₀ i)
        (R₁.stmt j) = some (R₂.res i) := by
      have := R₂.res_eq i hi1 hiN
      rw [← hstmt_eq] at this
      exact (rL_driver ret reads E₂ _ _).trans this
    exact replay_hReadRes_with (L := driverLevel ret reads)
      (fun n s _ v r _ => XServe (drvE E₁) driverView reads R₁ Allowed n s v r)
      hLT hCRS1L hCRS2L hCT hDVF R₁ hTF1L hDAG1 hLink hNTI
      (fun n s c v r c' h => (hspec n s).counts c v r c' h) (fun n s _ => hspec n s)
      (fun n s c v r c' hm hw => by
        rcases (hm.2 hw) with ⟨e, hF, hew, hseg, hmv, hr, -⟩ | ⟨-, hx, -⟩
        · exact Or.inl ⟨e, hF, hew, hseg, hmv, hr⟩
        · exact Or.inr hx)
      hSBC hCS
      (fun j S₂ b yb r' c₀ c' hj1 hjN hw' hSag hlast hyb hconv hx =>
        xServe_hX hLT hLink hDVF hTF1L hDAG1 hAllowed j S₂ b yb r' hj1 hjN hSag hyb hconv hx)
      j (stateAt R₂.stmt ret E₂ S₀ i) (R₂.res i) hj1 hjN hw hSagree h2
  exact T2_of_A hRS hCRS1 hRC hTP R₁ R₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI hAWrite hReadRes

theorem T2_1 {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid Args]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (A : AdapterSem FQN Relation MethodName Args) (hAs : LevelSoundT A.level)
    (hCRS1 : CompiledReadsSoundL reads (alphaComp (Query := Query) A E₁))
    (hCRS2 : CompiledReadsSoundL reads (alphaComp (Query := Query) A E₂))
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hk₁ : RunLinkT A R₁) (hk₂ : RunLinkT A R₂)
    (hTF1 : TargetFaithfulL (alphaComp (Query := Query) A E₁))
    (hTF2 : TargetFaithfulL (alphaComp (Query := Query) A E₂))
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P)) (hNTI : NextTildeInsensitive P)
    {adapterView : AdapterCall MethodName Args → CallView MethodName Args}
    {driverView : DriverCall FQN Query → CallView MethodName Args}
    (hAVF : AdapterViewFaithful adapterView)
    {Allowed : A.level.Call → A.level.Call → (Relation → Relation) → Prop}
    (hAllowed : StandInSet A.level Allowed)
    (cls : MethodName → Cls) (hCT : ClsTruthful A.level cls adapterView)
    (hSBC : SameBarrierCount cls (callsB E₂ adapterView driverView Boundary.coreAdapter)
      (callsB E₁ adapterView driverView Boundary.coreAdapter) R₁.N R₁.stmt)
    (hCS : ReplayOKX (L := A.level) cls (alphaComp (Query := Query) A E₁)
      (alphaComp (Query := Query) A E₂) adapterView reads R₁ Allowed) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have hFaith : ∀ a b : A.level.Call, CVEquiv (adapterView a) (adapterView b) → a ≈ b :=
    fun a b h => hAVF a b h
  have hspec : ∀ n s, MatcherSpec cls CVEquiv
      (recEvsOf (L := A.level) cls (alphaComp (Query := Query) A E₁) adapterView R₁ n)
      (MatchCallX cls CVEquiv
        (recEvsOf (L := A.level) cls (alphaComp (Query := Query) A E₁) adapterView R₁ n)
        (fun s v r => XServe (L := A.level) (alphaComp (Query := Query) A E₁) adapterView reads R₁
          Allowed n s v r)
        s) :=
    fun n s => MatchCallX.spec cls CVEquiv _ _ s
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      LForall₂ (· ≈ ·) (effCalls A.level (alphaComp (Query := Query) A E₁ (R₁.stmt j)))
        (effCalls A.level (alphaComp (Query := Query) A E₂ (R₁.stmt j))) :=
    fun j hj1 hjN _ => replay_hAWrite_with (L := A.level) hAs hCT hFaith R₁ hNTI hspec hSBC hCS
      j hj1 hjN
  have hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL (alphaComp (Query := Query) A E₁) R₁.stmt S₀ j o')
          (stateAtL (alphaComp (Query := Query) A E₂) R₂.stmt S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i) := by
    intro j i hj1 hjN hi1 hiN hstmt_eq hw hSagree
    obtain ⟨r₂, h2, e2⟩ := hk₂.res_link i hi1 hiN
    rw [← hstmt_eq] at h2
    exact ResEquiv.trans
      (replay_hReadRes_with (L := A.level)
        (fun n s _ v r _ =>
          XServe (alphaComp (Query := Query) A E₁) adapterView reads R₁ Allowed n s v r)
        hAs hCRS1 hCRS2 hCT hFaith R₁ hTF1 hDAG1 hk₁.res_link hNTI
        (fun n s c v r c' h => (hspec n s).counts c v r c' h) (fun n s _ => hspec n s)
        (fun n s c v r c' hm hw => by
          rcases (hm.2 hw) with ⟨e, hF, hew, hseg, hmv, hr, -⟩ | ⟨-, hx, -⟩
          · exact Or.inl ⟨e, hF, hew, hseg, hmv, hr⟩
          · exact Or.inr hx)
        hSBC hCS
        (fun j S₂ b yb r' c₀ c' hj1 hjN hw' hSag hlast hyb hconv hx =>
          xServe_hX hAs hk₁.res_link hFaith hTF1 hDAG1 hAllowed j S₂ b yb r' hj1 hjN hSag hyb
            hconv hx)
        j _ r₂ hj1 hjN hw hSagree h2) e2
  have h := Eqv.T2_adapter A hAs R₁ R₂ hk₁ hk₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI
    (fun j hj1 hjN hw => writeAgree_of_forall₂ hAs hCRS1 hTF1 _ (hAWrite j hj1 hjN hw)) hReadRes
  exact ⟨h.1, ⟨h.2.1, h.2.2⟩, h.1, ⟨h.2.1, h.2.2⟩⟩

end Module4
end Formalization
