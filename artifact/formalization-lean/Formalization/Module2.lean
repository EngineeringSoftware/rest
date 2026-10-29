/-
Module 2: normalization equivalence at the recording boundary.

Values (`Relation`, call arguments, driver statements) are compared up to
abstract equivalences `~_R`/`~_A`/`~_S`, assumed given as `Setoid`s, instead of
literally. The *argument* is not here: it is Module 1's equivalence-parametrized
core (`Module1.Eqv.T2_of_A`, `T2_adapter`), stated once for any boundary and
specialized to equality by Module 1 itself. What this module adds:

* the **driver boundary as a `Level`** (`driverCallSetoid`, `driverLevel_soundT`):
  the three driver-level hypotheses `ReadsSound`/`RetCongruent`/`TargetPreserving`
  make `driverLevel` a `LevelSoundT`, and `T2_of_A`/`stepAgreeT` are the facades
  Modules 3-4 call;
* the **normalized replay layer** (`ConvergentReplayT`/
  `PerTurnAlignedT`, `callsB_agree_of_alignedT`): replay matches call views up to
  `CVEquiv` instead of equality, and still reproduces the recording literally;
* `T2_2` (driver boundary) and `T2_1` (adapter boundary, through `AdapterSem` and
  `RunLinkT`, with no assumption relating the two engines' `δ`), which derive
  `(A~)` from the replay hypotheses plus view-faithfulness and hand the rest to
  the core.

One hypothesis is added that the paper-level statement does not make:
`NextTildeInsensitive` (Module 1's `Eqv`). It is *necessary*: two live runs'
histories now agree only up to `~_Res`, and a `next` that branches on the erased
noise makes T2 false.
-/

import Formalization.Module1

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Formalization
namespace Module2

open Formalization.Module1
open Formalization.Module1.Eqv hiding ObsEquiv BehEquiv

/-! ## D4 (AdapterCall) -/

/-- `AdapterCall ~_AC AC'  :≡  method = method' ∧ args ~_A args'`. -/
def ACEquiv {MethodName Args : Type} [Setoid Args]
    (c c' : AdapterCall MethodName Args) : Prop :=
  c.method = c'.method ∧ c.args ≈ c'.args

instance acSetoid {MethodName Args : Type} [Setoid Args] :
    Setoid (AdapterCall MethodName Args) where
  r := ACEquiv
  iseqv := ⟨fun _ => ⟨rfl, Setoid.refl _⟩, fun h => ⟨h.1.symm, Setoid.symm h.2⟩,
    fun h1 h2 => ⟨h1.1.trans h2.1, Setoid.trans h1.2 h2.2⟩⟩

instance adapterCallSetoid {FQN Relation MethodName Args : Type} [Setoid Args]
    (A : AdapterSem FQN Relation MethodName Args) : Setoid A.level.Call :=
  inferInstanceAs (Setoid (AdapterCall MethodName Args))

/-! ## D6 (Boundary & observable calls) -/

/-- `CallView ~_V CallView'  :≡  op = op' ∧ args ~_A args'` — `op` still
matches exactly ((R4~): "normalization doesn't change which operation was
invoked, only its payload"). -/
def CVEquiv {MethodName Args : Type} [Setoid Args]
    (c c' : CallView MethodName Args) : Prop :=
  c.op = c'.op ∧ c.args ≈ c'.args

/-! ## D8′ (Behavioral equivalence, relaxed)

`R₁ ≈ R₂ :≡ S_final(R₁) ~_St S_final(R₂) ∧ O(R₁) ~_O O(R₂)`, where
`O(R₁) ~_O O(R₂) :≡ ∀ n r, (n,r) ∈ O(R₁) ⟺ ∃ r', (n,r') ∈ O(R₂) ∧ r ~_Res r'`
and symmetrically. Literal `Behavior` equality (D8) is the special case
`~_R` = equality. -/

def ObsEquiv {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation} [Setoid Relation]
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀) : Prop :=
  (∀ n r, isObs R₁.node R₁.stmt R₁.res R₁.N n r →
      ∃ r', isObs R₂.node R₂.stmt R₂.res R₂.N n r' ∧ ResEquiv r r') ∧
  (∀ n r, isObs R₂.node R₂.stmt R₂.res R₂.N n r →
      ∃ r', isObs R₁.node R₁.stmt R₁.res R₁.N n r' ∧ ResEquiv r r')

def BehEquiv {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation} [Setoid Relation]
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀) : Prop :=
  StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂

/-! ## D9″ (Event-based replay & convergence, relaxed (R4~))

Replay is **call by call**, exactly as in Module 1: each live call is served the one recorded event at
the cursor, and a turn's result is the result served for its last call. The only relaxation is the
match test, (R4~): a recorded call and a live call match when they are `CVEquiv` — `op` exactly, `args`
up to `~_A` — instead of equal. Module 1's replay is already generic in that match relation
(`replayEvWith`, `ConvergentReplayWith`, `PerTurnAlignedWith`, `callsB_agree_of_aligned_with`), so this
module only instantiates it at `CVEquiv`. Since `~_A` is not assumed `Decidable`, the instantiation is
`noncomputable`, using `Classical.propDecidable`; nothing below relies on it being computable.

`ConvergentReplayT` still asserts the replay reproduces `recordingOf R₁ n` **literally**, entry for
entry — not merely up to `~` — even though the *acceptance test* for each call is (R4~). Every event
the replay ever serves is generated by `E₁` from `R₁`'s own literal history, and the served result at a
successful step is always that matched event's own literal `result` field; `E₂`'s own served values are
never consulted at all, only its *compiled views*, used solely to decide whether to accept a call. What
does change is the downstream payoff: (R4~)-acceptance only buys `CVEquiv`-agreement of the two engines'
own per-turn call views, not literal equality, which is what `callsB_agree_of_alignedT` concludes in
place of Module 1's `callsB_agree_of_aligned`. -/

open Classical in
noncomputable instance cvEquivDecidable {MethodName Args : Type} [Setoid Args] :
    DecidableRel (@CVEquiv MethodName Args _) := fun _ _ => Classical.propDecidable _

/-- **`ConvergentReplayT`** — (R4~)-relaxed `ConvergentReplay`: `ρ = τ_B(R₁)` (built via `E₁`, D9's own
construction) is convergent for a replay driven by `E₂`'s `next`/`callsB` under (R4~) matching, i.e. that
replay reproduces `R₁`'s own per-node history entry for entry, **literally**. -/
noncomputable def ConvergentReplayT {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Args]
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (B : Boundary) : Prop :=
  ConvergentReplayWith CVEquiv R₁ E₂ adapterView driverView B

/-- **`PerTurnAlignedT`** — (R4~)-relaxed `PerTurnAligned`: whenever replaying exactly `k` steps for node
`n` succeeds, the cursor it lands on is exactly the event-count `E₁`'s own compilation of the replayed
prefix produces. -/
noncomputable def PerTurnAlignedT {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Args]
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (B : Boundary) : Prop :=
  PerTurnAlignedWith CVEquiv R₁ E₂ adapterView driverView B

/-- **`callsB_agree_of_alignedT`** — (R4~)-relaxed `callsB_agree_of_aligned`: `ConvergentReplayT` +
`PerTurnAlignedT` recover (A~) at the `CallView` level, turn by turn: `CVEquiv` pointwise agreement of
the two engines' own compiled calls, in place of Module 1's literal equality. -/
theorem callsB_agree_of_alignedT {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Args]
    {P : Project Nodes FQN Query Relation} {E₁ E₂ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (hCV : ConvergentReplayT R₁ E₂ adapterView driverView B)
    (hAl : PerTurnAlignedT R₁ E₂ adapterView driverView B) :
    ∀ j, 1 ≤ j → j ≤ R₁.N →
      LForall₂ CVEquiv (callsB E₁ adapterView driverView B (R₁.stmt j))
        (callsB E₂ adapterView driverView B (R₁.stmt j)) :=
  callsB_agree_of_aligned_with CVEquiv R₁ adapterView driverView B hCV hAl

/-! ## Well-formedness for T2₁/T2₂

Everything Module 2 declares untouched (target-faithfulness, DAG-order,
`UniqueWriterGlobal`, `StaticPrec`) is Module 1's, verbatim; the
`~`-relaxed conditions of Module 2 follow. -/

/-- **(~-target-preserving)**: `stmt ~_S stmt' ⟹ target(stmt) = target(stmt')`. -/
def TargetPreserving (FQN Query : Type) [Setoid (Statement FQN Query)] : Prop :=
  ∀ s s' : Statement FQN Query, s ≈ s' → target s = target s'

/-- **(reads-sound-~)**, corrected. An earlier draft of this hypothesis
(`ReadsSoundT`) quantified the statement supplying the `reads` set
(`stmt`) *separately* from the two `~_S`-related statements `ret` was
actually applied to (`s`, `s'`), with nothing tying the three together —
so `stmt` could be chosen to read almost nothing, forcing the
state-agreement premise to be nearly vacuous, while `s`/`s'` ranged freely
over unrelated, state-dependent statements. That made it false for any
realistic SQL semantics with genuine state-dependence. `ReadsSound` is the
fix: an exact structural mirror of Module 1's `ReadsSound`, `=` replaced by
`≈`/`OptEquiv` throughout, with a single `stmt` playing both roles at once
— it both supplies the `reads` set *and* is the statement `ret` is
evaluated against, on both sides of the equivalence. `T2` recovers
everything the old, unsound hypothesis bought by pairing this with
`CompiledReadsSound` (reused unchanged from Module 1 — see below) and the
new `RetCongruent` (see `stepAgreeT`, `foldl_step_maintainT`, and their
derivation-pattern docstrings) instead of assuming it all at once. -/
def ReadsSound {FQN Query Relation : Type} [Setoid Relation]
    (reads : Statement FQN Query → FQN → Prop)
    (ret : State FQN Relation → Query → Relation) : Prop :=
  ∀ (stmt : Statement FQN Query) (S S' : State FQN Relation),
    (∀ o, reads stmt o → OptEquiv (S o) (S' o)) → ret S (qOf stmt) ≈ ret S' (qOf stmt)

/- Module 1's **`CompiledReadsSound`** — "every compiled call a statement
realizes to reads no more than the abstract statement declares" — needs no
`~`-relaxation at all (its statement never mentions `Relation`'s
equivalence), so Module 2 reuses it completely unchanged via the `open
Formalization.Module1` above; nothing is redeclared here. It supplies the
missing link `ReadsSound` alone cannot: given an abstract statement
`stmtV` and one of its compiled realizations `c` (`c ∈ drvE E₁ stmtV`),
agreement on everything `stmtV` reads gives agreement on everything `c`
reads, which is exactly the premise `ReadsSound` needs to be applied *at*
`c`. -/

/-- **(ret-~-congruent)** — new in Module 2, needed only alongside
`ReadsSound`/`CompiledReadsSound` in place of the retired `ReadsSoundT`:
evaluating two `~_S`-congruent statements against the *same* state gives
`~_R`-equivalent results. Where `ReadsSound` buys agreement, for *one*
statement, across two states that agree on its reads, `RetCongruent` buys
agreement, for *one* state, across two `~_S`-related statements.
`stepAgreeT` and `foldl_step_maintainT` chain the two: given `stmtV`'s two
compiled calls `c ∈ drvE E₁ stmtV`, `c' ∈ drvE E₂ stmtV` with `c ≈ c'`
(from `(A~)`), and `S₁`/`S₂` agreeing on everything `stmtV` (hence, via
`CompiledReadsSound`, `c`) reads, `ReadsSound` at `c` gives `ret S₁ (qOf c)
≈ ret S₂ (qOf c)`, and `RetCongruent` at `S₂` gives `ret S₂ (qOf c) ≈ ret
S₂ (qOf c')`; transitivity closes the gap to `ret S₁ (qOf c) ≈ ret S₂ (qOf
c')`. -/
def RetCongruent {FQN Query Relation : Type} [Setoid Relation] [Setoid (Statement FQN Query)]
    (ret : State FQN Relation → Query → Relation) : Prop :=
  ∀ (S : State FQN Relation) (stmt stmt' : Statement FQN Query), stmt ≈ stmt' →
    ret S (qOf stmt) ≈ ret S (qOf stmt')

/-- **(driver-view-~-faithful)**: `driverView(c) ~_V driverView(c') ⟹ c ~_S c'`. -/
def DriverViewFaithful {FQN Query MethodName Args : Type}
    [Setoid Args] [Setoid (Statement FQN Query)]
    (driverView : DriverCall FQN Query → CallView MethodName Args) : Prop :=
  ∀ c c', CVEquiv (driverView c) (driverView c') → c ≈ c'

/-- **(adapter-view-~-faithful)**: `adapterView(c) ~_V adapterView(c') ⟹ c ~_AC c'`. -/
def AdapterViewFaithful {MethodName Args : Type} [Setoid Args]
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args) : Prop :=
  ∀ c c', CVEquiv (adapterView c) (adapterView c') → ACEquiv c c'

/-- Two `~_S`-related statements have the same constructor shape (immediate
from `(~-target-preserving)`: `target` distinguishes `Write` from `Read`). -/
theorem read_of_equiv_read {FQN Query : Type} [Setoid (Statement FQN Query)]
    (hTP : TargetPreserving FQN Query) {q : Query} {s : Statement FQN Query}
    (h : (Statement.read q : Statement FQN Query) ≈ s) : ∃ q', s = Statement.read q' := by
  have ht := hTP _ _ h
  cases s with
  | read q' => exact ⟨q', rfl⟩
  | write o' q' => rw [target, target] at ht; exact absurd ht.symm (by simp)

theorem write_of_equiv_write {FQN Query : Type} [Setoid (Statement FQN Query)]
    (hTP : TargetPreserving FQN Query) {o : FQN} {q : Query} {s : Statement FQN Query}
    (h : (Statement.write o q : Statement FQN Query) ≈ s) :
    ∃ q', s = Statement.write o q' := by
  have ht := hTP _ _ h
  cases s with
  | read q' => rw [target, target] at ht; exact absurd ht (by simp)
  | write o' q' =>
    rw [target, target] at ht
    exact ⟨q', by rw [(Option.some.inj ht).symm]⟩

/-! ## The driver boundary as a `Level`

Module 1's equivalence-parametrized core (`Eqv`) is stated for any `Level`. The
driver level's calls are `Statement`s, with the `~_S` setoid assumed here; the
three driver-level hypotheses below (`ReadsSound`, `RetCongruent`,
`TargetPreserving`) are exactly what makes `driverLevel` a `LevelSoundT`. -/

instance driverCallSetoid {FQN Query Relation : Type} [DecidableEq FQN]
    [Setoid (Statement FQN Query)]
    {ret : State FQN Relation → Query → Relation}
    {reads : Statement FQN Query → FQN → Prop} :
    Setoid (driverLevel ret reads).Call :=
  inferInstanceAs (Setoid (Statement FQN Query))

theorem driverLevel_soundT {FQN Query Relation : Type} [DecidableEq FQN]
    [Setoid Relation] [Setoid (Statement FQN Query)]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    (hRS : ReadsSound reads ret) (hRC : RetCongruent ret) (hTP : TargetPreserving FQN Query) :
    LevelSoundT (driverLevel ret reads) where
  preserve := driverLevel_preserve ret reads
  target_pres := fun c c' h => hTP c c' h
  reads_sound := fun c S S' hag t ht => by
    cases c with
    | write o q =>
      have hto : o = t := Option.some.inj ht
      subst hto
      have := hRS (Statement.write o q) S S' hag
      simp only [driverLevel, execS, qOf, ite_true] at this ⊢
      exact this
    | read q => simp [driverLevel, target] at ht
  ans_sound := fun c S S' hag => by
    cases c with
    | write o q => exact trivial
    | read q =>
      exact hRS (Statement.read q) S S' hag
  step_congr := fun c c' hcc S t ht => by
    cases c with
    | write o q =>
      have hto : o = t := Option.some.inj ht
      subst hto
      obtain ⟨q', hq'⟩ := write_of_equiv_write hTP hcc
      subst hq'
      simp only [driverLevel, execS, ite_true]
      exact hRC S (Statement.write o q) (Statement.write o q') hcc
    | read q => simp [driverLevel, target] at ht
  ans_congr := fun c c' hcc S => by
    cases c with
    | write o q =>
      obtain ⟨q', hq'⟩ := write_of_equiv_write hTP hcc
      subst hq'; exact trivial
    | read q =>
      obtain ⟨q', hq'⟩ := read_of_equiv_read hTP hcc
      subst hq'
      exact hRC S (Statement.read q) (Statement.read q') hcc

/-- Module 1's `stepAgree`, at the driver level, in `rE` form. -/
theorem stepAgreeT {FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [Setoid Relation] [Setoid (Statement FQN Query)]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args}
    (hRS : ReadsSound reads ret) (hCRS1 : CompiledReadsSound reads E₁) (hRC : RetCongruent ret)
    (hTP : TargetPreserving FQN Query)
    (stmtV : Statement FQN Query) (S₁ S₂ : State FQN Relation)
    (hSagree : ∀ o', reads stmtV o' → OptEquiv (S₁ o') (S₂ o'))
    (hA : LForall₂ (· ≈ ·) (drvE E₁ stmtV) (drvE E₂ stmtV))
    (r₁ r₂ : Result Relation)
    (h1 : rE ret E₁ S₁ stmtV = some r₁) (h2 : rE ret E₂ S₂ stmtV = some r₂) :
    ResEquiv r₁ r₂ :=
  Formalization.Module1.Eqv.stepAgree (L := driverLevel ret reads) (comp₁ := drvE E₁)
    (comp₂ := drvE E₂) (driverLevel_soundT hRS hRC hTP) (driverLevel_compiledReadsSound hCRS1)
    stmtV S₁ S₂ hSagree hA r₁ r₂ ((rL_driver ret reads E₁ S₁ stmtV).trans h1)
    ((rL_driver ret reads E₂ S₂ stmtV).trans h2)

/-- **T2₂/T2₁'s shared core, given `(A~)`** at the driver level: Module 1's
`Eqv.T2_of_A` at `driverLevel`. `hAWrite`/`hReadRes` split `(A~)` into its
write-turn call-agreement half and its read-turn result-agreement conclusion —
the split segmented matching (Module 3) forces. -/
theorem T2_of_A {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid (Statement FQN Query)]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (hRS : ReadsSound reads ret) (hCRS1 : CompiledReadsSound reads E₁) (hRC : RetCongruent ret)
    (hTP : TargetPreserving FQN Query)
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hTF1 : TargetFaithful E₁) (hTF2 : TargetFaithful E₂)
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P)) (hNTI : NextTildeInsensitive P)
    (hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      LForall₂ (· ≈ ·) (effCalls (driverLevel ret reads) (drvE E₁ (R₁.stmt j)))
        (effCalls (driverLevel ret reads) (drvE E₂ (R₁.stmt j))))
    (hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAt R₁.stmt ret E₁ S₀ j o') (stateAt R₂.stmt ret E₂ S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i)) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have h := Formalization.Module1.Eqv.T2_of_A (driverLevel_soundT hRS hRC hTP)
    (R₁.toL reads) (R₂.toL reads)
    (driverLevel_targetFaithful hTF1) (driverLevel_targetFaithful hTF2) hUWG hDAG1 hDAG2 hSWF
    hNTI
    (fun j hj1 hjN hw => writeAgree_of_forall₂ (driverLevel_soundT hRS hRC hTP)
      (driverLevel_compiledReadsSound hCRS1) (driverLevel_targetFaithful hTF1) _
      (hAWrite j hj1 hjN hw))
    hReadRes
  exact ⟨h.1, h.2.1, h.2.2⟩

/-! ## Deriving `(A~)` from `ConvergentReplayT`/`PerTurnAlignedT`

Module 1's own `T2_2`/`T2_1` derive `(A)` inline from `callsB_agree_of_aligned`
plus view-injectivity, with no separate helper between the replay hypotheses and
the theorem; `T2_2`/`T2_1` below mirror that, deriving `(A~)` from
`callsB_agree_of_alignedT` plus view-faithfulness. -/

/-! ## T2₂ / T2₁ (Cross-engine conformance, relaxed) -/

/-- **T2₂ (Cross-engine conformance via `adapter→driver` recording,
relaxed).** `R₁` live, `ρ = τ_{adapter→driver}(R₁)` `ConvergentReplayT` +
`PerTurnAlignedT` for some replay of `E₂`, `P` single-writer-per-FQN and
`(static-acyclicity)`, both engines target-faithful, both schedules
DAG-order, `ret` `reads-sound-~`, `(~-target-preserving)`,
`(driver-view-~-faithful)` — plus `(next-~-insensitive)` (see its docstring:
not in `formalization-2.md`, and necessary). Conclusion:
`S_final(R₁) ~_St S_final(R₂)` and `O(R₁) ~_O O(R₂)`, hence `R₁ ≈ R₂` (D8′).

`(A~)` itself comes from `callsB_agree_of_alignedT` plus
`(driver-view-~-faithful)`, applied pointwise via `LForall₂.of_map`/`.imp` —
Module 1's `list_map_injective` step, transported to `~_A`-level
injectivity. -/
theorem T2_2 {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid Args]
    [Setoid (Statement FQN Query)]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (hRS : ReadsSound reads ret) (hCRS1 : CompiledReadsSound reads E₁) (hRC : RetCongruent ret)
    (hTP : TargetPreserving FQN Query)
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hTF1 : TargetFaithful E₁) (hTF2 : TargetFaithful E₂)
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P)) (hNTI : NextTildeInsensitive P)
    {adapterView : AdapterCall MethodName Args → CallView MethodName Args}
    {driverView : DriverCall FQN Query → CallView MethodName Args}
    (hDVF : DriverViewFaithful driverView)
    (hCV : ConvergentReplayT R₁ E₂ adapterView driverView Boundary.adapterDriver)
    (hAl : PerTurnAlignedT R₁ E₂ adapterView driverView Boundary.adapterDriver) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have hcb := callsB_agree_of_alignedT R₁ adapterView driverView Boundary.adapterDriver hCV hAl
  simp only [callsB] at hcb
  have hA : ∀ j, 1 ≤ j → j ≤ R₁.N →
      LForall₂ (· ≈ ·) (drvE E₁ (R₁.stmt j)) (drvE E₂ (R₁.stmt j)) := by
    intro j hj1 hjN
    exact (hcb j hj1 hjN).of_map.imp (fun a b h => hDVF a b h)
  -- Positional matching gives blanket `(A~)` outright; `T2_of_A` only wants
  -- its write/read-restricted halves, so this is a trivial adapter.
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      LForall₂ (· ≈ ·) (effCalls (driverLevel ret reads) (drvE E₁ (R₁.stmt j)))
        (effCalls (driverLevel ret reads) (drvE E₂ (R₁.stmt j))) :=
    fun j hj1 hjN _ => effCalls_congr (driverLevel_soundT hRS hRC hTP) (hA j hj1 hjN)
  have hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAt R₁.stmt ret E₁ S₀ j o') (stateAt R₂.stmt ret E₂ S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i) := by
    intro j i hj1 hjN hi1 hiN hstmt_eq _ hSagree
    have hresA := R₁.res_eq j hj1 hjN
    have hresB := R₂.res_eq i hi1 hiN
    rw [← hstmt_eq] at hresB
    exact stepAgreeT hRS hCRS1 hRC hTP (R₁.stmt j) (stateAt R₁.stmt ret E₁ S₀ j)
      (stateAt R₂.stmt ret E₂ S₀ i) hSagree (hA j hj1 hjN) _ _ hresA hresB
  exact T2_of_A hRS hCRS1 hRC hTP R₁ R₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI hAWrite hReadRes

/-- **T2₁ (Cross-engine conformance via `core→adapter` recording, relaxed).**
`ρ = τ_{core→adapter}(R₁)` is `ConvergentReplayT`/`PerTurnAlignedT` for `E₂`,
`(adapter-view-~-faithful)` gives `(A~)` at the *adapter* level (`α` calls
pointwise `ACEquiv`), and the T2 argument runs there (`Eqv.T2_adapter`) on the
adapter-level runs `A` induces; `RunLinkT` ties them back to the recorded
driver-boundary runs. No assumption relates `δ_{E₁}` to `δ_{E₂}`. -/
theorem T2_1 {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid Args]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (A : AdapterSem FQN Relation MethodName Args) (hAs : LevelSoundT A.level)
    (hCRS1 : CompiledReadsSoundL reads (alphaComp (Query := Query) A E₁))
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
    (hCV : ConvergentReplayT R₁ E₂ adapterView driverView Boundary.coreAdapter)
    (hAl : PerTurnAlignedT R₁ E₂ adapterView driverView Boundary.coreAdapter) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have hcb := callsB_agree_of_alignedT R₁ adapterView driverView Boundary.coreAdapter hCV hAl
  simp only [callsB] at hcb
  have hAlpha : ∀ j, 1 ≤ j → j ≤ R₁.N →
      LForall₂ (· ≈ ·) (alphaComp (Query := Query) A E₁ (R₁.stmt j))
        (alphaComp (Query := Query) A E₂ (R₁.stmt j)) := by
    intro j hj1 hjN
    exact (hcb j hj1 hjN).of_map.imp (fun a b h => hAVF a b h)
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      LForall₂ (· ≈ ·) (effCalls A.level (alphaComp (Query := Query) A E₁ (R₁.stmt j)))
        (effCalls A.level (alphaComp (Query := Query) A E₂ (R₁.stmt j))) :=
    fun j hj1 hjN _ => effCalls_congr hAs (hAlpha j hj1 hjN)
  have hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL (alphaComp (Query := Query) A E₁) R₁.stmt S₀ j o')
          (stateAtL (alphaComp (Query := Query) A E₂) R₂.stmt S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i) := by
    intro j i hj1 hjN hi1 hiN hstmt_eq _ hSagree
    obtain ⟨r₁, h1, e1⟩ := hk₁.res_link j hj1 hjN
    obtain ⟨r₂, h2, e2⟩ := hk₂.res_link i hi1 hiN
    rw [← hstmt_eq] at h2
    have hr := stepAgree hAs hCRS1 (R₁.stmt j) _ _ hSagree (hAlpha j hj1 hjN) r₁ r₂ h1 h2
    exact ResEquiv.trans (ResEquiv.symm e1) (ResEquiv.trans hr e2)
  have h := Eqv.T2_adapter A hAs R₁ R₂ hk₁ hk₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI
    (fun j hj1 hjN hw => writeAgree_of_forall₂ hAs hCRS1 hTF1 _ (hAWrite j hj1 hjN hw)) hReadRes
  exact ⟨h.1, ⟨h.2.1, h.2.2⟩, h.1, ⟨h.2.1, h.2.2⟩⟩

end Module2
end Formalization
