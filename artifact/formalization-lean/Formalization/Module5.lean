/-
Module 5: write-commutative regions ("runs"), **matched call by call**.

Module 3 matches a live write call to *the* recorded write barrier with the same number: writes are served
in strict recorded order. Module 5 relaxes that for the writes *inside one turn*. A materialization emits a
stream of DDL calls, grouped into **bundles** (a chain of calls whose order is fixed by an immediate
dependency, such as `create schema s; create view s.v`), and two engines may emit the bundles in different
orders. A **run** is a stretch of those write calls whose bundles commute: replay may serve the bundles in any
order, and the statements inside a bundle in their recorded order.

**What a run is, in the model.**

* A block of calls is a list of calls of a boundary `L`. Two blocks *commute* (`BlockCommute`) when, at every
  state, running them in either order leaves `~_R`-equal states. `BlockPerm` is the least relation containing
  adjacent swaps of commuting blocks, and `blockPerm_fold` shows that it preserves the effect of the flattened
  call list. Footprint disjointness is a sufficient condition for commutation (it is what the implementation's
  object-key check approximates), but the model needs only the semantic property.
* A turn's write calls `ws`, read in the order `π`, are a **valid run** (`RunCert L ws π`) when `ws` splits into
  blocks that a `BlockPerm` rearranges into `permList ws π`.
* Replay (`MatchCallXR`) is Module 4's matcher with one change: a live *write* call with barrier count `c`
  matches the recorded write whose barrier number is `ρ c`, instead of `c`. `ρ` is the identity off a run and
  permutes the barrier numbers of a run's turn. The candidate-set narrowing of the implementation is one way
  to compute `ρ`; the model asks only that some `ρ` exists with the properties below. Read calls are matched
  as before, and a statement with no target uses `ρ = id` (`RunSpec.readId`).

**What it buys.** Under Module 3 a replay gives the T2 core, for every write turn, that the two engines'
effect calls are pointwise `≈`. Under Module 5 the replaying engine's effect calls are a commuting reordering
of the recording's, so that fact no longer holds. The T2 core instead takes the weaker `WriteAgree`
(Module 1), which `replay_hAWriteP` derives from a convergent replay and a `RunCert`. `T2_2` and `T2_1` are
Module 4's theorems with the strict write matcher replaced by the run matcher.

**What the object model has to be.** A turn has one target, and every call of it targets that same object
(`TargetFaithful`). The sub-objects a bundle creates (the schema and the view) are therefore parts of the
value of the node's own target. A call updates a part of the value, which makes it read its own target; the
model allows that (`StaticPrec` excludes only a read of a *different* object). A node's objects are its own,
by `UniqueWriterGlobal`, so another node never writes into a run's span. Real dbt threads interleave calls of
different nodes, and idempotent `CREATE SCHEMA IF NOT EXISTS` may be shared across nodes; neither is
modeled (see `implementation-deviations.md`).
-/

import Formalization.Module4

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Formalization
namespace Module5

open Formalization.Module1 hiding BehEquiv T2_1 T2_2 ReadsSound
open Formalization.Module1.Eqv hiding ObsEquiv BehEquiv
open Formalization.Module2 hiding T2_1 T2_2
open Formalization.Module3 hiding T2_1 T2_2
open Formalization.Module4 hiding T2_1 T2_2

/-! # Commuting blocks -/

section Commutation

variable {FQN Relation : Type} [Setoid Relation]

theorem stateEquiv_refl (S : State FQN Relation) : StateEquiv S S := fun _ => OptEquiv.refl _

/-- One step is a congruence for `StateEquiv`: equivalent states stay equivalent. -/
theorem step_stateEquiv {L : Level FQN Relation} [Setoid L.Call] (hL : LevelSoundT L)
    {S S' : State FQN Relation} (h : StateEquiv S S') (c : L.Call) :
    StateEquiv (L.step S c) (L.step S' c) := by
  intro o
  by_cases ht : L.target c = some o
  · exact hL.reads_sound c S S' (fun o' _ => h o') o ht
  · rw [hL.preserve c S o ht, hL.preserve c S' o ht]; exact h o

theorem foldl_stateEquiv {L : Level FQN Relation} [Setoid L.Call] (hL : LevelSoundT L) :
    ∀ (cs : List L.Call) {S S' : State FQN Relation}, StateEquiv S S' →
      StateEquiv (cs.foldl L.step S) (cs.foldl L.step S')
  | [], _, _, h => h
  | c :: cs, _, _, h => foldl_stateEquiv hL cs (step_stateEquiv hL h c)

/-- **Two blocks commute**: at every state, running `a` then `b` leaves the same state, up to `~`, as
running `b` then `a`. -/
def BlockCommute (L : Level FQN Relation) (a b : List L.Call) : Prop :=
  ∀ S : State FQN Relation,
    StateEquiv (b.foldl L.step (a.foldl L.step S)) (a.foldl L.step (b.foldl L.step S))

/-- Reorderings reachable by swapping adjacent commuting blocks. -/
inductive BlockPerm (L : Level FQN Relation) :
    List (List L.Call) → List (List L.Call) → Prop
  | refl (l : List (List L.Call)) : BlockPerm L l l
  | swap (pre post : List (List L.Call)) (a b : List L.Call) :
      BlockCommute L a b → BlockPerm L (pre ++ a :: b :: post) (pre ++ b :: a :: post)
  | trans {l₁ l₂ l₃ : List (List L.Call)} :
      BlockPerm L l₁ l₂ → BlockPerm L l₂ l₃ → BlockPerm L l₁ l₃

/-- **Reordering commuting blocks does not change the effect** of the flattened call list. -/
theorem blockPerm_fold {L : Level FQN Relation} [Setoid L.Call] (hL : LevelSoundT L)
    {bs bs' : List (List L.Call)} (h : BlockPerm L bs bs') :
    ∀ S : State FQN Relation,
      StateEquiv (bs.flatten.foldl L.step S) (bs'.flatten.foldl L.step S) := by
  induction h with
  | refl l => intro S; exact stateEquiv_refl _
  | swap pre post a b hc =>
    intro S
    simp only [List.flatten_append, List.flatten_cons, List.foldl_append]
    exact foldl_stateEquiv hL _ (hc _)
  | trans _ _ ih1 ih2 => intro S; exact StateEquiv.trans (ih1 S) (ih2 S)

end Commutation

/-! # A list read in a permuted order -/

section PermList

variable {α : Type}

/-- The first `n` entries of `l` read in the order `π 0, π 1, …` (an index outside `l` is skipped). -/
def permAux (l : List α) (π : Nat → Nat) : Nat → List α
  | 0 => []
  | n + 1 => permAux l π n ++ (l[π n]?).toList

/-- `l` read in the order `π 0, …, π (|l|-1)`. -/
def permList (l : List α) (π : Nat → Nat) : List α := permAux l π l.length

theorem permAux_length (l : List α) (π : Nat → Nat) :
    ∀ n, (∀ u, u < n → π u < l.length) → (permAux l π n).length = n
  | 0, _ => rfl
  | n + 1, h => by
    have hπ : π n < l.length := h n (Nat.lt_succ_self n)
    have h1 : (l[π n]?).toList.length = 1 := by
      rw [List.getElem?_eq_getElem hπ]; rfl
    simp only [permAux, List.length_append, h1]
    rw [permAux_length l π n (fun u hu => h u (Nat.lt_succ_of_lt hu))]

theorem permAux_getElem? (l : List α) (π : Nat → Nat) :
    ∀ n, (∀ u, u < n → π u < l.length) → ∀ u, u < n → (permAux l π n)[u]? = l[π u]?
  | 0, _, u, hu => by omega
  | n + 1, h, u, hu => by
    have hπ : π n < l.length := h n (Nat.lt_succ_self n)
    have hlen : (permAux l π n).length = n :=
      permAux_length l π n (fun u hu => h u (Nat.lt_succ_of_lt hu))
    simp only [permAux]
    rcases Nat.lt_or_ge u n with hlt | hge
    · rw [List.getElem?_append_left (by omega)]
      exact permAux_getElem? l π n (fun u hu => h u (Nat.lt_succ_of_lt hu)) u hlt
    · have hun : u = n := by omega
      subst hun
      rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
      rw [List.getElem?_eq_getElem hπ]; rfl

theorem permAux_mem (l : List α) (π : Nat → Nat) :
    ∀ (n : Nat) (x : α), x ∈ permAux l π n → ∃ u, l[π u]? = some x
  | 0, x, h => by simp [permAux] at h
  | n + 1, x, h => by
    simp only [permAux, List.mem_append] at h
    rcases h with h | h
    · exact permAux_mem l π n x h
    · refine ⟨n, ?_⟩
      cases hn : l[π n]? with
      | none => rw [hn] at h; simp at h
      | some y => rw [hn] at h; simp at h; rw [h]

theorem permAux_map {β : Type} (f : α → β) (l : List α) (π : Nat → Nat) :
    ∀ n, permAux (l.map f) π n = (permAux l π n).map f
  | 0 => rfl
  | n + 1 => by
    simp only [permAux, List.map_append, permAux_map f l π n]
    congr 1
    simp [List.getElem?_map]
    cases l[π n]? <;> rfl

theorem permList_map {β : Type} (f : α → β) (l : List α) (π : Nat → Nat) :
    permList (l.map f) π = (permList l π).map f := by
  unfold permList
  rw [List.length_map, permAux_map]

theorem permList_length (l : List α) (π : Nat → Nat) (h : ∀ u, u < l.length → π u < l.length) :
    (permList l π).length = l.length :=
  permAux_length l π l.length h

theorem permList_getElem? (l : List α) (π : Nat → Nat) (h : ∀ u, u < l.length → π u < l.length)
    (u : Nat) (hu : u < l.length) : (permList l π)[u]? = l[π u]? :=
  permAux_getElem? l π l.length h u hu

theorem permAux_id (l : List α) (π : Nat → Nat) (hπ : ∀ u, π u = u) :
    ∀ n, n ≤ l.length → permAux l π n = l.take n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [permAux, hπ]
    rw [permAux_id l π hπ n (by omega), List.take_add_one]

theorem permList_id (l : List α) (π : Nat → Nat) (hπ : ∀ u, π u = u) : permList l π = l := by
  unfold permList
  rw [permAux_id l π hπ l.length (Nat.le_refl _), List.take_length]

theorem permList_mem (l : List α) (π : Nat → Nat) (x : α) (h : x ∈ permList l π) : x ∈ l := by
  obtain ⟨u, hu⟩ := permAux_mem l π l.length x h
  exact List.mem_of_getElem? hu

end PermList

/-! # The run matcher -/

section Matcher

variable {FQN Query Relation MethodName Args : Type}

/-- **The call matcher with runs.** Module 4's `MatchCallX`, with one change in the write clause: a live
write with barrier count `c` is served by the recorded write whose barrier number is `ρ stmt c`, where `stmt`
is the live statement the call belongs to. `ρ stmt = id` gives `MatchCallX`. -/
def MatchCallXR (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop)
    (XS : Statement FQN Query → CallView MethodName Args → Result Relation → Prop)
    (ρ : Statement FQN Query → Nat → Nat)
    (stmt : Statement FQN Query) (c : Nat) (v : CallView MethodName Args)
    (r : Result Relation) (c' : Nat) : Prop :=
  (isW cls v = true → ∃ e, F e ∧ isW cls e.view = true ∧ e.seg = ρ stmt c ∧ m v e.view ∧
      r = e.res ∧ c' = c + 1) ∧
  (isW cls v = false →
    (∃ e, F e ∧ isW cls e.view = false ∧ e.seg = c ∧ m v e.view ∧ r = e.res ∧ c' = c) ∨
    ((¬ ∃ e, F e ∧ isW cls e.view = false ∧ e.seg = c ∧ m v e.view) ∧ XS stmt v r ∧ c' = c))

/-- What the extraction lemmas need of a matcher with the write permutation `ρ`: a live write is served
by the recorded write barrier `ρ c` (and consumes one barrier), a live read leaves the count alone. -/
structure MatcherSpecP (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop) (ρ : Nat → Nat)
    (mc : Nat → CallView MethodName Args → Result Relation → Nat → Prop) : Prop where
  write : ∀ c v r c', mc c v r c' → isW cls v = true →
    ∃ e, F e ∧ isW cls e.view = true ∧ e.seg = ρ c ∧ m v e.view ∧ r = e.res ∧ c' = c + 1
  read : ∀ c v r c', mc c v r c' → isW cls v = false → c' = c

theorem MatcherSpecP.counts {cls : MethodName → Cls}
    {m : CallView MethodName Args → CallView MethodName Args → Prop}
    {F : RecEv MethodName Args Relation → Prop} {ρ : Nat → Nat}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hs : MatcherSpecP cls m F ρ mc') :
    ∀ c v r c', mc' c v r c' → c' = c + (if isW cls v = true then 1 else 0) := by
  intro c v r c' h
  by_cases hw : isW cls v = true
  · obtain ⟨-, -, -, -, -, -, hc⟩ := hs.write c v r c' h hw
    simp [hw, hc]
  · have hw' : isW cls v = false := by simpa using hw
    simp [hw, hs.read c v r c' h hw']

theorem MatchCallXR.specP (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop)
    (XS : Statement FQN Query → CallView MethodName Args → Result Relation → Prop)
    (ρ : Statement FQN Query → Nat → Nat) (stmt : Statement FQN Query) :
    MatcherSpecP cls m F (ρ stmt) (MatchCallXR cls m F XS ρ stmt) where
  write := fun c v r c' h hw => h.1 hw
  read := fun c v r c' h hw => by
    rcases h.2 hw with ⟨-, -, -, -, -, -, hc'⟩ | ⟨-, -, hc'⟩ <;> exact hc'

/-- A statement whose `ρ` is the identity is matched exactly as in Module 4. -/
theorem MatchCallXR.spec (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop)
    (XS : Statement FQN Query → CallView MethodName Args → Result Relation → Prop)
    (ρ : Statement FQN Query → Nat → Nat) (stmt : Statement FQN Query)
    (hid : ∀ c, ρ stmt c = c) :
    MatcherSpec cls m F (MatchCallXR cls m F XS ρ stmt) where
  write := fun c v r c' h hw => by
    obtain ⟨e, hF, hew, hseg, hm, hr, hc'⟩ := h.1 hw
    exact ⟨e, hF, hew, by rw [hseg, hid], hm, hr, hc'⟩
  read := fun c v r c' h hw => (MatchCallXR.specP cls m F XS ρ stmt).read c v r c' h hw

/-- Each write call of a served turn, numbered `u` among the turn's writes, is served by the recorded write
barrier `ρ (c + u)`. -/
theorem MatchAll.writesP {cls : MethodName → Cls}
    {m : CallView MethodName Args → CallView MethodName Args → Prop}
    {F : RecEv MethodName Args Relation → Prop} {ρ : Nat → Nat}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hs : MatcherSpecP cls m F ρ mc')
    {c : Nat} {vs : List (CallView MethodName Args)} {c' : Nat}
    (h : MatchAll mc' c vs c') :
    ∀ (u : Nat) (w : CallView MethodName Args), (vs.filter (isW cls))[u]? = some w →
      ∃ e, F e ∧ isW cls e.view = true ∧ e.seg = ρ (c + u) ∧ m w e.view := by
  induction h with
  | nil => intro u w hw; simp at hw
  | @cons c v r c₁ vs c' hm hrest ih =>
    intro u w hw
    by_cases hv : isW cls v = true
    · obtain ⟨e, hF, hew, hseg, hmv, -, hc₁⟩ := hs.write c v r c₁ hm hv
      cases u with
      | zero =>
        simp only [List.filter_cons, hv, ite_true, List.getElem?_cons_zero, Option.some.injEq] at hw
        subst hw
        exact ⟨e, hF, hew, by simpa using hseg, hmv⟩
      | succ u =>
        simp only [List.filter_cons, hv, ite_true, List.getElem?_cons_succ] at hw
        obtain ⟨e', hF', hew', hseg', hm'⟩ := ih u w hw
        refine ⟨e', hF', hew', ?_, hm'⟩
        have : c₁ + u = c + (u + 1) := by omega
        rw [hseg', this]
    · have hv' : isW cls v = false := by simpa using hv
      have hc₁ := hs.read c v r c₁ hm hv'
      simp only [List.filter_cons, hv] at hw
      obtain ⟨e', hF', hew', hseg', hm'⟩ := ih u w hw
      exact ⟨e', hF', hew', by rw [hseg', hc₁], hm'⟩

/-- **The write calls of a served turn are a permutation of the recorded turn's write calls**, up to
`CVEquiv`: the `u`-th live write call matches the `π u`-th recorded write call of the turn, where
`π u = ρ (Wt t + u) - Wt t`. `hρ` says that `ρ` keeps a turn's barrier numbers inside the turn. -/
theorem write_views_matchP [Setoid Relation] [Setoid Args] {cls : MethodName → Cls}
    {recV liveV : Statement FQN Query → List (CallView MethodName Args)}
    {cr : Nat → Nat → Result Relation} {L : History FQN Query Relation}
    {t : Nat} {s : Statement FQN Query} {rr r' : Result Relation} {ρ : Nat → Nat}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hspec : MatcherSpecP cls CVEquiv (InRec cls recV cr L) ρ mc')
    (hLt : L[t]? = some (s, rr)) (hSBC : nw cls (liveV s) = nw cls (recV s))
    (hρ : ∀ c, Wt cls recV L t ≤ c → c < Wt cls recV L t + nw cls (recV s) →
      Wt cls recV L t ≤ ρ c ∧ ρ c < Wt cls recV L t + nw cls (recV s))
    (hserve : ServeTurn mc' (Wt cls recV L t) (liveV s) r' (Wt cls recV L (t + 1))) :
    LForall₂ CVEquiv ((liveV s).filter (isW cls))
      (permList ((recV s).filter (isW cls)) (fun u => ρ (Wt cls recV L t + u) - Wt cls recV L t)) := by
  have hwr := MatchAll.writesP hspec hserve.matchAll
  have hsucc := Wt_succ_of cls recV L t _ hLt
  simp only at hsucc
  have hlen : ((liveV s).filter (isW cls)).length = ((recV s).filter (isW cls)).length := hSBC
  have hπ : ∀ u, u < ((recV s).filter (isW cls)).length →
      ρ (Wt cls recV L t + u) - Wt cls recV L t < ((recV s).filter (isW cls)).length := by
    intro u hu
    have hm : ((recV s).filter (isW cls)).length = nw cls (recV s) := rfl
    rw [hm] at hu ⊢
    have := hρ (Wt cls recV L t + u) (by omega) (by omega)
    omega
  have hplen := permList_length ((recV s).filter (isW cls))
    (fun u => ρ (Wt cls recV L t + u) - Wt cls recV L t) hπ
  refine LForall₂.of_getElem? _ _ (by rw [hplen, hlen]) ?_
  intro u w w' hw hw'
  have hulen : u < ((liveV s).filter (isW cls)).length := (List.getElem?_eq_some_iff.mp hw).1
  have hum : u < nw cls (recV s) := by
    have : ((liveV s).filter (isW cls)).length = nw cls (recV s) := hlen
    omega
  obtain ⟨e, hF, hew, hseg, hm⟩ := hwr u w hw
  obtain ⟨hlo, hhi⟩ := hρ (Wt cls recV L t + u) (by omega) (by omega)
  obtain ⟨k, hk, -, hsegk⟩ := InRec.write_in_turn hF hew hLt (by omega) (by omega)
  have h1 := filter_getElem_of_write cls (recV s) k e.view hk hew
  have h2 : nw cls ((recV s).take k) = ρ (Wt cls recV L t + u) - Wt cls recV L t := by omega
  rw [h2] at h1
  rw [permList_getElem? _ _ hπ u (by omega)] at hw'
  rw [h1] at hw'
  rw [← Option.some.inj hw']
  exact hm

end Matcher

/-! # Runs, and what a convergent replay gives the T2 core -/

section Sem

variable {Nodes FQN Query Relation MethodName Args : Type} [DecidableEq FQN] [DecidableEq Nodes]

/-- **A run.** A turn's write calls `ws`, in recorded order, are read in the order `π` by a replay that
serves a run's bundles in a different order: `ws` splits into blocks, and a sequence of swaps of adjacent
commuting blocks rearranges them into `permList ws π`. -/
def RunCert [Setoid Relation] (L : Level FQN Relation) (ws : List L.Call) (π : Nat → Nat) : Prop :=
  ∃ bs bs' : List (List L.Call), bs.flatten = ws ∧ bs'.flatten = permList ws π ∧ BlockPerm L bs bs'

omit [DecidableEq FQN] in
/-- Serving a turn's writes in their recorded order is a (trivial) run. -/
theorem RunCert.of_id [Setoid Relation] {L : Level FQN Relation} (ws : List L.Call) (π : Nat → Nat)
    (hπ : ∀ u, π u = u) : RunCert L ws π :=
  ⟨[ws], [ws], by simp, by simp [permList_id ws π hπ], BlockPerm.refl _⟩

omit [DecidableEq FQN] in
/-- A valid run does not change the effect of the turn's write calls. -/
theorem RunCert.effect [Setoid Relation] {L : Level FQN Relation} [Setoid L.Call]
    (hL : LevelSoundT L) {ws : List L.Call} {π : Nat → Nat} (h : RunCert L ws π)
    (S : State FQN Relation) :
    StateEquiv (ws.foldl L.step S) ((permList ws π).foldl L.step S) := by
  obtain ⟨bs, bs', h1, h2, hp⟩ := h
  have := blockPerm_fold hL hp S
  rw [h1, h2] at this
  exact this

/-- The write-barrier number at which the recorded turn at position `j` of `R₁` starts. -/
abbrev turnBase {L : Level FQN Relation} (cls : MethodName → Cls)
    (comp₁ : Comp FQN Query Relation L) (view : L.Call → CallView MethodName Args)
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (j : Nat) : Nat :=
  Wt cls (fun s => (comp₁ s).map view) (recordingOf R₁ (R₁.node j)) (turnCount R₁.node (R₁.node j) j)

/-- **The run data of a replay.** `ρ n s` is the permutation of barrier numbers node `n` applies to a live
turn of statement `s`.
* `readId`: a statement with no target (a read) is not reordered.
* `range`: for a write turn, `ρ` keeps the barrier numbers of the turn inside the turn.
* `cert`: the order in which the turn's write calls are served is a valid run (`RunCert`). -/
structure RunSpec [Setoid Relation] {L : Level FQN Relation} (cls : MethodName → Cls)
    (comp₁ : Comp FQN Query Relation L) (view : L.Call → CallView MethodName Args)
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (ρ : Nodes → Statement FQN Query → Nat → Nat) : Prop where
  readId : ∀ n s, target s = none → ∀ c, ρ n s c = c
  range : ∀ j, 1 ≤ j → j ≤ R₁.N → target (R₁.stmt j) ≠ none →
    ∀ c, turnBase cls comp₁ view R₁ j ≤ c →
      c < turnBase cls comp₁ view R₁ j + nw cls ((comp₁ (R₁.stmt j)).map view) →
      turnBase cls comp₁ view R₁ j ≤ ρ (R₁.node j) (R₁.stmt j) c ∧
        ρ (R₁.node j) (R₁.stmt j) c <
          turnBase cls comp₁ view R₁ j + nw cls ((comp₁ (R₁.stmt j)).map view)
  cert : ∀ j, 1 ≤ j → j ≤ R₁.N → target (R₁.stmt j) ≠ none →
    RunCert L ((comp₁ (R₁.stmt j)).filter (isW cls ∘ view))
      (fun u => ρ (R₁.node j) (R₁.stmt j) (turnBase cls comp₁ view R₁ j + u) -
        turnBase cls comp₁ view R₁ j)

/-- The replay of Module 5: Module 4's replay with the matcher `MatchCallXR`, whose write clause serves
a live write from the recorded barrier `ρ`. -/
abbrev ReplayOKXR [Setoid Relation] [Setoid Args] {L : Level FQN Relation} (cls : MethodName → Cls)
    (comp₁ comp₂ : Comp FQN Query Relation L) (view : L.Call → CallView MethodName Args)
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (reads : Statement FQN Query → FQN → Prop)
    (R₁ : LiveRun P E₁ ret S₀)
    (Allowed : L.Call → L.Call → (Relation → Relation) → Prop)
    (ρ : Nodes → Statement FQN Query → Nat → Nat) : Prop :=
  ReplayWith cls comp₁ comp₂ view R₁ (fun n stmt =>
    MatchCallXR cls CVEquiv (recEvsOf cls comp₁ view R₁ n)
      (fun s v r => XServe comp₁ view reads R₁ Allowed n s v r) (ρ n) stmt)

/-- **`WriteAgree`, from a convergent replay with runs.** For a write turn, the replaying engine's write
calls are the recording's, read in the order the run matcher served them (`write_views_matchP`), and a valid
run does not change their effect (`RunCert.effect`). So from states agreeing on the statement's reads and at
a tracked object, the two engines' executions of the turn agree at that object. -/
theorem replay_hAWriteP [Setoid Relation] [Setoid Args] {L : Level FQN Relation} [Setoid L.Call]
    {cls : MethodName → Cls}
    {comp₁ comp₂ : Comp FQN Query Relation L} {view : L.Call → CallView MethodName Args}
    {reads : Statement FQN Query → FQN → Prop}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    {XS : Nodes → Statement FQN Query → CallView MethodName Args → Result Relation → Prop}
    {ρ : Nodes → Statement FQN Query → Nat → Nat}
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (hTF1 : TargetFaithfulL comp₁) (hCT : ClsTruthful L cls view)
    (hFaith : ∀ c c' : L.Call, CVEquiv (view c) (view c') → c ≈ c')
    (R₁ : LiveRun P E₁ ret S₀) (hNTI : NextTildeInsensitive P)
    (hSBC : SameBarrierCount cls (fun s => (comp₂ s).map view) (fun s => (comp₁ s).map view)
      R₁.N R₁.stmt)
    (hRuns : RunSpec cls comp₁ view R₁ ρ)
    (hCS : ReplayWith cls comp₁ comp₂ view R₁ (fun n stmt =>
      MatchCallXR cls CVEquiv (recEvsOf cls comp₁ view R₁ n) (XS n) (ρ n) stmt)) :
    ∀ j, 1 ≤ j → j ≤ R₁.N → target (R₁.stmt j) ≠ none →
      WriteAgree L reads comp₁ comp₂ (R₁.stmt j) := by
  intro j hj1 hjN hne
  have hspecP : ∀ n s, MatcherSpecP cls CVEquiv (recEvsOf cls comp₁ view R₁ n) (ρ n s)
      (MatchCallXR cls CVEquiv (recEvsOf cls comp₁ view R₁ n) (XS n) (ρ n) s) :=
    fun n s => MatchCallXR.specP cls CVEquiv _ (XS n) (ρ n) s
  obtain ⟨r', hserve, -⟩ := turn_at
    (mc := fun n stmt => MatchCallXR cls CVEquiv (recEvsOf cls comp₁ view R₁ n) (XS n) (ρ n) stmt)
    R₁ hNTI (fun n stmt c v r c' h => (hspecP n stmt).counts c v r c' h) hSBC hCS hj1 hjN
  have hLt := recordingOf_get R₁ (R₁.node j) j hj1 hjN rfl
  have hmatch := write_views_matchP (cls := cls) (recV := fun s => (comp₁ s).map view)
    (liveV := fun s => (comp₂ s).map view)
    (cr := recResOf comp₁ R₁.node R₁.stmt R₁.res S₀ R₁.N (R₁.node j))
    (hspecP (R₁.node j) (R₁.stmt j)) hLt (hSBC j hj1 hjN) (hRuns.range j hj1 hjN hne) hserve
  rw [List.filter_map, List.filter_map, permList_map] at hmatch
  have hcalls := (LForall₂.of_map hmatch).imp (fun a b h => hFaith a b h)
  have hcalls' := LForall₂.symm (fun hh => Setoid.symm hh) hcalls
  have hA : LForall₂ (· ≈ ·)
      (effCalls L (permList ((comp₁ (R₁.stmt j)).filter (isW cls ∘ view))
        (fun u => ρ (R₁.node j) (R₁.stmt j) (turnBase cls comp₁ view R₁ j + u) -
          turnBase cls comp₁ view R₁ j)))
      (effCalls L (comp₂ (R₁.stmt j))) := by
    rw [← effCalls_filter_write hCT (comp₂ (R₁.stmt j))]
    exact effCalls_congr hL hcalls'
  have hsub : ∀ c ∈ permList ((comp₁ (R₁.stmt j)).filter (isW cls ∘ view))
      (fun u => ρ (R₁.node j) (R₁.stmt j) (turnBase cls comp₁ view R₁ j + u) -
        turnBase cls comp₁ view R₁ j), c ∈ comp₁ (R₁.stmt j) :=
    fun c hc => (List.mem_filter.mp (permList_mem _ _ c hc)).1
  have hcert := hRuns.cert j hj1 hjN hne
  intro ot S₁ S₂ hS hT
  have e1 : (comp₁ (R₁.stmt j)).foldl L.step S₁ =
      ((comp₁ (R₁.stmt j)).filter (isW cls ∘ view)).foldl L.step S₁ := by
    rw [foldl_effCalls L hL.preserve (comp₁ (R₁.stmt j)) S₁,
      foldl_effCalls L hL.preserve ((comp₁ (R₁.stmt j)).filter (isW cls ∘ view)) S₁,
      effCalls_filter_write hCT (comp₁ (R₁.stmt j))]
  unfold execL
  rw [e1]
  exact OptEquiv.trans (hcert.effect hL S₁ ot)
    (foldl_agreeT_lists hL hCRS1 hTF1 (R₁.stmt j) ot _ _ hsub hA S₁ S₂ hS hT)

end Sem

/-! # T2₂ / T2₁ with write-commutative regions

`T2_of_A` is Module 2's driver-level facade of the T2 core with `WriteAgree` in place of pointwise `≈` of the
effect calls. `T2_2` and `T2_1` are Module 4's theorems with the strict write matcher replaced by the run
matcher: `hAWrite` now comes from `replay_hAWriteP`, `hReadRes` from Module 3's extraction lemma as before. -/

theorem T2_of_A {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid (Statement FQN Query)]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (hRS : ReadsSound reads ret) (hRC : RetCongruent ret)
    (hTP : TargetPreserving FQN Query)
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hTF1 : TargetFaithful E₁) (hTF2 : TargetFaithful E₂)
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P)) (hNTI : NextTildeInsensitive P)
    (hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree (driverLevel ret reads) reads (drvE E₁) (drvE E₂) (R₁.stmt j))
    (hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAt R₁.stmt ret E₁ S₀ j o') (stateAt R₂.stmt ret E₂ S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i)) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have h := Formalization.Module1.Eqv.T2_of_A (driverLevel_soundT hRS hRC hTP)
    (R₁.toL reads) (R₂.toL reads)
    (driverLevel_targetFaithful hTF1) (driverLevel_targetFaithful hTF2) hUWG hDAG1 hDAG2 hSWF
    hNTI hAWrite hReadRes
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **T2₂ with write-commutative regions** (adapter→driver recording): Module 4's `T2₂` with the run
matcher. `ρ` and `hRuns` give, for each write turn, the order in which the replay serves its write calls and
the certificate that this order is a run (commuting bundles). -/
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
    (ρ : Nodes → Statement FQN Query → Nat → Nat)
    (hRuns : RunSpec (L := driverLevel ret reads) cls (drvE E₁) driverView R₁ ρ)
    (hCS : ReplayOKXR (L := driverLevel ret reads) cls (drvE E₁) (drvE E₂) driverView reads R₁
      Allowed ρ) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have hLT := driverLevel_soundT hRS hRC hTP
  have hCRS1L := driverLevel_compiledReadsSound (ret := ret) hCRS1
  have hCRS2L := driverLevel_compiledReadsSound (ret := ret) hCRS2
  have hTF1L := driverLevel_targetFaithful (ret := ret) (reads := reads) hTF1
  have hLink : ResLink (L := driverLevel ret reads) (drvE E₁) R₁ := resLink_driver R₁
  have hspecP : ∀ n s, MatcherSpecP cls CVEquiv
      (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView R₁ n) (ρ n s)
      (MatchCallXR cls CVEquiv
        (recEvsOf (L := driverLevel ret reads) cls (drvE E₁) driverView R₁ n)
        (fun s v r => XServe (L := driverLevel ret reads) (drvE E₁) driverView reads R₁ Allowed n
          s v r) (ρ n) s) :=
    fun n s => MatchCallXR.specP cls CVEquiv _ _ (ρ n) s
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree (driverLevel ret reads) reads (drvE E₁) (drvE E₂) (R₁.stmt j) :=
    fun j hj1 hjN hw => replay_hAWriteP (L := driverLevel ret reads) (reads := reads)
      (XS := fun n s v r => XServe (L := driverLevel ret reads) (drvE E₁) driverView reads R₁
        Allowed n s v r)
      hLT hCRS1L hTF1L hCT hDVF R₁ hNTI hSBC hRuns hCS j hj1 hjN
      (by obtain ⟨o', ho'⟩ := hw; rw [ho']; exact Option.some_ne_none _)
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
      (fun n s c v r c' h => (hspecP n s).counts c v r c' h)
      (fun n s hs => MatchCallXR.spec cls CVEquiv _ _ (ρ n) s (hRuns.readId n s hs))
      (fun n s c v r c' hm hw => by
        rcases (hm.2 hw) with ⟨e, hF, hew, hseg, hmv, hr, -⟩ | ⟨-, hx, -⟩
        · exact Or.inl ⟨e, hF, hew, hseg, hmv, hr⟩
        · exact Or.inr hx)
      hSBC hCS
      (fun j S₂ b yb r' c₀ c' hj1 hjN hw' hSag hlast hyb hconv hx =>
        xServe_hX hLT hLink hDVF hTF1L hDAG1 hAllowed j S₂ b yb r' hj1 hjN hSag hyb hconv hx)
      j (stateAt R₂.stmt ret E₂ S₀ i) (R₂.res i) hj1 hjN hw hSagree h2
  exact T2_of_A hRS hRC hTP R₁ R₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI hAWrite hReadRes

/-- **T2₁ with write-commutative regions** (core→adapter recording). -/
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
    (ρ : Nodes → Statement FQN Query → Nat → Nat)
    (hRuns : RunSpec (L := A.level) cls (alphaComp (Query := Query) A E₁) adapterView R₁ ρ)
    (hCS : ReplayOKXR (L := A.level) cls (alphaComp (Query := Query) A E₁)
      (alphaComp (Query := Query) A E₂) adapterView reads R₁ Allowed ρ) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have hFaith : ∀ a b : A.level.Call, CVEquiv (adapterView a) (adapterView b) → a ≈ b :=
    fun a b h => hAVF a b h
  have hspecP : ∀ n s, MatcherSpecP cls CVEquiv
      (recEvsOf (L := A.level) cls (alphaComp (Query := Query) A E₁) adapterView R₁ n) (ρ n s)
      (MatchCallXR cls CVEquiv
        (recEvsOf (L := A.level) cls (alphaComp (Query := Query) A E₁) adapterView R₁ n)
        (fun s v r => XServe (L := A.level) (alphaComp (Query := Query) A E₁) adapterView reads R₁
          Allowed n s v r) (ρ n) s) :=
    fun n s => MatchCallXR.specP cls CVEquiv _ _ (ρ n) s
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree A.level reads (alphaComp (Query := Query) A E₁) (alphaComp (Query := Query) A E₂)
        (R₁.stmt j) :=
    fun j hj1 hjN hw => replay_hAWriteP (L := A.level) (reads := reads)
      (XS := fun n s v r => XServe (L := A.level) (alphaComp (Query := Query) A E₁) adapterView reads
        R₁ Allowed n s v r)
      hAs hCRS1 hTF1 hCT hFaith R₁ hNTI hSBC hRuns hCS j hj1 hjN
      (by obtain ⟨o', ho'⟩ := hw; rw [ho']; exact Option.some_ne_none _)
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
        (fun n s c v r c' h => (hspecP n s).counts c v r c' h)
        (fun n s hs => MatchCallXR.spec cls CVEquiv _ _ (ρ n) s (hRuns.readId n s hs))
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
    hAWrite hReadRes
  exact ⟨h.1, ⟨h.2.1, h.2.2⟩, h.1, ⟨h.2.1, h.2.2⟩⟩

end Module5
end Formalization
