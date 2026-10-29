/-
Module 3: segments — in-order write barriers, reorderable reads, **matched call by
call**.

The unit of replay matching is the adapter/driver *call*, never the turn. A node's
recording is the flat stream of its calls, each classified by method name as a
`read` or a `write` (`cls`). A *segment* is the stretch of the stream between two
write barriers. Replay keeps one number per node, `c`, the count of write barriers
consumed so far, and serves each live call individually:

* a live `write` call must match (op exactly, args up to `~_A`) the next write
  barrier — the recorded write call that has exactly `c` write calls before it;
* a live `read` call may match *any* recorded read call of the current segment —
  one with exactly `c` write calls before it — and is never consumed.

A turn (a `Statement`) only groups its calls: it fixes the order in which calls
are issued and supplies the one result the project's `next` sees, the result of the
turn's last call.

This file has two layers.

**Pure layer** (`Cls` … `turn_serve`). Combinatorics of the recording and the
replay, independent of any state or `Level`. The recording is a predicate on call
events (`InRec`); replay (`MatchAll`, `ServeTurn`, `ReplaySeg`,
`ConvergentReplaySeg`) is parametrized by the matcher for a single call, so
Module 4 reuses it with its cross-node rule added to the matcher.

**Semantic layer.** The recorded per-call results (`callResAt`), the call-level
state (`stateAtCall`), the bridges between states of `R₁` at call granularity, the
cross-engine read agreement (`crossReadAgree`), and `T2₂`/`T2₁`.

Hypotheses this module adds to Module 2's, and why:

* `ClsTruthful` — the classification is *truthful*: a call classified `read` has
  no target. A call classified `write` need not write (the implementation
  classifies unknown methods, and `execute`, as writes conservatively).
* `SameBarrierCount` — for every statement `R₁` realizes, the replaying engine's
  compilation issues as many write-classified calls as the recording engine's.
  Without it a live turn can *borrow* a neighbouring turn's write barrier, and
  the per-turn effect agreement the T2 core needs (`hAWrite`) does not follow.
  (Turn-level matching used to give this for free by matching a whole write turn
  to a whole recorded turn.)
* `CompiledReadsSound E₂` (`hCRS2`), as before.
-/

import Formalization.Module2

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Formalization
namespace Module3

open Formalization.Module1 hiding BehEquiv T2_1 T2_2 ReadsSound
open Formalization.Module1.Eqv hiding ObsEquiv BehEquiv
open Formalization.Module2 hiding T2_1 T2_2

/-! # Pure layer -/

/-- A method's classification: does the replay treat its calls as reads
(reorderable within a segment, never consumed) or as writes (barriers)? -/
inductive Cls where
  | read
  | write
  deriving DecidableEq

section Pure

variable {FQN Query Relation MethodName Args : Type}

/-- The call with this view is a write barrier. -/
def isW (cls : MethodName → Cls) (v : CallView MethodName Args) : Bool :=
  decide (cls v.op = Cls.write)

/-- The number of write barriers among a list of call views. -/
def nw (cls : MethodName → Cls) (vs : List (CallView MethodName Args)) : Nat :=
  (vs.filter (isW cls)).length

theorem nw_nil (cls : MethodName → Cls) : nw cls ([] : List (CallView MethodName Args)) = 0 := rfl

theorem nw_append (cls : MethodName → Cls) (a b : List (CallView MethodName Args)) :
    nw cls (a ++ b) = nw cls a + nw cls b := by
  simp [nw, List.filter_append]

theorem nw_cons (cls : MethodName → Cls) (v : CallView MethodName Args)
    (vs : List (CallView MethodName Args)) :
    nw cls (v :: vs) = (if isW cls v = true then 1 else 0) + nw cls vs := by
  by_cases h : isW cls v = true
  · simp [nw, h]; omega
  · simp [nw, h]

theorem nw_take_succ (cls : MethodName → Cls) (vs : List (CallView MethodName Args)) (k : Nat)
    (v : CallView MethodName Args) (h : vs[k]? = some v) :
    nw cls (vs.take (k + 1)) = nw cls (vs.take k) + (if isW cls v = true then 1 else 0) := by
  rw [List.take_add_one, h, nw_append]
  by_cases hw : isW cls v = true
  · simp [nw, hw]
  · simp [nw, hw]

theorem nw_take_le (cls : MethodName → Cls) (vs : List (CallView MethodName Args)) (k : Nat) :
    nw cls (vs.take k) ≤ nw cls vs := by
  conv => rhs; rw [← List.take_append_drop k vs]
  rw [nw_append]; omega

/-- A write at index `k` is not yet counted by the prefix before it. -/
theorem nw_take_lt (cls : MethodName → Cls) (vs : List (CallView MethodName Args)) (k : Nat)
    (v : CallView MethodName Args) (h : vs[k]? = some v) (hw : isW cls v = true) :
    nw cls (vs.take k) < nw cls vs := by
  have h1 := nw_take_succ cls vs k v h
  have h2 := nw_take_le cls vs (k + 1)
  rw [h1] at h2; simp [hw] at h2; omega

/-- The `u`-th write of `vs` is the one at index `k`, where `u` counts the writes before it. -/
theorem filter_getElem_of_write (cls : MethodName → Cls) :
    ∀ (vs : List (CallView MethodName Args)) (k : Nat) (v : CallView MethodName Args),
      vs[k]? = some v → isW cls v = true →
      (vs.filter (isW cls))[nw cls (vs.take k)]? = some v
  | [], k, v, h, _ => by simp at h
  | a :: rest, 0, v, h, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [nw, hw]
  | a :: rest, k + 1, v, h, hw => by
    simp only [List.getElem?_cons_succ] at h
    have ih := filter_getElem_of_write cls rest k v h hw
    by_cases ha : isW cls a = true
    · have : nw cls ((a :: rest).take (k + 1)) = nw cls (rest.take k) + 1 := by
        rw [List.take_succ_cons, nw_cons]; simp [ha]; omega
      rw [this]
      simp [ha, ih]
    · have : nw cls ((a :: rest).take (k + 1)) = nw cls (rest.take k) := by
        rw [List.take_succ_cons, nw_cons]; simp [ha]
      rw [this]
      simp [ha, ih]

/-! ## The recording -/

/-- One recorded call: its view, its result, and its *segment number* — the number
of write calls before it in the node's call stream. A write call's segment number is
its barrier number. -/
structure RecEv (MethodName Args Relation : Type) where
  view : CallView MethodName Args
  res : Result Relation
  seg : Nat

/-- The number of write calls in the first `t` recorded turns of `L`. -/
def Wt (cls : MethodName → Cls)
    (recV : Statement FQN Query → List (CallView MethodName Args))
    (L : History FQN Query Relation) (t : Nat) : Nat :=
  ((L.take t).map (fun x => nw cls (recV x.1))).sum

theorem Wt_succ_of (cls : MethodName → Cls)
    (recV : Statement FQN Query → List (CallView MethodName Args))
    (L : History FQN Query Relation) (t : Nat) (x : Statement FQN Query × Result Relation)
    (h : L[t]? = some x) : Wt cls recV L (t + 1) = Wt cls recV L t + nw cls (recV x.1) := by
  simp only [Wt, List.take_add_one, h, Option.toList_some, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem Wt_succ_none (cls : MethodName → Cls)
    (recV : Statement FQN Query → List (CallView MethodName Args))
    (L : History FQN Query Relation) (t : Nat) (h : L[t]? = none) :
    Wt cls recV L (t + 1) = Wt cls recV L t := by
  simp only [Wt, List.take_add_one, h, Option.toList_none, List.append_nil]

theorem Wt_mono (cls : MethodName → Cls)
    (recV : Statement FQN Query → List (CallView MethodName Args))
    (L : History FQN Query Relation) {t t' : Nat} (h : t ≤ t') :
    Wt cls recV L t ≤ Wt cls recV L t' := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    cases hm : L[m]? with
    | none => rw [Wt_succ_none cls recV L m hm]; exact ih
    | some x => rw [Wt_succ_of cls recV L m x hm]; omega

/-- `e` is a recorded call of `L`: the `k`-th call of the compilation (under `recV`) of the
statement of recorded turn `t`; its result is `cr t k` and its segment number counts
the write calls before it. -/
def InRec (cls : MethodName → Cls)
    (recV : Statement FQN Query → List (CallView MethodName Args))
    (cr : Nat → Nat → Result Relation) (L : History FQN Query Relation)
    (e : RecEv MethodName Args Relation) : Prop :=
  ∃ t s r k v, L[t]? = some (s, r) ∧ (recV s)[k]? = some v ∧
    e = ⟨v, cr t k, Wt cls recV L t + nw cls ((recV s).take k)⟩

/-- A recorded *write* call whose barrier number falls inside recorded turn `t`'s range
`[Wt t, Wt (t+1))` is one of turn `t`'s own write calls. -/
theorem InRec.write_in_turn {cls : MethodName → Cls}
    {recV : Statement FQN Query → List (CallView MethodName Args)}
    {cr : Nat → Nat → Result Relation} {L : History FQN Query Relation}
    {e : RecEv MethodName Args Relation} (he : InRec cls recV cr L e)
    (hw : isW cls e.view = true) {t : Nat} {s : Statement FQN Query} {r : Result Relation}
    (hLt : L[t]? = some (s, r))
    (hlo : Wt cls recV L t ≤ e.seg) (hhi : e.seg < Wt cls recV L (t + 1)) :
    ∃ k, (recV s)[k]? = some e.view ∧ e.res = cr t k ∧
      e.seg = Wt cls recV L t + nw cls ((recV s).take k) := by
  obtain ⟨t', s', r', k', v', hLt', hk', rfl⟩ := he
  simp only at hw hlo hhi ⊢
  rcases Nat.lt_trichotomy t' t with hlt | heq | hgt
  · exfalso
    have h1 := nw_take_lt cls (recV s') k' v' hk' hw
    have h2 := Wt_succ_of cls recV L t' (s', r') hLt'
    have h3 := Wt_mono cls recV L (show t' + 1 ≤ t by omega)
    simp only at h2
    omega
  · subst heq
    rw [hLt] at hLt'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hLt')
    exact ⟨k', hk', rfl, rfl⟩
  · exfalso
    have h3 := Wt_mono cls recV L (show t + 1 ≤ t' by omega)
    omega

/-! ## Replay, call by call -/

section Replay

variable {Nodes : Type}

/-- **The call matcher.** Serve one live call (view `v`) when `c` write barriers have been
consumed, from the recorded calls `F`: a result `r` and the new barrier count `c'`.

* A live `write` must match (`m`: op exactly, args up to `~_A`) the next write barrier —
  the recorded write call with exactly `c` write calls before it; the count advances.
* A live `read` may match any recorded read call of the current segment (exactly `c`
  write calls before it). Reads are never consumed, so the count stays. -/
def MatchCall (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop) (c : Nat) (v : CallView MethodName Args)
    (r : Result Relation) (c' : Nat) : Prop :=
  (isW cls v = true → ∃ e, F e ∧ isW cls e.view = true ∧ e.seg = c ∧ m v e.view ∧
      r = e.res ∧ c' = c + 1) ∧
  (isW cls v = false → ∃ e, F e ∧ isW cls e.view = false ∧ e.seg = c ∧ m v e.view ∧
      r = e.res ∧ c' = c)

/-- Every call of a list is served, in order. -/
inductive MatchAll
    (mc : Nat → CallView MethodName Args → Result Relation → Nat → Prop) :
    Nat → List (CallView MethodName Args) → Nat → Prop
  | nil {c : Nat} : MatchAll mc c [] c
  | cons {c : Nat} {v : CallView MethodName Args} {r : Result Relation} {c₁ : Nat}
      {vs : List (CallView MethodName Args)} {c' : Nat} :
      mc c v r c₁ → MatchAll mc c₁ vs c' → MatchAll mc c (v :: vs) c'

/-- A turn's calls are served in order; the turn's result is the result served for its last
call (and a turn with no calls is not replayable). -/
def ServeTurn (mc : Nat → CallView MethodName Args → Result Relation → Nat → Prop)
    (c : Nat) (vs : List (CallView MethodName Args)) (r : Result Relation) (c' : Nat) : Prop :=
  ∃ vs₀ v c₀, vs = vs₀ ++ [v] ∧ MatchAll mc c vs₀ c₀ ∧ mc c₀ v r c'

/-- Node `n`'s replayed history and barrier count after `k` of its turns. A turn exists only
if `next` returned a statement for the history so far, and its calls were served. -/
inductive ReplaySeg (P : Project Nodes FQN Query Relation) (n : Nodes)
    (liveV : Statement FQN Query → List (CallView MethodName Args))
    (mc : Statement FQN Query → Nat → CallView MethodName Args → Result Relation → Nat → Prop) :
    Nat → History FQN Query Relation → Nat → Prop
  | zero : ReplaySeg P n liveV mc 0 [] 0
  | step {k : Nat} {H : History FQN Query Relation} {c c' : Nat} {stmt : Statement FQN Query}
      {r : Result Relation} :
      ReplaySeg P n liveV mc k H c → P.nxt n H = some stmt →
      ServeTurn (mc stmt) c (liveV stmt) r c' →
      ReplaySeg P n liveV mc (k + 1) (H ++ [(stmt, r)]) c'

/-- A replay of every turn of `n`, reproducing the recording `L` up to `~`, after which `next`
is done and no recorded write barrier is left unconsumed. -/
def ConvergentReplaySeg [Setoid Relation] (cls : MethodName → Cls)
    (P : Project Nodes FQN Query Relation) (n : Nodes)
    (liveV : Statement FQN Query → List (CallView MethodName Args))
    (mc : Statement FQN Query → Nat → CallView MethodName Args → Result Relation → Nat → Prop)
    (F : RecEv MethodName Args Relation → Prop) (L : History FQN Query Relation) : Prop :=
  ∃ K H c, ReplaySeg P n liveV mc K H c ∧ HistEquiv H L ∧ P.nxt n H = none ∧
    ∀ e, F e → isW cls e.view = true → e.seg < c

variable {P : Project Nodes FQN Query Relation} {n : Nodes}
  {liveV : Statement FQN Query → List (CallView MethodName Args)}
  {mc : Statement FQN Query → Nat → CallView MethodName Args → Result Relation → Nat → Prop}

theorem ReplaySeg.length {k : Nat} {H : History FQN Query Relation} {c : Nat}
    (hrep : ReplaySeg P n liveV mc k H c) : H.length = k := by
  induction hrep with
  | zero => rfl
  | @step k H c c' stmt r hprev hnxt hserve ih =>
      rw [List.length_append, ih, List.length_singleton]

theorem ReplaySeg.step_inv {k : Nat} {H' : History FQN Query Relation} {c' : Nat}
    (h : ReplaySeg P n liveV mc (k + 1) H' c') :
    ∃ H c stmt r, ReplaySeg P n liveV mc k H c ∧ P.nxt n H = some stmt ∧
      ServeTurn (mc stmt) c (liveV stmt) r c' ∧ H' = H ++ [(stmt, r)] := by
  cases h with
  | step hprev hnxt hserve => exact ⟨_, _, _, _, hprev, hnxt, hserve, rfl⟩

theorem ReplaySeg.prefix {K : Nat} {H : History FQN Query Relation} {c : Nat}
    (hrep : ReplaySeg P n liveV mc K H c) :
    ∀ k, k ≤ K → ∃ c', ReplaySeg P n liveV mc k (H.take k) c' := by
  induction hrep with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst this
      exact ⟨0, by simpa using ReplaySeg.zero⟩
  | @step k₀ prev cur₀ cur' stmt r hprev hnxt hserve ih =>
      intro k hk
      rcases Nat.lt_or_ge k (k₀ + 1) with hlt | hge
      · obtain ⟨c'', hprefix⟩ := ih k (by omega)
        have hlen : prev.length = k₀ := ReplaySeg.length hprev
        rw [List.take_append_of_le_length (by omega)]
        exact ⟨c'', hprefix⟩
      · have hkeq : k = k₀ + 1 := by omega
        subst hkeq
        have hlen : (prev ++ [(stmt, r)]).length = k₀ + 1 := by
          rw [List.length_append, ReplaySeg.length hprev, List.length_singleton]
        rw [List.take_of_length_le (by omega)]
        exact ⟨cur', .step hprev hnxt hserve⟩

/-- Every matcher advances the barrier count by one on a write call and by nothing on a read. -/
def CountsBarriers (cls : MethodName → Cls)
    (mc : Statement FQN Query → Nat → CallView MethodName Args → Result Relation → Nat → Prop) :
    Prop :=
  ∀ stmt c v r c', mc stmt c v r c' → c' = c + (if isW cls v = true then 1 else 0)

theorem MatchAll.count {cls : MethodName → Cls}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hcnt : ∀ c v r c', mc' c v r c' → c' = c + (if isW cls v = true then 1 else 0))
    {c : Nat} {vs : List (CallView MethodName Args)} {c' : Nat}
    (h : MatchAll mc' c vs c') : c' = c + nw cls vs := by
  induction h with
  | nil => simp [nw_nil]
  | @cons c v r c₁ vs c' hm hrest ih =>
    rw [ih, hcnt c v r c₁ hm, nw_cons]; omega

theorem ServeTurn.count {cls : MethodName → Cls}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hcnt : ∀ c v r c', mc' c v r c' → c' = c + (if isW cls v = true then 1 else 0))
    {c : Nat} {vs : List (CallView MethodName Args)} {r : Result Relation} {c' : Nat}
    (h : ServeTurn mc' c vs r c') : c' = c + nw cls vs := by
  obtain ⟨vs₀, v, c₀, rfl, hall, hlast⟩ := h
  rw [hcnt c₀ v r c' hlast, MatchAll.count hcnt hall, nw_append]
  have : nw cls [v] = (if isW cls v = true then 1 else 0) := by
    rw [nw_cons, nw_nil]; omega
  rw [this]; omega

theorem ReplaySeg.count {cls : MethodName → Cls} (hcnt : CountsBarriers cls mc)
    {k : Nat} {H : History FQN Query Relation} {c : Nat}
    (hrep : ReplaySeg P n liveV mc k H c) :
    c = (H.map (fun x => nw cls (liveV x.1))).sum := by
  induction hrep with
  | zero => rfl
  | @step k H c c' stmt r hprev hnxt hserve ih =>
    rw [ServeTurn.count (hcnt stmt) hserve, ih]
    simp

/-- **Replay of each recorded turn.** A convergent replay serves recorded turn `t` (statement
`s`) from the barrier count `Wt t` — the write calls of the turns before it — to `Wt (t+1)`,
and the result it serves is `~` the recorded one. The barrier count is pinned to the recording
by `SameBarrierCount`-style hypothesis `hSBC`: the replaying engine issues as many writes for
`s` as the recording engine did. -/
theorem turn_serve [Setoid Relation] {cls : MethodName → Cls}
    {recV : Statement FQN Query → List (CallView MethodName Args)}
    {cr : Nat → Nat → Result Relation} {L : History FQN Query Relation}
    (hcnt : CountsBarriers cls mc) (hNTI : NextTildeInsensitive P)
    (hLnxt : ∀ (t : Nat) (s : Statement FQN Query) (r : Result Relation),
      L[t]? = some (s, r) → P.nxt n (L.take t) = some s)
    (hSBC : ∀ (t : Nat) (s : Statement FQN Query) (r : Result Relation),
      L[t]? = some (s, r) → nw cls (liveV s) = nw cls (recV s))
    (hc : ConvergentReplaySeg cls P n liveV mc (InRec cls recV cr L) L) :
    ∀ (t : Nat) (s : Statement FQN Query) (r : Result Relation), L[t]? = some (s, r) →
      ∃ r', ServeTurn (mc s) (Wt cls recV L t) (liveV s) r' (Wt cls recV L (t + 1)) ∧
        ResEquiv r' r := by
  obtain ⟨K, H, c, hrep, hHL, -, -⟩ := hc
  intro t s r hLt
  have hlenHL : H.length = L.length := LForall₂.length_eq hHL
  have hK : K = L.length := by rw [← ReplaySeg.length hrep, hlenHL]
  have htlt : t < L.length := (List.getElem?_eq_some_iff.mp hLt).1
  obtain ⟨c1, hrep1⟩ := ReplaySeg.prefix hrep (t + 1) (by omega)
  obtain ⟨H₀, c₀, stmt, r₀, hrep0, hnxt0, hserve, hH1⟩ := ReplaySeg.step_inv hrep1
  have hlen0 : H₀.length = t := ReplaySeg.length hrep0
  have hH₀ : H₀ = H.take t := by
    have h1 : (H.take (t + 1)).take t = H.take t := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [hH1, List.take_left' hlen0] at h1
    exact h1
  have hequiv : HistEquiv H₀ (L.take t) := by rw [hH₀]; exact LForall₂.take hHL t
  have hnxt' : P.nxt n H₀ = some s := by
    rw [hNTI n H₀ (L.take t) hequiv]; exact hLnxt t s r hLt
  have hstmt : stmt = s := Option.some.inj (hnxt0.symm.trans hnxt')
  subst hstmt
  -- the barrier count after `t` turns
  have hc0 : c₀ = Wt cls recV L t := by
    rw [ReplaySeg.count hcnt hrep0]
    unfold Wt
    refine LForall₂.sum_eq hequiv ?_
    intro a b hab hb
    obtain ⟨t', ht'⟩ := List.mem_iff_getElem?.mp hb
    have hLt' : L[t']? = some b := by
      rw [List.getElem?_take] at ht'
      by_cases h : t' < t
      · simpa [h] using ht'
      · simp [h] at ht'
    rw [hab.1]
    exact hSBC t' b.1 b.2 hLt'
  have hc1 : c1 = Wt cls recV L (t + 1) := by
    rw [ServeTurn.count (hcnt _) hserve, hc0, Wt_succ_of cls recV L t (stmt, r) hLt, hSBC t stmt r hLt]
  rw [hc0, hc1] at hserve
  refine ⟨r₀, hserve, ?_⟩
  have hHt : H[t]? = some (stmt, r₀) := by
    have h2 : (H.take (t + 1))[t]? = some (stmt, r₀) := by
      rw [hH1, List.getElem?_append_right (by omega), hlen0]; simp
    rwa [List.getElem?_take_of_lt (by omega)] at h2
  exact (LForall₂.get hHL t _ _ hHt hLt).2

/-! ### What a matcher must provide

`MatcherSpec` is the interface the extraction lemmas need of a call matcher: a live write is
served by a recorded write barrier (and consumes it), a live read leaves the barrier count
alone. `MatchCall` meets it; so does Module 4's matcher, which adds a cross-node fallback
for reads. -/

structure MatcherSpec (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop)
    (mc : Nat → CallView MethodName Args → Result Relation → Nat → Prop) : Prop where
  write : ∀ c v r c', mc c v r c' → isW cls v = true →
    ∃ e, F e ∧ isW cls e.view = true ∧ e.seg = c ∧ m v e.view ∧ r = e.res ∧ c' = c + 1
  read : ∀ c v r c', mc c v r c' → isW cls v = false → c' = c

theorem MatcherSpec.counts {cls : MethodName → Cls}
    {m : CallView MethodName Args → CallView MethodName Args → Prop}
    {F : RecEv MethodName Args Relation → Prop}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hs : MatcherSpec cls m F mc') :
    ∀ c v r c', mc' c v r c' → c' = c + (if isW cls v = true then 1 else 0) := by
  intro c v r c' h
  by_cases hw : isW cls v = true
  · obtain ⟨-, -, -, -, -, -, hc⟩ := hs.write c v r c' h hw
    simp [hw, hc]
  · have hw' : isW cls v = false := by simpa using hw
    simp [hw, hs.read c v r c' h hw']

theorem MatchCall.spec (cls : MethodName → Cls)
    (m : CallView MethodName Args → CallView MethodName Args → Prop)
    (F : RecEv MethodName Args Relation → Prop) :
    MatcherSpec cls m F (MatchCall cls m F) where
  write := fun c v r c' h hw => by
    obtain ⟨e, hF, hew, hseg, hm, hr, hc'⟩ := h.1 hw
    exact ⟨e, hF, hew, hseg, hm, hr, hc'⟩
  read := fun c v r c' h hw => by
    obtain ⟨e, -, -, -, -, -, hc'⟩ := h.2 hw
    exact hc'

theorem MatchAll.snoc {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    {c : Nat} {vs : List (CallView MethodName Args)} {c₀ : Nat} (h : MatchAll mc' c vs c₀)
    {v : CallView MethodName Args} {r : Result Relation} {c' : Nat} (hl : mc' c₀ v r c') :
    MatchAll mc' c (vs ++ [v]) c' := by
  induction h with
  | nil => exact .cons hl .nil
  | cons hm hrest ih => exact .cons hm (ih hl)

theorem ServeTurn.matchAll {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    {c : Nat} {vs : List (CallView MethodName Args)} {r : Result Relation} {c' : Nat}
    (h : ServeTurn mc' c vs r c') : MatchAll mc' c vs c' := by
  obtain ⟨vs₀, v, c₀, rfl, hall, hlast⟩ := h
  exact hall.snoc hlast

/-- Each write call of a served turn, numbered `u` among the turn's writes, is served by the
recorded write barrier number `c + u`. -/
theorem MatchAll.writes {cls : MethodName → Cls}
    {m : CallView MethodName Args → CallView MethodName Args → Prop}
    {F : RecEv MethodName Args Relation → Prop}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hs : MatcherSpec cls m F mc')
    {c : Nat} {vs : List (CallView MethodName Args)} {c' : Nat}
    (h : MatchAll mc' c vs c') :
    ∀ (u : Nat) (w : CallView MethodName Args), (vs.filter (isW cls))[u]? = some w →
      ∃ e, F e ∧ isW cls e.view = true ∧ e.seg = c + u ∧ m w e.view := by
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
        exact ⟨e', hF', hew', by rw [hseg', hc₁]; omega, hm'⟩
    · have hv' : isW cls v = false := by simpa using hv
      have hc₁ := hs.read c v r c₁ hm hv'
      simp only [List.filter_cons, hv] at hw
      obtain ⟨e', hF', hew', hseg', hm'⟩ := ih u w hw
      exact ⟨e', hF', hew', by rw [hseg', hc₁], hm'⟩

theorem nw_eq_zero_iff (cls : MethodName → Cls) (vs : List (CallView MethodName Args)) :
    nw cls vs = 0 ↔ ∀ v ∈ vs, isW cls v = false := by
  unfold nw
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · intro h v hv; simpa using h v hv
  · intro h v hv; simp [h v hv]

/-! ### Where a matched read sits relative to the live turn

A live turn `t` runs between barrier counts `Wt t` and `Wt (t+1)`. A recorded read it is
served from carries a segment number in that range, which pins down where in the recording
the read lies: before turn `t`, after it, or within it — and, outside it, that nothing
between the read and turn `t` is a write barrier. -/

theorem InRec.read_before {cls : MethodName → Cls}
    {recV : Statement FQN Query → List (CallView MethodName Args)}
    {L : History FQN Query Relation}
    {t₀ t k₀ : Nat} {s₀ : Statement FQN Query} {r₀ : Result Relation}
    (hLt₀ : L[t₀]? = some (s₀, r₀))
    {c₀ : Nat} (hseg : c₀ = Wt cls recV L t₀ + nw cls ((recV s₀).take k₀))
    (hlo : Wt cls recV L t ≤ c₀) (hlt : t₀ < t) :
    nw cls ((recV s₀).drop k₀) = 0 ∧
      ∀ s' (x : Statement FQN Query × Result Relation), t₀ < s' → s' < t → L[s']? = some x →
        nw cls (recV x.1) = 0 := by
  have h1 := Wt_succ_of cls recV L t₀ (s₀, r₀) hLt₀
  have h2 := Wt_mono cls recV L (show t₀ + 1 ≤ t by omega)
  have h3 : nw cls (recV s₀) = nw cls ((recV s₀).take k₀) + nw cls ((recV s₀).drop k₀) := by
    rw [← nw_append, List.take_append_drop]
  simp only at h1
  refine ⟨by omega, ?_⟩
  intro s' x hs1 hs2 hx
  have h4 := Wt_mono cls recV L (show t₀ + 1 ≤ s' by omega)
  have h5 := Wt_succ_of cls recV L s' x hx
  have h6 := Wt_mono cls recV L (show s' + 1 ≤ t by omega)
  omega

theorem InRec.read_after {cls : MethodName → Cls}
    {recV : Statement FQN Query → List (CallView MethodName Args)}
    {L : History FQN Query Relation}
    {t₀ t k₀ : Nat} {s₀ : Statement FQN Query}
    {c₀ : Nat} (hseg : c₀ = Wt cls recV L t₀ + nw cls ((recV s₀).take k₀))
    (hhi : c₀ ≤ Wt cls recV L (t + 1)) (hgt : t < t₀) :
    nw cls ((recV s₀).take k₀) = 0 ∧
      ∀ s' (x : Statement FQN Query × Result Relation), t < s' → s' < t₀ → L[s']? = some x →
        nw cls (recV x.1) = 0 := by
  have h2 := Wt_mono cls recV L (show t + 1 ≤ t₀ by omega)
  refine ⟨by omega, ?_⟩
  intro s' x hs1 hs2 hx
  have h4 := Wt_mono cls recV L (show t + 1 ≤ s' by omega)
  have h5 := Wt_succ_of cls recV L s' x hx
  have h6 := Wt_mono cls recV L (show s' + 1 ≤ t₀ by omega)
  omega

/-- **The write calls of a served turn are the recorded turn's write calls**, one to one and in
order, up to `CVEquiv` — given that the two engines issue as many writes for the statement. -/
theorem write_views_match [Setoid Args] {cls : MethodName → Cls}
    {recV liveV : Statement FQN Query → List (CallView MethodName Args)}
    {cr : Nat → Nat → Result Relation} {L : History FQN Query Relation}
    {t : Nat} {s : Statement FQN Query} {rr r' : Result Relation}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hspec : MatcherSpec cls CVEquiv (InRec cls recV cr L) mc')
    (hLt : L[t]? = some (s, rr)) (hSBC : nw cls (liveV s) = nw cls (recV s))
    (hserve : ServeTurn mc' (Wt cls recV L t) (liveV s) r' (Wt cls recV L (t + 1))) :
    LForall₂ CVEquiv ((liveV s).filter (isW cls)) ((recV s).filter (isW cls)) := by
  have hwr := MatchAll.writes hspec hserve.matchAll
  have hsucc := Wt_succ_of cls recV L t _ hLt
  have hlen : ((liveV s).filter (isW cls)).length = ((recV s).filter (isW cls)).length := hSBC
  refine LForall₂.of_getElem? _ _ hlen ?_
  intro u w w' hw hw'
  obtain ⟨e, hF, hew, hseg, hm⟩ := hwr u w hw
  have hulen : u < ((liveV s).filter (isW cls)).length := (List.getElem?_eq_some_iff.mp hw).1
  obtain ⟨k, hk, -, hsegk⟩ := InRec.write_in_turn hF hew hLt (by omega)
    (by simp only [nw] at hsucc hlen; omega)
  have h1 := filter_getElem_of_write cls (recV s) k e.view hk hew
  have h2 : nw cls ((recV s).take k) = u := by omega
  rw [h2] at h1
  rw [h1] at hw'
  rw [← Option.some.inj hw']
  exact hm

/-- **What the last call of a served turn was served from.** The turn's result is the result
served for its last call `v`. If `v` is a write, it was served by the recorded turn's own write
barrier. If it is a read, it was served either by a recorded read `(t₀, k₀)` of the node's current
segment — and, by the barrier arithmetic, everything between that read and the live turn `t` is
not a write barrier — or by the matcher's other route `X` (Module 4's cross-node lookup). -/
theorem served_last [Setoid Args] {cls : MethodName → Cls}
    {recV liveV : Statement FQN Query → List (CallView MethodName Args)}
    {cr : Nat → Nat → Result Relation} {L : History FQN Query Relation}
    {t : Nat} {s : Statement FQN Query} {rr r' : Result Relation}
    {mc' : Nat → CallView MethodName Args → Result Relation → Nat → Prop}
    (hspec : MatcherSpec cls CVEquiv (InRec cls recV cr L) mc')
    (X : Nat → CallView MethodName Args → Result Relation → Nat → Prop)
    (hrd : ∀ c v r c', mc' c v r c' → isW cls v = false →
      (∃ e, InRec cls recV cr L e ∧ isW cls e.view = false ∧ e.seg = c ∧ CVEquiv v e.view ∧
        r = e.res) ∨ X c v r c')
    (hLt : L[t]? = some (s, rr))
    (hserve : ServeTurn mc' (Wt cls recV L t) (liveV s) r' (Wt cls recV L (t + 1))) :
    ∃ (vs₀ : List (CallView MethodName Args)) (v : CallView MethodName Args),
      liveV s = vs₀ ++ [v] ∧
      ((isW cls v = true ∧ ∃ (k₀ : Nat) (w : CallView MethodName Args),
          (recV s)[k₀]? = some w ∧ CVEquiv v w ∧ r' = cr t k₀) ∨
       (isW cls v = false ∧ ∃ (t₀ : Nat) (s₀ : Statement FQN Query) (r₀ : Result Relation)
          (k₀ : Nat) (w : CallView MethodName Args),
          L[t₀]? = some (s₀, r₀) ∧ (recV s₀)[k₀]? = some w ∧ CVEquiv v w ∧ r' = cr t₀ k₀ ∧
          ((t₀ < t ∧ nw cls ((recV s₀).drop k₀) = 0 ∧
              ∀ (s' : Nat) (x : Statement FQN Query × Result Relation), t₀ < s' → s' < t →
                L[s']? = some x → nw cls (recV x.1) = 0) ∨
            t₀ = t ∨
            (t < t₀ ∧ nw cls ((recV s₀).take k₀) = 0 ∧
              ∀ (s' : Nat) (x : Statement FQN Query × Result Relation), t < s' → s' < t₀ →
                L[s']? = some x → nw cls (recV x.1) = 0))) ∨
       (isW cls v = false ∧ X (Wt cls recV L t + nw cls vs₀) v r' (Wt cls recV L (t + 1)))) := by
  obtain ⟨vs₀, v, c₀, hvs, hall, hml⟩ := hserve
  refine ⟨vs₀, v, hvs, ?_⟩
  have hcount := MatchAll.count hspec.counts hall
  have hsucc := Wt_succ_of cls recV L t _ hLt
  have hnwl : nw cls (liveV s) = nw cls vs₀ + (if isW cls v = true then 1 else 0) := by
    rw [hvs, nw_append]
    have : nw cls [v] = (if isW cls v = true then 1 else 0) := by
      rw [nw_cons, nw_nil]; omega
    rw [this]
  by_cases hw : isW cls v = true
  · left
    refine ⟨hw, ?_⟩
    obtain ⟨e, hF, hew, hseg, hm, hr, hc'⟩ := hspec.write c₀ v r' _ hml hw
    obtain ⟨k, hk, hres, -⟩ := InRec.write_in_turn hF hew hLt (by omega)
      (by simp only [hw, ite_true] at hnwl; simp only at hsucc; omega)
    exact ⟨k, e.view, hk, hm, by rw [hr, hres]⟩
  · have hw' : isW cls v = false := by simpa using hw
    have hc' := hspec.read c₀ v r' _ hml hw'
    rcases hrd c₀ v r' _ hml hw' with ⟨e, hF, hew, hseg, hm, hr⟩ | hX
    · right; left
      refine ⟨hw', ?_⟩
      obtain ⟨t₀, s₀, r₀, k₀, w, hLt₀, hk₀, he⟩ := hF
      have hseg' : c₀ = Wt cls recV L t₀ + nw cls ((recV s₀).take k₀) := by
        rw [he] at hseg; exact hseg.symm
      have hres : r' = cr t₀ k₀ := by rw [hr, he]
      have hview : CVEquiv v w := by rw [he] at hm; exact hm
      have hlo : Wt cls recV L t ≤ c₀ := by omega
      have hhi : c₀ ≤ Wt cls recV L (t + 1) := by
        simp only [hw', Bool.false_eq_true, ite_false] at hnwl; simp only at hsucc; omega
      refine ⟨t₀, s₀, r₀, k₀, w, hLt₀, hk₀, hview, hres, ?_⟩
      rcases Nat.lt_trichotomy t₀ t with hlt | heq | hgt
      · exact Or.inl ⟨hlt, InRec.read_before hLt₀ hseg' hlo hlt⟩
      · exact Or.inr (Or.inl heq)
      · exact Or.inr (Or.inr ⟨hgt, InRec.read_after hseg' hhi hgt⟩)
    · right; right
      exact ⟨hw', by rw [← hcount]; exact hX⟩

end Replay

end Pure

/-! # Semantic layer

From here on a call is a call of a `Level` (the driver level or an adapter level), compiled by
an engine (`comp`), and viewed at the boundary through `view`. -/

section Sem

variable {Nodes FQN Query Relation MethodName Args : Type} [DecidableEq FQN] [DecidableEq Nodes]

/-- **The classification is truthful** for the level `L`: a call whose method the map
classifies as `read` has no target — it never changes state. The converse is not required:
a call classified `write` need not write. -/
def ClsTruthful (L : Level FQN Relation) (cls : MethodName → Cls)
    (view : L.Call → CallView MethodName Args) : Prop :=
  ∀ c : L.Call, cls (view c).op = Cls.read → L.target c = none

/-- **The two engines issue as many write calls per statement.** For every statement `R₁`
realizes, the replaying engine's compilation (`liveV`) has as many write-classified calls as the
recording engine's (`recV`). -/
def SameBarrierCount (cls : MethodName → Cls)
    (liveV recV : Statement FQN Query → List (CallView MethodName Args))
    (N : Nat) (stmt : Nat → Statement FQN Query) : Prop :=
  ∀ j, 1 ≤ j → j ≤ N → nw cls (liveV (stmt j)) = nw cls (recV (stmt j))

/-! ## State at call granularity -/

/-- The state just before call `k` of the turn at position `j`. -/
def stateAtCall {L : Level FQN Relation} (comp : Comp FQN Query Relation L)
    (stmt : Nat → Statement FQN Query) (S₀ : State FQN Relation) (j k : Nat) :
    State FQN Relation :=
  ((comp (stmt j)).take k).foldl L.step (stateAtL comp stmt S₀ j)

omit [DecidableEq FQN] in
theorem stateAtCall_prefix {L : Level FQN Relation} {comp : Comp FQN Query Relation L}
    (hL : LevelPreserve L) (stmt : Nat → Statement FQN Query) (S₀ : State FQN Relation)
    (j k : Nat) (o : FQN) (h : ∀ c ∈ (comp (stmt j)).take k, L.target c ≠ some o) :
    stateAtCall comp stmt S₀ j k o = stateAtL comp stmt S₀ j o :=
  foldl_step_preserve L hL o _ _ h

theorem stateAtCall_suffix {L : Level FQN Relation} {comp : Comp FQN Query Relation L}
    (hL : LevelPreserve L) (stmt : Nat → Statement FQN Query) (S₀ : State FQN Relation)
    (j k : Nat) (hj : 1 ≤ j) (o : FQN)
    (h : ∀ c ∈ (comp (stmt j)).drop k, L.target c ≠ some o) :
    stateAtL comp stmt S₀ (j + 1) o = stateAtCall comp stmt S₀ j k o := by
  rw [Gen.stateAt_succ (comp := comp) stmt S₀ j hj]
  unfold execL stateAtCall
  conv => lhs; rw [← List.take_append_drop k (comp (stmt j)), List.foldl_append]
  exact foldl_step_preserve L hL o _ _ h

/-- The state is unchanged on `o` across a range of turns none of whose calls targets `o`. -/
theorem stateAtL_const_calls {L : Level FQN Relation} {comp : Comp FQN Query Relation L}
    (hL : LevelPreserve L) (stmt : Nat → Statement FQN Query) (S₀ : State FQN Relation)
    (o : FQN) (i₁ : Nat) (hi₁ : 1 ≤ i₁) :
    ∀ d, (∀ s, i₁ ≤ s → s < i₁ + d → ∀ c ∈ comp (stmt s), L.target c ≠ some o) →
      stateAtL comp stmt S₀ (i₁ + d) o = stateAtL comp stmt S₀ i₁ o
  | 0, _ => rfl
  | d + 1, h => by
    have hd : stateAtL comp stmt S₀ (i₁ + d) o = stateAtL comp stmt S₀ i₁ o :=
      stateAtL_const_calls hL stmt S₀ o i₁ hi₁ d (fun s hs1 hs2 => h s hs1 (by omega))
    have hstep : stateAtL comp stmt S₀ (i₁ + d + 1) =
        execL comp (stateAtL comp stmt S₀ (i₁ + d)) (stmt (i₁ + d)) :=
      Gen.stateAt_succ stmt S₀ (i₁ + d) (by omega)
    have : i₁ + (d + 1) = i₁ + d + 1 := by omega
    rw [this, hstep]
    unfold execL
    rw [foldl_step_preserve L hL o _ _ (h (i₁ + d) (by omega) (by omega)), hd]

/-- **State agreement within `R`, at call granularity.** Between two turns `i₁ ≤ i₂`, the state on
`o` is unchanged when no call of node `n`'s own turns in between targets `o`, provided `o` is read
by a turn of node `n` at or before `i₁` (`DAGOrder` puts every *other* node's write to `o` before
that turn). -/
theorem stateAt_agree_calls {L : Level FQN Relation} {comp : Comp FQN Query Relation L}
    {P : Project Nodes FQN Query Relation} {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    {reads : Statement FQN Query → FQN → Prop}
    (R : LiveRun P E ret S₀) (hL : LevelPreserve L) (hTF : TargetFaithfulL comp)
    (hDAG : DAGOrder reads R) (n : Nodes) (a₀ : Nat) (ha₁ : 1 ≤ a₀) (haN : a₀ ≤ R.N)
    (hanode : R.node a₀ = n) {i₁ i₂ : Nat} (hai : a₀ ≤ i₁) (h12 : i₁ ≤ i₂)
    (h2N : i₂ ≤ R.N + 1) (o : FQN) (hro : reads (R.stmt a₀) o)
    (hnw : ∀ s, i₁ ≤ s → s < i₂ → R.node s = n → ∀ c ∈ comp (R.stmt s), L.target c ≠ some o) :
    stateAtL comp R.stmt S₀ i₂ o = stateAtL comp R.stmt S₀ i₁ o := by
  have hkey := stateAtL_const_calls (comp := comp) hL R.stmt S₀ o i₁ (by omega) (i₂ - i₁) ?_
  · rwa [show i₁ + (i₂ - i₁) = i₂ from by omega] at hkey
  · intro s hs1 hs2 c hc hct
    have hsN : s ≤ R.N := by omega
    by_cases hnode : R.node s = n
    · exact hnw s hs1 (by omega) hnode c hc hct
    · have hs1' : 1 ≤ s := by omega
      -- `c` targets `o`, so by target-faithfulness the statement does
      have hstmt : target (R.stmt s) = some o := by
        have := hTF (R.stmt s) c hc (by rw [hct]; simp)
        rw [← this]; exact hct
      have := hDAG a₀ ha₁ haN o hro s hs1' hsN (by rw [hanode]; exact hnode) hstmt
      omega

/-- `stateAt_agree_calls` with the statement-level condition on node `n`'s own turns: none of them
*targets* `o` (so, by target-faithfulness, none of their calls does). -/
theorem stateAt_agree_of_DAG {L : Level FQN Relation} {comp : Comp FQN Query Relation L}
    {P : Project Nodes FQN Query Relation} {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    {reads : Statement FQN Query → FQN → Prop}
    (R : LiveRun P E ret S₀) (hLP : LevelPreserve L) (hTF : TargetFaithfulL comp)
    (hDAG : DAGOrder reads R)
    {i₁ i₂ : Nat} (h1 : 1 ≤ i₁) (hi₁N : i₁ ≤ R.N) (h12 : i₁ ≤ i₂) (h2N : i₂ ≤ R.N + 1)
    (o : FQN) (hro : reads (R.stmt i₁) o)
    (hnw : ∀ j, i₁ ≤ j → j < i₂ → R.node j = R.node i₁ → target (R.stmt j) ≠ some o) :
    stateAtL comp R.stmt S₀ i₂ o = stateAtL comp R.stmt S₀ i₁ o :=
  stateAt_agree_calls R hLP hTF hDAG (R.node i₁) i₁ h1 hi₁N rfl (Nat.le_refl i₁) h12 h2N o hro
    (fun s hs1 hs2 hsn c hc hct => by
      have hne : L.target c ≠ none := by rw [hct]; simp
      exact hnw s hs1 hs2 hsn (by rw [← hTF (R.stmt s) c hc hne]; exact hct))

/-! ## Recorded runs at a boundary -/

/-- A recorded run's answers at boundary `comp`: at every turn, the boundary's own evaluation
of the turn is `~_Res` to the recorded result. At the driver boundary it holds with equality from
`res_eq` (`resLink_driver`); at an adapter boundary it is `RunLinkT.res_link`. -/
def ResLink {P : Project Nodes FQN Query Relation} {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    [Setoid Relation] {L : Level FQN Relation}
    (comp : Comp FQN Query Relation L) (R : LiveRun P E ret S₀) : Prop :=
  ∀ i, 1 ≤ i → i ≤ R.N →
    ∃ r, rL comp (stateAtL comp R.stmt S₀ i) (R.stmt i) = some r ∧ ResEquiv r (R.res i)

theorem resLink_driver [Setoid Relation]
    {reads : Statement FQN Query → FQN → Prop}
    {P : Project Nodes FQN Query Relation} {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) :
    ResLink (L := driverLevel ret reads) (drvE E) R := fun i h1 h2 =>
  ⟨R.res i, (rL_driver ret reads E _ _).trans (R.res_eq i h1 h2), ResEquiv.refl _⟩

/-- Node `n`'s recording entry at raw position `j`, read off at `j`'s own turn index. -/
theorem recordingOf_get {P : Project Nodes FQN Query Relation}
    {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) (n : Nodes) (j : Nat) (hj1 : 1 ≤ j) (hjN : j ≤ R.N)
    (hjnode : R.node j = n) :
    (recordingOf R n)[turnCount R.node n j]? = some (R.stmt j, R.res j) := by
  have hstepEq : histAt R.node R.stmt R.res n (j + 1) =
      histAt R.node R.stmt R.res n j ++ [(R.stmt j, R.res j)] := by
    simp only [histAt, hj1, hjnode, and_self, ite_true]
  have h2 : (histAt R.node R.stmt R.res n (j + 1))[turnCount R.node n j]? =
      some (R.stmt j, R.res j) := by
    rw [hstepEq, ← turnCount_eq_length R.node R.stmt R.res n j,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hcountstep : turnCount R.node n (j + 1) = turnCount R.node n j + 1 := by
    simp only [turnCount, hj1, hjnode, and_self, ite_true]
  have h3 : histAt R.node R.stmt R.res n (j + 1) =
      (histAt R.node R.stmt R.res n (R.N + 1)).take (turnCount R.node n (j + 1)) :=
    histAt_prefix R.node R.stmt R.res n (by omega)
  unfold recordingOf
  rw [h3] at h2
  rwa [List.getElem?_take_of_lt (by omega)] at h2

/-- The converse: every recorded turn of `n` is the turn at some raw position of `n`. -/
theorem recordingOf_find {P : Project Nodes FQN Query Relation}
    {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) (n : Nodes) {t : Nat} {x : Statement FQN Query × Result Relation}
    (h : (recordingOf R n)[t]? = some x) :
    ∃ j, 1 ≤ j ∧ j ≤ R.N ∧ R.node j = n ∧ turnCount R.node n j = t ∧
      x = (R.stmt j, R.res j) := by
  have hlt : t < turnCount R.node n (R.N + 1) := by
    have := (List.getElem?_eq_some_iff.mp h).1
    unfold recordingOf at this
    rwa [turnCount_eq_length] at this
  obtain ⟨j, hjlt, hj1, hjnode, hjcount, hjentry⟩ :=
    histAt_find R.node R.stmt R.res n (R.N + 1) t hlt
  refine ⟨j, hj1, by omega, hjnode, hjcount, ?_⟩
  have : recordingOf R n = histAt R.node R.stmt R.res n (R.N + 1) := rfl
  rw [this, hjentry] at h
  exact (Option.some.inj h).symm

/-- `next` produces the recorded statement from the recorded history before it. -/
theorem recordingOf_nxt {P : Project Nodes FQN Query Relation}
    {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) (n : Nodes) {t : Nat} {s : Statement FQN Query}
    {r : Result Relation} (h : (recordingOf R n)[t]? = some (s, r)) :
    P.nxt n ((recordingOf R n).take t) = some s := by
  obtain ⟨j, hj1, hjN, hjnode, hjcount, hx⟩ := recordingOf_find R n h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  have h1 := R.stmt_eq j hj1 hjN
  rw [hjnode] at h1
  have h2 : (recordingOf R n).take (turnCount R.node n j) = histAt R.node R.stmt R.res n j := by
    unfold recordingOf
    rw [← histAt_prefix R.node R.stmt R.res n (show j ≤ R.N + 1 by omega)]
  rw [hjcount] at h2
  rw [h2]; exact h1

/-- The recorded result of call `k` of the turn at position `j`: the turn's own recorded result for
its last call, and for any other call the answer it was given by the boundary (`ok` if it
returns none). -/
def callResAt {L : Level FQN Relation} (comp : Comp FQN Query Relation L)
    (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation) (S₀ : State FQN Relation)
    (j k : Nat) : Result Relation :=
  if k + 1 = (comp (stmt j)).length then res j
  else
    match (comp (stmt j))[k]? with
    | some c =>
      match L.ans (stateAtCall comp stmt S₀ j k) c with
      | some y => Result.rel y
      | none => Result.ok
    | none => Result.ok

open Classical in
/-- The recorded results, indexed by node-local turn: the result of call `k` of `n`'s `t`-th turn. -/
noncomputable def recResOf {L : Level FQN Relation} (comp : Comp FQN Query Relation L)
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (S₀ : State FQN Relation) (N : Nat) (n : Nodes) (t k : Nat) : Result Relation :=
  if h : ∃ j, 1 ≤ j ∧ j ≤ N ∧ node j = n ∧ turnCount node n j = t then
    callResAt comp stmt res S₀ (Classical.choose h) k
  else Result.ok

omit [DecidableEq FQN] in
theorem recResOf_eq {L : Level FQN Relation} (comp : Comp FQN Query Relation L)
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (S₀ : State FQN Relation) (N : Nat) (n : Nodes) (j k : Nat) (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hn : node j = n) :
    recResOf comp node stmt res S₀ N n (turnCount node n j) k =
      callResAt comp stmt res S₀ j k := by
  have h : ∃ j', 1 ≤ j' ∧ j' ≤ N ∧ node j' = n ∧ turnCount node n j' = turnCount node n j :=
    ⟨j, hj1, hjN, hn, rfl⟩
  unfold recResOf
  rw [dif_pos h]
  obtain ⟨h1, -, h3, h4⟩ := Classical.choose_spec h
  have := turn_position_unique node n h1 h3 hj1 hn h4
  rw [this]

omit [DecidableEq FQN] in
/-- The recorded result of a turn's last call is the turn's own recorded result. -/
theorem recResOf_last {L : Level FQN Relation} (comp : Comp FQN Query Relation L)
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (S₀ : State FQN Relation) (N : Nat) (n : Nodes) (j k : Nat) (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hn : node j = n) (hlast : k + 1 = (comp (stmt j)).length) :
    recResOf comp node stmt res S₀ N n (turnCount node n j) k = res j := by
  rw [recResOf_eq comp node stmt res S₀ N n j k hj1 hjN hn]
  unfold callResAt
  simp [hlast]

/-- The recorded result of a call is the answer the boundary gave it. -/
theorem callResAt_spec {L : Level FQN Relation} {comp : Comp FQN Query Relation L}
    [Setoid Relation]
    (hL : LevelPreserve L) (hTF : TargetFaithfulL comp)
    {P : Project Nodes FQN Query Relation} {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) (hLink : ResLink comp R) {j k : Nat} (hj1 : 1 ≤ j) (hjN : j ≤ R.N)
    {a : L.Call} (ha : (comp (R.stmt j))[k]? = some a) {x : Relation}
    (hx : ResEquiv (callResAt comp R.stmt R.res S₀ j k) (Result.rel x)) :
    ∃ y, L.ans (stateAtCall comp R.stmt S₀ j k) a = some y ∧
      ResEquiv (Result.rel y) (callResAt comp R.stmt R.res S₀ j k) := by
  unfold callResAt at hx ⊢
  by_cases hlast : k + 1 = (comp (R.stmt j)).length
  · simp only [hlast, ite_true] at hx ⊢
    obtain ⟨r, hr, hrr⟩ := hLink j hj1 hjN
    cases hst : R.stmt j with
    | write o q =>
      exfalso
      rw [hst] at hr
      simp only [rL] at hr
      have hr' : r = Result.ok := (Option.some.inj hr).symm
      subst hr'
      have : R.res j = Result.ok := by
        cases hrj : R.res j with
        | ok => rfl
        | rel y => rw [hrj] at hrr; exact hrr.elim
      rw [this] at hx
      exact hx
    | read q =>
      rw [hst] at hr hlast ha
      simp only [rL] at hr
      have hlastc : (comp (Statement.read q)).getLast? = some a := by
        rw [List.getLast?_eq_getElem?, ← hlast]
        simpa using ha
      rw [hlastc] at hr
      simp only [Option.map_eq_some_iff] at hr
      obtain ⟨y, hy, rfl⟩ := hr
      have hstate : stateAtCall comp R.stmt S₀ j k = stateAtL comp R.stmt S₀ j := by
        funext o
        apply stateAtCall_prefix hL
        intro c hc
        have hcm : c ∈ comp (Statement.read q) := by
          have := List.mem_of_mem_take hc
          rwa [hst] at this
        have hnone : L.target c = none :=
          Classical.byContradiction fun hne => hne (hTF (Statement.read q) c hcm hne)
        rw [hnone]; simp
      refine ⟨y, ?_, hrr⟩
      rw [hstate]; exact hy
  · simp only [hlast, ite_false] at hx ⊢
    rw [ha] at hx ⊢
    simp only at hx ⊢
    cases hans : L.ans (stateAtCall comp R.stmt S₀ j k) a with
    | none => rw [hans] at hx; exact hx.elim
    | some y => exact ⟨y, rfl, ResEquiv.refl _⟩

omit [DecidableEq FQN] in
/-- Calls of a turn none of whose views is a write barrier have no target. -/
theorem quiet_of_nw_zero {L : Level FQN Relation} {cls : MethodName → Cls}
    {view : L.Call → CallView MethodName Args} (hCT : ClsTruthful L cls view)
    (cs : List L.Call) (h : nw cls (cs.map view) = 0) : ∀ c ∈ cs, L.target c = none := by
  intro c hc
  have hw := (nw_eq_zero_iff cls _).mp h (view c) (List.mem_map_of_mem hc)
  apply hCT c
  cases hcc : cls (view c).op with
  | read => rfl
  | write => simp [isW, hcc] at hw

/-- **Cross-engine read agreement, at call granularity.** A recorded call `a` — call `k₀` of the turn
at position `j₀` of `R₁` — and a live call `b` of the turn at `j'`, both of node `n`, are `≈`-related.
Then the answer `a` was given in `R₁` (at the state just before it) is `~_R` the answer `b` gets
at any state `S₂` that agrees with `R₁`'s state at `j'` on the reads of `j'`'s statement.

`hpos` says that nothing between the two calls, in node `n`'s own stream, is a write: the recorded
call lies before the live turn and everything from it up to the turn is quiet, or after it and
everything from the turn up to it is quiet, or in the live turn itself. `DAGOrder` handles the other
nodes. -/
theorem crossReadAgree [Setoid Relation] {L : Level FQN Relation} [Setoid L.Call]
    {comp₁ comp₂ : Comp FQN Query Relation L}
    {reads : Statement FQN Query → FQN → Prop}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (hCRS2 : CompiledReadsSoundL reads comp₂)
    (R₁ : LiveRun P E₁ ret S₀) (hTF1 : TargetFaithfulL comp₁) (hDAG : DAGOrder reads R₁)
    (n : Nodes) {j₀ j' k₀ : Nat} (hj₀1 : 1 ≤ j₀) (hj₀N : j₀ ≤ R₁.N) (hj₀node : R₁.node j₀ = n)
    (hj'1 : 1 ≤ j') (hj'N : j' ≤ R₁.N) (hj'node : R₁.node j' = n)
    {a b : L.Call} (ha : (comp₁ (R₁.stmt j₀))[k₀]? = some a) (hbm : b ∈ comp₂ (R₁.stmt j'))
    (hab : a ≈ b)
    (hpos :
      (j₀ < j' ∧ (∀ c ∈ (comp₁ (R₁.stmt j₀)).drop k₀, L.target c = none) ∧
        (∀ s, j₀ < s → s < j' → R₁.node s = n → ∀ c ∈ comp₁ (R₁.stmt s), L.target c = none)) ∨
      (j' < j₀ ∧ (∀ c ∈ (comp₁ (R₁.stmt j₀)).take k₀, L.target c = none) ∧
        (∀ s, j' ≤ s → s < j₀ → R₁.node s = n → ∀ c ∈ comp₁ (R₁.stmt s), L.target c = none)) ∨
      (j₀ = j' ∧ ∀ c ∈ comp₁ (R₁.stmt j'), L.target c = none))
    (S₂ : State FQN Relation)
    (hSagree : ∀ o, reads (R₁.stmt j') o →
      OptEquiv (stateAtL comp₁ R₁.stmt S₀ j' o) (S₂ o))
    {ya yb : Relation}
    (h1 : L.ans (stateAtCall comp₁ R₁.stmt S₀ j₀ k₀) a = some ya)
    (h2 : L.ans S₂ b = some yb) : ya ≈ yb := by
  have ha_mem : a ∈ comp₁ (R₁.stmt j₀) := List.mem_of_getElem? ha
  have hstep2 : OptEquiv (L.ans (stateAtL comp₁ R₁.stmt S₀ j') b) (L.ans S₂ b) :=
    hL.ans_sound b _ _ (fun o ho => hSagree o (hCRS2 (R₁.stmt j') b hbm o ho))
  have hnotarget : ∀ {cs : List L.Call} {o : FQN}, (∀ c ∈ cs, L.target c = none) →
      ∀ c ∈ cs, L.target c ≠ some o := by
    intro cs o h c hc; rw [h c hc]; simp
  have hfin : OptEquiv (L.ans (stateAtCall comp₁ R₁.stmt S₀ j₀ k₀) a)
      (L.ans (stateAtL comp₁ R₁.stmt S₀ j') b) := by
    rcases hpos with ⟨hlt, hsuf, hmid⟩ | ⟨hlt, hpre, hmid⟩ | ⟨rfl, hq⟩
    · have hbridge : ∀ o, L.reads a o →
          OptEquiv (stateAtCall comp₁ R₁.stmt S₀ j₀ k₀ o) (stateAtL comp₁ R₁.stmt S₀ j' o) := by
        intro o ho
        have hro : reads (R₁.stmt j₀) o := hCRS1 _ a ha_mem o ho
        have e1 := stateAtCall_suffix hL.preserve R₁.stmt S₀ j₀ k₀ hj₀1 o (hnotarget hsuf)
        have e2 := stateAt_agree_calls (comp := comp₁) R₁ hL.preserve hTF1 hDAG n j₀ hj₀1 hj₀N
          hj₀node (Nat.le_succ j₀) (show j₀ + 1 ≤ j' by omega) (by omega) o hro
          (fun s hs1 hs2 hsn => hnotarget (hmid s (by omega) hs2 hsn))
        rw [← e1, e2]; exact OptEquiv.refl _
      exact OptEquiv.trans (hL.ans_sound a _ _ hbridge)
        (hL.ans_congr a b hab (stateAtL comp₁ R₁.stmt S₀ j'))
    · have hbridge : ∀ o, L.reads b o →
          OptEquiv (stateAtCall comp₁ R₁.stmt S₀ j₀ k₀ o) (stateAtL comp₁ R₁.stmt S₀ j' o) := by
        intro o ho
        have hro : reads (R₁.stmt j') o := hCRS2 _ b hbm o ho
        have e1 := stateAtCall_prefix hL.preserve R₁.stmt S₀ j₀ k₀ o (hnotarget hpre)
        have e2 := stateAt_agree_calls (comp := comp₁) R₁ hL.preserve hTF1 hDAG n j' hj'1 hj'N
          hj'node (Nat.le_refl j') (Nat.le_of_lt hlt) (by omega) o hro
          (fun s hs1 hs2 hsn => hnotarget (hmid s hs1 hs2 hsn))
        rw [e1, e2]; exact OptEquiv.refl _
      exact OptEquiv.trans (hL.ans_congr a b hab (stateAtCall comp₁ R₁.stmt S₀ j₀ k₀))
        (hL.ans_sound b _ _ hbridge)
    · have hstate : stateAtCall comp₁ R₁.stmt S₀ j₀ k₀ = stateAtL comp₁ R₁.stmt S₀ j₀ := by
        funext o
        exact stateAtCall_prefix hL.preserve R₁.stmt S₀ j₀ k₀ o
          (hnotarget (fun c hc => hq c (List.mem_of_mem_take hc)))
      rw [hstate]
      exact hL.ans_congr a b hab (stateAtL comp₁ R₁.stmt S₀ j₀)
  have hchain := OptEquiv.trans hfin hstep2
  rw [h1, h2] at hchain
  exact hchain

/-! ## What a convergent replay gives the T2 core -/

/-- The recorded calls of node `n` of `R₁` at the boundary `comp₁`/`view`. -/
abbrev recEvsOf {L : Level FQN Relation} (cls : MethodName → Cls)
    (comp₁ : Comp FQN Query Relation L) (view : L.Call → CallView MethodName Args)
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (n : Nodes) : RecEv MethodName Args Relation → Prop :=
  InRec cls (fun s => (comp₁ s).map view)
    (recResOf comp₁ R₁.node R₁.stmt R₁.res S₀ R₁.N n) (recordingOf R₁ n)

/-- **Every node's recording is replayed by the replaying engine's calls, call by call**, with the
call matcher `mc` (it may depend on the node and on the statement the call belongs to). -/
def ReplayWith [Setoid Relation] [Setoid Args] {L : Level FQN Relation} (cls : MethodName → Cls)
    (comp₁ comp₂ : Comp FQN Query Relation L) (view : L.Call → CallView MethodName Args)
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀)
    (mc : Nodes → Statement FQN Query → Nat → CallView MethodName Args → Result Relation →
      Nat → Prop) : Prop :=
  ∀ n, ConvergentReplaySeg cls P n (fun s => (comp₂ s).map view) (mc n)
    (recEvsOf cls comp₁ view R₁ n) (recordingOf R₁ n)

/-- The replay of Module 3: the matcher is `MatchCall`. -/
abbrev ReplayOK [Setoid Relation] [Setoid Args] {L : Level FQN Relation} (cls : MethodName → Cls)
    (comp₁ comp₂ : Comp FQN Query Relation L) (view : L.Call → CallView MethodName Args)
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) : Prop :=
  ReplayWith cls comp₁ comp₂ view R₁ (fun n _ => MatchCall cls CVEquiv (recEvsOf cls comp₁ view R₁ n))

omit [DecidableEq FQN] in
theorem effCalls_filter_write {L : Level FQN Relation} {cls : MethodName → Cls}
    {view : L.Call → CallView MethodName Args} (hCT : ClsTruthful L cls view)
    (cs : List L.Call) :
    effCalls L (cs.filter (isW cls ∘ view)) = effCalls L cs := by
  unfold effCalls
  rw [List.filter_filter]
  apply List.filter_congr
  intro c _
  by_cases hs : (L.target c).isSome = true
  · have hw : isW cls (view c) = true := by
      cases hcc : cls (view c).op with
      | write => simp [isW, hcc]
      | read => have := hCT c hcc; rw [this] at hs; simp at hs
    simp [hs, hw, Function.comp]
  · simp [hs]

/-- The call-level step of a recorded turn: the replay serves recorded turn `t` of node `n`
(the turn at position `j`) from barrier count `Wt t` to `Wt (t+1)`, with a result `~` the recorded
one. -/
theorem turn_at [Setoid Relation] [Setoid Args] {L : Level FQN Relation} {cls : MethodName → Cls}
    {comp₁ comp₂ : Comp FQN Query Relation L} {view : L.Call → CallView MethodName Args}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    {mc : Nodes → Statement FQN Query → Nat → CallView MethodName Args → Result Relation →
      Nat → Prop}
    (R₁ : LiveRun P E₁ ret S₀) (hNTI : NextTildeInsensitive P)
    (hcnt : ∀ n, CountsBarriers cls (mc n))
    (hSBC : SameBarrierCount cls (fun s => (comp₂ s).map view) (fun s => (comp₁ s).map view)
      R₁.N R₁.stmt)
    (hCS : ReplayWith cls comp₁ comp₂ view R₁ mc) {j : Nat} (hj1 : 1 ≤ j) (hjN : j ≤ R₁.N) :
    ∃ r', ServeTurn (mc (R₁.node j) (R₁.stmt j))
        (Wt cls (fun s => (comp₁ s).map view) (recordingOf R₁ (R₁.node j))
          (turnCount R₁.node (R₁.node j) j))
        ((comp₂ (R₁.stmt j)).map view) r'
        (Wt cls (fun s => (comp₁ s).map view) (recordingOf R₁ (R₁.node j))
          (turnCount R₁.node (R₁.node j) j + 1)) ∧
      ResEquiv r' (R₁.res j) := by
  have hLt := recordingOf_get R₁ (R₁.node j) j hj1 hjN rfl
  exact turn_serve (mc := mc (R₁.node j))
    (hcnt _) hNTI
    (fun t s r h => recordingOf_nxt R₁ (R₁.node j) h)
    (fun t s r h => by
      obtain ⟨j', hj'1, hj'N, -, -, hx⟩ := recordingOf_find R₁ (R₁.node j) h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
      exact hSBC j' hj'1 hj'N)
    (hCS (R₁.node j)) _ _ _ hLt

/-- **`hAWrite`, from a convergent replay.** For a write turn, the calls of the two engines that
have an effect are `~`-related pairwise: the live engine's write barriers are matched one to one
with the recorded turn's own, in order. -/
theorem replay_hAWrite_with [Setoid Relation] [Setoid Args] {L : Level FQN Relation} [Setoid L.Call]
    {cls : MethodName → Cls}
    {comp₁ comp₂ : Comp FQN Query Relation L} {view : L.Call → CallView MethodName Args}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    {mc : Nodes → Statement FQN Query → Nat → CallView MethodName Args → Result Relation →
      Nat → Prop}
    (hL : LevelSoundT L) (hCT : ClsTruthful L cls view)
    (hFaith : ∀ c c' : L.Call, CVEquiv (view c) (view c') → c ≈ c')
    (R₁ : LiveRun P E₁ ret S₀) (hNTI : NextTildeInsensitive P)
    (hspec : ∀ n s, MatcherSpec cls CVEquiv (recEvsOf cls comp₁ view R₁ n) (mc n s))
    (hSBC : SameBarrierCount cls (fun s => (comp₂ s).map view) (fun s => (comp₁ s).map view)
      R₁.N R₁.stmt)
    (hCS : ReplayWith cls comp₁ comp₂ view R₁ mc) :
    ∀ j, 1 ≤ j → j ≤ R₁.N →
      LForall₂ (· ≈ ·) (effCalls L (comp₁ (R₁.stmt j))) (effCalls L (comp₂ (R₁.stmt j))) := by
  intro j hj1 hjN
  obtain ⟨r', hserve, -⟩ := turn_at R₁ hNTI
    (fun n stmt c v r c' h => (hspec n stmt).counts c v r c' h) hSBC hCS hj1 hjN
  have hLt := recordingOf_get R₁ (R₁.node j) j hj1 hjN rfl
  have hforall := write_views_match (cls := cls) (recV := fun s => (comp₁ s).map view)
    (liveV := fun s => (comp₂ s).map view)
    (cr := recResOf comp₁ R₁.node R₁.stmt R₁.res S₀ R₁.N (R₁.node j))
    (hspec _ _) hLt (hSBC j hj1 hjN) hserve
  -- to calls of the level
  rw [List.filter_map, List.filter_map] at hforall
  have hcalls := (LForall₂.of_map hforall).imp (fun a b h => hFaith a b h)
  have hcalls' := LForall₂.symm (fun hh => Setoid.symm hh) hcalls
  have := effCalls_congr hL hcalls'
  rw [effCalls_filter_write hCT, effCalls_filter_write hCT] at this
  exact this

theorem turnCount_lt_of_lt {node : Nat → Nodes} (n : Nodes) {j₀ j : Nat} (h1 : 1 ≤ j₀)
    (hn : node j₀ = n) (hlt : j₀ < j) : turnCount node n j₀ < turnCount node n j := by
  have hstep : turnCount node n (j₀ + 1) = turnCount node n j₀ + 1 := by
    simp only [turnCount, h1, hn, and_self, ite_true]
  have := turnCount_mono node n (show j₀ + 1 ≤ j by omega)
  omega

theorem lt_of_turnCount_lt {node : Nat → Nodes} (n : Nodes) {j₀ j : Nat}
    (h : turnCount node n j₀ < turnCount node n j) : j₀ < j := by
  rcases Nat.lt_or_ge j₀ j with hlt | hge
  · exact hlt
  · have := turnCount_mono node n hge
    omega

omit [DecidableEq FQN] in
theorem rL_last {L : Level FQN Relation} {comp : Comp FQN Query Relation L}
    {S : State FQN Relation} {q : Query} {b : L.Call} {r : Result Relation}
    (hb : (comp (Statement.read q)).getLast? = some b)
    (h : rL comp S (Statement.read q) = some r) :
    ∃ y, L.ans S b = some y ∧ r = Result.rel y := by
  simp only [rL, hb, Option.map_eq_some_iff] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, hy, rfl⟩

/-- **`hReadRes`, from a convergent replay.** The result `R₁` recorded for a read turn `j` is `~` the
result any run of the replaying engine at a state agreeing with `R₁`'s on `j`'s reads obtains for
its last call: the replay served that call from a recorded call of the same segment, and nothing
between the two is a write barrier.

The matcher `mc` may have a route `X` besides the local segment (Module 4's cross-node lookup); `hX`
says that a last call served by `X` is also sound. For Module 3's own matcher `X` is empty. -/
theorem replay_hReadRes_with [Setoid Relation] [Setoid Args] {L : Level FQN Relation}
    [Setoid L.Call] {cls : MethodName → Cls}
    {comp₁ comp₂ : Comp FQN Query Relation L} {view : L.Call → CallView MethodName Args}
    {reads : Statement FQN Query → FQN → Prop}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    {mc : Nodes → Statement FQN Query → Nat → CallView MethodName Args → Result Relation →
      Nat → Prop}
    (X : Nodes → Statement FQN Query → Nat → CallView MethodName Args → Result Relation →
      Nat → Prop)
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (hCRS2 : CompiledReadsSoundL reads comp₂)
    (hCT : ClsTruthful L cls view)
    (hFaith : ∀ c c' : L.Call, CVEquiv (view c) (view c') → c ≈ c')
    (R₁ : LiveRun P E₁ ret S₀) (hTF1 : TargetFaithfulL comp₁) (hDAG : DAGOrder reads R₁)
    (hLink : ResLink comp₁ R₁) (hNTI : NextTildeInsensitive P)
    (hcnt : ∀ n, CountsBarriers cls (mc n))
    (hspec : ∀ n s, target s = none →
      MatcherSpec cls CVEquiv (recEvsOf cls comp₁ view R₁ n) (mc n s))
    (hrd : ∀ n s c v r c', mc n s c v r c' → isW cls v = false →
      (∃ e, recEvsOf cls comp₁ view R₁ n e ∧ isW cls e.view = false ∧ e.seg = c ∧
        CVEquiv v e.view ∧ r = e.res) ∨ X n s c v r c')
    (hSBC : SameBarrierCount cls (fun s => (comp₂ s).map view) (fun s => (comp₁ s).map view)
      R₁.N R₁.stmt)
    (hCS : ReplayWith cls comp₁ comp₂ view R₁ mc)
    (hX : ∀ (j : Nat) (S₂ : State FQN Relation) (b : L.Call) (yb : Relation)
      (r' : Result Relation) (c₀ c' : Nat), 1 ≤ j → j ≤ R₁.N → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' → OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (S₂ o')) →
      (comp₂ (R₁.stmt j)).getLast? = some b → L.ans S₂ b = some yb →
      ResEquiv r' (R₁.res j) → X (R₁.node j) (R₁.stmt j) c₀ (view b) r' c' →
      ResEquiv (R₁.res j) (Result.rel yb)) :
    ∀ (j : Nat) (S₂ : State FQN Relation) (r₂ : Result Relation), 1 ≤ j → j ≤ R₁.N →
      target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' → OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (S₂ o')) →
      rL comp₂ S₂ (R₁.stmt j) = some r₂ → ResEquiv (R₁.res j) r₂ := by
  intro j S₂ r₂ hj1 hjN hread hSag h2
  obtain ⟨q, hq⟩ : ∃ q, R₁.stmt j = Statement.read q := by
    cases hst : R₁.stmt j with
    | write o q => rw [hst] at hread; simp [target] at hread
    | read q => exact ⟨q, rfl⟩
  have hquiet : ∀ c ∈ comp₁ (R₁.stmt j), L.target c = none := fun c hc =>
    Classical.byContradiction fun hne => hne (by
      have := hTF1 (R₁.stmt j) c hc hne
      rw [this]; exact hread)
  obtain ⟨r', hserve, hconv⟩ := turn_at R₁ hNTI hcnt hSBC hCS hj1 hjN
  have hLt := recordingOf_get R₁ (R₁.node j) j hj1 hjN rfl
  obtain ⟨vs₀, v, hvs, hcases⟩ := served_last (cls := cls) (recV := fun s => (comp₁ s).map view)
    (liveV := fun s => (comp₂ s).map view)
    (cr := recResOf comp₁ R₁.node R₁.stmt R₁.res S₀ R₁.N (R₁.node j))
    (hspec _ _ hread) (X (R₁.node j) (R₁.stmt j)) (hrd _ _) hLt hserve
  -- the live last call
  obtain ⟨cs₀, b, hcs, hbv⟩ : ∃ (cs₀ : List L.Call) (b : L.Call),
      comp₂ (R₁.stmt j) = cs₀ ++ [b] ∧ view b = v := by
    obtain ⟨l₁, l₂, hl, -, hl2⟩ := List.map_eq_append_iff.mp hvs
    obtain ⟨b, rfl, hb⟩ := List.map_eq_singleton_iff.mp hl2
    exact ⟨l₁, b, hl, hb⟩
  have hbmem : b ∈ comp₂ (R₁.stmt j) := by rw [hcs]; simp
  have hblast : (comp₂ (Statement.read q)).getLast? = some b := by rw [← hq, hcs]; simp
  rw [hq] at h2
  obtain ⟨yb, hyb, rfl⟩ := rL_last hblast h2
  -- the shared tail: any recorded call `(j₀, k₀)` with the quietness facts
  have key : ∀ (j₀ k₀ : Nat) (a : L.Call), 1 ≤ j₀ → j₀ ≤ R₁.N → R₁.node j₀ = R₁.node j →
      (comp₁ (R₁.stmt j₀))[k₀]? = some a → CVEquiv (view b) (view a) →
      r' = callResAt comp₁ R₁.stmt R₁.res S₀ j₀ k₀ →
      ((j₀ < j ∧ (∀ c ∈ (comp₁ (R₁.stmt j₀)).drop k₀, L.target c = none) ∧
        (∀ s, j₀ < s → s < j → R₁.node s = R₁.node j → ∀ c ∈ comp₁ (R₁.stmt s),
          L.target c = none)) ∨
      (j < j₀ ∧ (∀ c ∈ (comp₁ (R₁.stmt j₀)).take k₀, L.target c = none) ∧
        (∀ s, j ≤ s → s < j₀ → R₁.node s = R₁.node j → ∀ c ∈ comp₁ (R₁.stmt s),
          L.target c = none)) ∨
      (j₀ = j ∧ ∀ c ∈ comp₁ (R₁.stmt j), L.target c = none)) →
      ResEquiv (R₁.res j) (Result.rel yb) := by
    intro j₀ k₀ a hj₀1 hj₀N hj₀n ha hview hr' hpos
    have hab : a ≈ b := Setoid.symm (hFaith b a hview)
    obtain ⟨rl, hrl, hrlr⟩ := hLink j hj1 hjN
    obtain ⟨x, hx⟩ : ∃ x, R₁.res j = Result.rel x := by
      rw [hq] at hrl
      simp only [rL] at hrl
      cases hg : (comp₁ (Statement.read q)).getLast? with
      | none => rw [hg] at hrl; simp at hrl
      | some c =>
        rw [hg] at hrl
        simp only [Option.map_eq_some_iff] at hrl
        obtain ⟨y, -, rfl⟩ := hrl
        cases hrj : R₁.res j with
        | ok => rw [hrj] at hrlr; exact hrlr.elim
        | rel x => exact ⟨x, rfl⟩
    have hx' : ResEquiv (callResAt comp₁ R₁.stmt R₁.res S₀ j₀ k₀) (Result.rel x) := by
      rw [← hr', ← hx]; exact hconv
    obtain ⟨ya, h1, hya⟩ := callResAt_spec hL.preserve hTF1 R₁ hLink hj₀1 hj₀N ha hx'
    have hyy : ya ≈ yb := crossReadAgree hL hCRS1 hCRS2 R₁ hTF1 hDAG (R₁.node j) hj₀1 hj₀N hj₀n
      hj1 hjN rfl ha hbmem hab hpos S₂ hSag h1 hyb
    have hsym : ResEquiv (Result.rel x) (callResAt comp₁ R₁.stmt R₁.res S₀ j₀ k₀) := by
      rw [← hr', ← hx]; exact ResEquiv.symm hconv
    rw [hx]
    exact ResEquiv.trans hsym (ResEquiv.trans (ResEquiv.symm hya) hyy)
  rcases hcases with ⟨hw, k₀, w, hk₀, hm, hres⟩ |
      ⟨hw, t₀, s₀, r₀, k₀, w, hLt₀, hk₀, hm, hres, hpos'⟩ | ⟨hw, hXc⟩
  · -- a write barrier: served by the recorded turn's own write call
    obtain ⟨a, ha, hav⟩ : ∃ a, (comp₁ (R₁.stmt j))[k₀]? = some a ∧ view a = w := by
      simpa [List.getElem?_map, Option.map_eq_some_iff] using hk₀
    refine key j k₀ a hj1 hjN rfl ha (by rw [hbv, hav]; exact hm) ?_
      (Or.inr (Or.inr ⟨rfl, hquiet⟩))
    rw [hres]
    exact recResOf_eq comp₁ R₁.node R₁.stmt R₁.res S₀ R₁.N (R₁.node j) j k₀ hj1 hjN rfl
  · -- a read of the current segment
    obtain ⟨j₀, hj₀1, hj₀N, hj₀n, hj₀t, hx₀⟩ := recordingOf_find R₁ (R₁.node j) hLt₀
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx₀
    obtain ⟨a, ha, hav⟩ : ∃ a, (comp₁ (R₁.stmt j₀))[k₀]? = some a ∧ view a = w := by
      simpa [List.getElem?_map, Option.map_eq_some_iff] using hk₀
    have hres' : r' = callResAt comp₁ R₁.stmt R₁.res S₀ j₀ k₀ := by
      rw [hres, ← hj₀t]
      exact recResOf_eq comp₁ R₁.node R₁.stmt R₁.res S₀ R₁.N (R₁.node j) j₀ k₀ hj₀1 hj₀N hj₀n
    have hview : CVEquiv (view b) (view a) := by rw [hbv, hav]; exact hm
    have hquietS : ∀ {s : Nat}, 1 ≤ s → s ≤ R₁.N → R₁.node s = R₁.node j →
        ∀ {t' : Nat}, turnCount R₁.node (R₁.node j) s = t' →
        ∀ (hz : nw cls ((comp₁ (R₁.stmt s)).map view) = 0), ∀ c ∈ comp₁ (R₁.stmt s),
          L.target c = none := by
      intro s _ _ _ _ _ hz
      exact quiet_of_nw_zero hCT _ hz
    rcases hpos' with ⟨hlt, hsuf, hmid⟩ | heq | ⟨hgt, hpre, hmid⟩
    · have hjlt : j₀ < j := lt_of_turnCount_lt (node := R₁.node) (R₁.node j) (by rw [hj₀t]; exact hlt)
      refine key j₀ k₀ a hj₀1 hj₀N hj₀n ha hview hres' (Or.inl ⟨hjlt, ?_, ?_⟩)
      · apply quiet_of_nw_zero hCT
        rw [List.map_drop]; exact hsuf
      · intro s hs1 hs2 hsn
        have ht1 : turnCount R₁.node (R₁.node j) j₀ < turnCount R₁.node (R₁.node j) s :=
          turnCount_lt_of_lt (R₁.node j) hj₀1 hj₀n hs1
        have ht2 : turnCount R₁.node (R₁.node j) s < turnCount R₁.node (R₁.node j) j :=
          turnCount_lt_of_lt (R₁.node j) (by omega) hsn hs2
        have hLs := recordingOf_get R₁ (R₁.node j) s (by omega) (by omega) hsn
        exact quiet_of_nw_zero hCT _ (hmid _ (R₁.stmt s, R₁.res s) (by omega) ht2 hLs)
    · have hj₀j : j₀ = j :=
        turn_position_unique R₁.node (R₁.node j) hj₀1 hj₀n hj1 rfl (hj₀t.trans heq)
      exact key j₀ k₀ a hj₀1 hj₀N hj₀n ha hview hres' (Or.inr (Or.inr ⟨hj₀j, hquiet⟩))
    · have hjgt : j < j₀ := lt_of_turnCount_lt (node := R₁.node) (R₁.node j) (by rw [hj₀t]; exact hgt)
      refine key j₀ k₀ a hj₀1 hj₀N hj₀n ha hview hres' (Or.inr (Or.inl ⟨hjgt, ?_, ?_⟩))
      · apply quiet_of_nw_zero hCT
        rw [List.map_take]; exact hpre
      · intro s hs1 hs2 hsn
        rcases Nat.eq_or_lt_of_le hs1 with hsj | hsj
        · rw [← hsj]; exact hquiet
        · have ht1 : turnCount R₁.node (R₁.node j) j < turnCount R₁.node (R₁.node j) s :=
            turnCount_lt_of_lt (R₁.node j) hj1 rfl hsj
          have ht2 : turnCount R₁.node (R₁.node j) s < turnCount R₁.node (R₁.node j) j₀ :=
            turnCount_lt_of_lt (R₁.node j) (by omega) hsn hs2
          have hLs := recordingOf_get R₁ (R₁.node j) s (by omega) (by omega) hsn
          exact quiet_of_nw_zero hCT _ (hmid _ (R₁.stmt s, R₁.res s) ht1 (by omega) hLs)
  · -- a read served by the matcher's other route
    exact hX j S₂ b yb r' _ _ hj1 hjN hread hSag (by rw [hcs]; simp) hyb hconv
      (by rw [hbv]; exact hXc)

/-- `replay_hAWrite_with` for Module 3's own matcher. -/
theorem replay_hAWrite [Setoid Relation] [Setoid Args] {L : Level FQN Relation} [Setoid L.Call]
    {cls : MethodName → Cls}
    {comp₁ comp₂ : Comp FQN Query Relation L} {view : L.Call → CallView MethodName Args}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (hL : LevelSoundT L) (hCT : ClsTruthful L cls view)
    (hFaith : ∀ c c' : L.Call, CVEquiv (view c) (view c') → c ≈ c')
    (R₁ : LiveRun P E₁ ret S₀) (hNTI : NextTildeInsensitive P)
    (hSBC : SameBarrierCount cls (fun s => (comp₂ s).map view) (fun s => (comp₁ s).map view)
      R₁.N R₁.stmt)
    (hCS : ReplayOK cls comp₁ comp₂ view R₁) :
    ∀ j, 1 ≤ j → j ≤ R₁.N →
      LForall₂ (· ≈ ·) (effCalls L (comp₁ (R₁.stmt j))) (effCalls L (comp₂ (R₁.stmt j))) :=
  replay_hAWrite_with hL hCT hFaith R₁ hNTI
    (fun _ _ => MatchCall.spec cls CVEquiv _) hSBC hCS

/-- `replay_hReadRes_with` for Module 3's own matcher: no second route. -/
theorem replay_hReadRes [Setoid Relation] [Setoid Args] {L : Level FQN Relation} [Setoid L.Call]
    {cls : MethodName → Cls}
    {comp₁ comp₂ : Comp FQN Query Relation L} {view : L.Call → CallView MethodName Args}
    {reads : Statement FQN Query → FQN → Prop}
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (hCRS2 : CompiledReadsSoundL reads comp₂)
    (hCT : ClsTruthful L cls view)
    (hFaith : ∀ c c' : L.Call, CVEquiv (view c) (view c') → c ≈ c')
    (R₁ : LiveRun P E₁ ret S₀) (hTF1 : TargetFaithfulL comp₁) (hDAG : DAGOrder reads R₁)
    (hLink : ResLink comp₁ R₁) (hNTI : NextTildeInsensitive P)
    (hSBC : SameBarrierCount cls (fun s => (comp₂ s).map view) (fun s => (comp₁ s).map view)
      R₁.N R₁.stmt)
    (hCS : ReplayOK cls comp₁ comp₂ view R₁) :
    ∀ (j : Nat) (S₂ : State FQN Relation) (r₂ : Result Relation), 1 ≤ j → j ≤ R₁.N →
      target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' → OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (S₂ o')) →
      rL comp₂ S₂ (R₁.stmt j) = some r₂ → ResEquiv (R₁.res j) r₂ :=
  replay_hReadRes_with (fun _ _ _ _ _ _ => False) hL hCRS1 hCRS2 hCT hFaith R₁ hTF1 hDAG hLink hNTI
    (fun n stmt c v r c' h => (MatchCall.spec cls CVEquiv _).counts c v r c' h)
    (fun n _ _ => MatchCall.spec cls CVEquiv _)
    (fun n s c v r c' h hw => Or.inl (by
      obtain ⟨e, hF, hew, hseg, hm, hr, -⟩ := h.2 hw
      exact ⟨e, hF, hew, hseg, hm, hr⟩))
    hSBC hCS (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hXc => hXc.elim)

end Sem

/-! ## T2₂ / T2₁ under call-by-call segmented matching

The T2 core (`Module2.T2_of_A`, `Eqv.T2_adapter`) takes two halves: `hAWrite` (write turns: the calls
that have an effect agree) and `hReadRes` (read turns: the result agrees). `replay_hAWrite` and
`replay_hReadRes` supply them from a convergent replay of every node, at any boundary; `T2₂` runs them
at the driver boundary and `T2₁` at an adapter boundary. -/

/-- **T2₂ (Cross-engine conformance via `adapter→driver` recording, segmented, call by call).** -/
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
    (cls : MethodName → Cls) (hCT : ClsTruthful (driverLevel ret reads) cls driverView)
    (hSBC : SameBarrierCount cls (callsB E₂ adapterView driverView Boundary.adapterDriver)
      (callsB E₁ adapterView driverView Boundary.adapterDriver) R₁.N R₁.stmt)
    (hCS : ReplayOK (L := driverLevel ret reads) cls (drvE E₁) (drvE E₂) driverView R₁) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have hLT := driverLevel_soundT hRS hRC hTP
  have hCRS1L := driverLevel_compiledReadsSound (ret := ret) hCRS1
  have hCRS2L := driverLevel_compiledReadsSound (ret := ret) hCRS2
  have hTF1L := driverLevel_targetFaithful (ret := ret) (reads := reads) hTF1
  have hLink : ResLink (L := driverLevel ret reads) (drvE E₁) R₁ := resLink_driver R₁
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      LForall₂ (· ≈ ·) (effCalls (driverLevel ret reads) (drvE E₁ (R₁.stmt j)))
        (effCalls (driverLevel ret reads) (drvE E₂ (R₁.stmt j))) :=
    fun j hj1 hjN _ => replay_hAWrite hLT hCT hDVF R₁ hNTI hSBC hCS j hj1 hjN
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
    exact replay_hReadRes hLT hCRS1L hCRS2L hCT hDVF R₁ hTF1L hDAG1 hLink hNTI hSBC hCS j
      (stateAt R₂.stmt ret E₂ S₀ i) (R₂.res i) hj1 hjN hw hSagree h2
  exact T2_of_A hRS hCRS1 hRC hTP R₁ R₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI hAWrite hReadRes

/-- **T2₁ (Cross-engine conformance via `core→adapter` recording, segmented, call by call).** The
same, at the adapter level: calls are `α`-calls and `RunLinkT` ties the adapter-level runs back to the
recorded driver-boundary ones. No assumption relates `δ_{E₁}` to `δ_{E₂}`. -/
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
    (cls : MethodName → Cls) (hCT : ClsTruthful A.level cls adapterView)
    (hSBC : SameBarrierCount cls (callsB E₂ adapterView driverView Boundary.coreAdapter)
      (callsB E₁ adapterView driverView Boundary.coreAdapter) R₁.N R₁.stmt)
    (hCS : ReplayOK (L := A.level) cls (alphaComp (Query := Query) A E₁)
      (alphaComp (Query := Query) A E₂) adapterView R₁) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      LForall₂ (· ≈ ·) (effCalls A.level (alphaComp (Query := Query) A E₁ (R₁.stmt j)))
        (effCalls A.level (alphaComp (Query := Query) A E₂ (R₁.stmt j))) :=
    fun j hj1 hjN _ => replay_hAWrite hAs hCT (fun a b h => hAVF a b h) R₁ hNTI hSBC hCS j hj1 hjN
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
      (replay_hReadRes hAs hCRS1 hCRS2 hCT (fun a b h => hAVF a b h) R₁ hTF1 hDAG1
        hk₁.res_link hNTI hSBC hCS j _ r₂ hj1 hjN hw hSagree h2) e2
  have h := Eqv.T2_adapter A hAs R₁ R₂ hk₁ hk₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI
    (fun j hj1 hjN hw => writeAgree_of_forall₂ hAs hCRS1 hTF1 _ (hAWrite j hj1 hjN hw)) hReadRes
  exact ⟨h.1, ⟨h.2.1, h.2.2⟩, h.1, ⟨h.2.1, h.2.2⟩⟩

end Module3
end Formalization
