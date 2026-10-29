/-
Faithful Lean 4 encoding of `formalization-1.md` ("Module 1: exact matching
only"), treated as read-only source of truth. Every definition/theorem below
is tagged with the D-number / theorem name it corresponds to.

Two genuine partiality points in the source are resolved the standard way a
total type theory forces (documented at point of use, and in the final
report): D5's `r_E` on a `Read` is defined only when `last(drv_E(stmt))` has
shape `Read(q)`; D9's `r_i := result(last(ρ_i))` is undefined when `evs_i` is
empty. Both are encoded as *equations that presuppose existence*, so a
`LiveRun`/`ReplayRun` for which they fail simply does not exist as a term of
that structure, exactly as "run existence is assumed, not established" is
already an acknowledged Open Gap for schedules generally.

D1/D2 (`Statement`, `Result`, `State`, `DriverCall`, `execS`) live in
`Formalization.Common`, unchanged; everything from D3 on is below, verbatim.
-/

import Formalization.Common

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Formalization
namespace Module1

variable (FQN Query Relation MethodName Args Nodes : Type)

/-! ## D3 (Project, reactive) -/

abbrev History (FQN Query Relation : Type) := List (Statement FQN Query × Result Relation)

/-- `P = (Nodes, next)`, `next : Nodes × History → Statement ∪ {⊥}`. -/
structure Project (Nodes FQN Query Relation : Type) where
  nxt : Nodes → History FQN Query Relation → Option (Statement FQN Query)

/-- `target`, implicit in `Write`'s own field. -/
def target {FQN Query : Type} : Statement FQN Query → Option FQN
  | .write t _ => some t
  | .read _ => none

-- `reads : Statement ⇀ 2^FQN`, encoded as a membership predicate.
variable (reads : Statement FQN Query → FQN → Prop)

/-! ## D4 (AdapterCall) -/

structure AdapterCall (MethodName Args : Type) where
  method : MethodName
  args : Args
  deriving DecidableEq

/-! ## D5 (Engine) -/

structure Engine (FQN Query MethodName Args : Type) where
  α : Statement FQN Query → List (AdapterCall MethodName Args)
  δ : AdapterCall MethodName Args → List (DriverCall FQN Query)

/-- `drv_E(stmt) := concat [ δ(c) : c ∈ α(stmt) ]` -/
def drvE {FQN Query MethodName Args : Type}
    (E : Engine FQN Query MethodName Args) (stmt : Statement FQN Query) :
    List (DriverCall FQN Query) :=
  (E.α stmt).flatMap E.δ

/-- `exec_E(S, stmt) := fold(exec, S, drv_E(stmt))` -/
def execE {FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    (ret : State FQN Relation → Query → Relation)
    (E : Engine FQN Query MethodName Args) :
    State FQN Relation → Statement FQN Query → State FQN Relation
  | S, stmt => (drvE E stmt).foldl (execS ret) S

/-- `r_E(S, stmt) := ok` if `stmt` is a `Write`; `:= ret(S,q)` where
`last(drv_E(stmt)) = Read(q)` if `stmt` is a `Read`. Genuinely partial in the
`Read` case (source gap #1): returns `none` when `drv_E` of a `Read` doesn't
end in a `Read` call. -/
def rE {FQN Query Relation MethodName Args : Type}
    (ret : State FQN Relation → Query → Relation)
    (E : Engine FQN Query MethodName Args)
    (S : State FQN Relation) : Statement FQN Query → Option (Result Relation)
  | .write _ _ => some Result.ok
  | .read q =>
      match (drvE E (Statement.read q)).getLast? with
      | some (Statement.read q') => some (Result.rel (ret S q'))
      | _ => none

/-! ## D6 (Boundary & observable calls) -/

inductive Boundary where
  | coreAdapter
  | adapterDriver
  deriving DecidableEq

/-- A boundary-observed call, abstracted to just its `(op, args)` shape plus,
for `adapter→driver`, the fact it *is* a `Statement`/`DriverCall`. We encode
`calls_B` uniformly as `List (AdapterCall MethodName Args)` by giving the
`adapter→driver` case a canonical `AdapterCall` view of a `DriverCall`
(`method`/`args` read off the `Write`/`Read` tag and payload, as D6 says) so
that "match pairwise on op/args" (R4) is a single notion at both boundaries. -/
structure CallView (MethodName Args : Type) where
  op : MethodName
  args : Args
  deriving DecidableEq

/-- `calls_B(stmt) := α(stmt)` at `core→adapter`, `:= drv_E(stmt)` at
`adapter→driver`; both viewed through `CallView` for uniform (op,args)
matching (D6). -/
def callsB {FQN Query MethodName Args : Type}
    (E : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (B : Boundary) (stmt : Statement FQN Query) : List (CallView MethodName Args) :=
  match B with
  | .coreAdapter => (E.α stmt).map adapterView
  | .adapterDriver => (drvE E stmt).map driverView

/-! ## Pointwise lifting of a relation to lists -/

inductive LForall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : LForall₂ R [] []
  | cons {a b l l'} : R a b → LForall₂ R l l' → LForall₂ R (a :: l) (b :: l')

theorem LForall₂.refl {α : Type} {R : α → α → Prop} (hr : ∀ a, R a a) :
    ∀ l : List α, LForall₂ R l l
  | [] => .nil
  | a :: l => .cons (hr a) (LForall₂.refl hr l)

theorem LForall₂.symm {α : Type} {R : α → α → Prop} (hs : ∀ {a b}, R a b → R b a) :
    ∀ {l l' : List α}, LForall₂ R l l' → LForall₂ R l' l
  | _, _, .nil => .nil
  | _, _, .cons h ht => .cons (hs h) (LForall₂.symm hs ht)

theorem LForall₂.imp {α β : Type} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) :
    ∀ {l : List α} {l' : List β}, LForall₂ R l l' → LForall₂ R' l l'
  | _, _, .nil => .nil
  | _, _, .cons hh ht => .cons (h _ _ hh) (LForall₂.imp h ht)

theorem LForall₂.append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {l₁' l₂' : List β}, LForall₂ R l₁ l₁' → LForall₂ R l₂ l₂' →
      LForall₂ R (l₁ ++ l₂) (l₁' ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h2 => .cons h (LForall₂.append t h2)

theorem LForall₂.of_map {α β γ : Type} {R : γ → γ → Prop} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {l' : List β}, LForall₂ R (l.map f) (l'.map g) →
      LForall₂ (fun a b => R (f a) (g b)) l l'
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: l, b :: l', h => by
    cases h with
    | cons hh ht => exact .cons hh (LForall₂.of_map ht)

theorem LForall₂.getLast? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, LForall₂ R l l' →
      (l.getLast? = none ∧ l'.getLast? = none) ∨
      (∃ a b, l.getLast? = some a ∧ l'.getLast? = some b ∧ R a b)
  | [], [], _ => Or.inl ⟨rfl, rfl⟩
  | a :: l, b :: l', h => by
    cases h with
    | cons hh ht =>
      match l, l', ht with
      | [], [], _ => exact Or.inr ⟨a, b, rfl, rfl, hh⟩
      | x :: xs, y :: ys, ht' =>
        rcases LForall₂.getLast? ht' with ⟨h1, h2⟩ | ⟨a', b', h1, h2, hr⟩
        · exact absurd h1 (by simp [List.getLast?])
        · refine Or.inr ⟨a', b', ?_, ?_, hr⟩
          · rw [List.getLast?_cons_cons]; exact h1
          · rw [List.getLast?_cons_cons]; exact h2


theorem LForall₂.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, LForall₂ R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ hrest => by simp [LForall₂.length_eq hrest]

theorem LForall₂.get {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, LForall₂ R l l' →
    ∀ (k : Nat) (a : α) (b : β), l[k]? = some a → l'[k]? = some b → R a b
  | _, _, .nil, k, a, b, ha, _ => by simp at ha
  | _, _, .cons hab hrest, k, a, b, ha, hb => by
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero] at ha hb
        rw [← Option.some.inj ha, ← Option.some.inj hb]
        exact hab
      | succ k =>
        simp only [List.getElem?_cons_succ] at ha hb
        exact LForall₂.get hrest k a b ha hb

theorem LForall₂.take {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, LForall₂ R l l' → ∀ k, LForall₂ R (l.take k) (l'.take k)
  | _, _, .nil, k => by simp [LForall₂.nil]
  | _, _, .cons hab hrest, k => by
      cases k with
      | zero => simp [LForall₂.nil]
      | succ k => simpa using LForall₂.cons hab (LForall₂.take hrest k)

/-- Sums of pointwise-related lists agree when the two summands agree on related elements. -/
theorem LForall₂.sum_eq {α β : Type} {R : α → β → Prop} {f : α → Nat} {g : β → Nat} :
    ∀ {l : List α} {l' : List β}, LForall₂ R l l' →
      (∀ a b, R a b → b ∈ l' → f a = g b) → (l.map f).sum = (l'.map g).sum
  | _, _, .nil, _ => rfl
  | _, _, @LForall₂.cons _ _ _ a b l l' hab hrest, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [h a b hab List.mem_cons_self,
      LForall₂.sum_eq hrest (fun x y hxy hy => h x y hxy (List.mem_cons_of_mem b hy))]

/-- Pointwise agreement of two equal-length lists is `LForall₂`. -/
theorem LForall₂.of_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ (l : List α) (l' : List β), l.length = l'.length →
      (∀ (u : Nat) (a : α) (b : β), l[u]? = some a → l'[u]? = some b → R a b) →
        LForall₂ R l l'
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, hR => by
    refine .cons (hR 0 a b rfl rfl) (LForall₂.of_getElem? l l' (by simpa using h) ?_)
    intro u x y hx hy
    exact hR (u + 1) x y (by simpa using hx) (by simpa using hy)

/-- `LForall₂` of equality is equality. -/
theorem LForall₂.eq_of {α : Type} :
    ∀ {l l' : List α}, LForall₂ (· = ·) l l' → l = l'
  | _, _, .nil => rfl
  | _, _, .cons h hrest => by rw [h, LForall₂.eq_of hrest]

/-! ## D7 (Live run, trace & behavior)

Positions are 1-indexed naturals, matching the source exactly (`i ∈ 1..N+1`);
`node/stmt/res : Nat → _` are total functions, meaningful only on `[1,N]`
(resp. `[1,N+1]` for `hist`/`state`), exactly as the source's `schedule`
lists turns and everything else is derived from it by filtering/folding.

`histAt`/`turnCount` are given by recursion on the position bound (rather
than via `List.range`/`filter`) purely so that the one algebraic fact T1
needs of them — `histAt_prefix` below, "an earlier `H(n,i)` is a prefix of
a later `H(n,i')`, cut at `i`'s own turn count" — is a two-line induction
instead of a page of list-filter lemmas. Both compute the same values the
source's set-builder notation describes; this is a proof-engineering choice
about *how*, not a change to *what*. -/

/-- `H(n,i) := [ (stmt_j,r_j) : j<i, n_j=n ]`. -/
def histAt {Nodes FQN Query Relation : Type} [DecidableEq Nodes]
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (n : Nodes) : Nat → History FQN Query Relation
  | 0 => []
  | i + 1 => histAt node stmt res n i ++ (if 1 ≤ i ∧ node i = n then [(stmt i, res i)] else [])

/-- Number of `n`'s turns strictly before position `i`. -/
def turnCount {Nodes : Type} [DecidableEq Nodes] (node : Nat → Nodes) (n : Nodes) : Nat → Nat
  | 0 => 0
  | i + 1 => turnCount node n i + (if 1 ≤ i ∧ node i = n then 1 else 0)

theorem turnCount_eq_length {Nodes FQN Query Relation : Type} [DecidableEq Nodes]
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (n : Nodes) (i : Nat) :
    (histAt node stmt res n i).length = turnCount node n i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [histAt, turnCount]
    split <;> simp [ih]

theorem turnCount_step {Nodes : Type} [DecidableEq Nodes] (node : Nat → Nodes) (n : Nodes)
    (i : Nat) : turnCount node n i ≤ turnCount node n (i + 1) := by
  simp only [turnCount]; split <;> omega

theorem turnCount_mono {Nodes : Type} [DecidableEq Nodes] (node : Nat → Nodes) (n : Nodes) :
    ∀ {i i' : Nat}, i ≤ i' → turnCount node n i ≤ turnCount node n i' := by
  intro i i' h
  induction h with
  | refl => exact Nat.le_refl _
  | @step m _ ih => exact Nat.le_trans ih (turnCount_step node n m)

/-- An earlier `H(n,i)` is exactly the prefix of a later `H(n,i')` of length
`turnCount node n i` — the one structural fact needed to relate `LiveRun`'s
raw-position bookkeeping to `ReplayRun`'s purely per-node one (T1). -/
theorem histAt_prefix {Nodes FQN Query Relation : Type} [DecidableEq Nodes]
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (n : Nodes) {i i' : Nat} (h : i ≤ i') :
    histAt node stmt res n i = (histAt node stmt res n i').take (turnCount node n i) := by
  induction h with
  | refl => rw [← turnCount_eq_length, List.take_length]
  | @step m him ih =>
    have hle : turnCount node n i ≤ turnCount node n m := turnCount_mono node n him
    simp only [histAt]
    split
    · rw [List.take_append_of_le_length (by rw [turnCount_eq_length]; exact hle)]
      exact ih
    · rw [List.append_nil]
      exact ih

/-- The position realizing any in-range turn count: if `k` is less than `n`'s
total turn count within the first `N` positions, there is a (unique) turn
position `j < N` with `node j = n`, exactly `k` of `n`'s turns before it, and
`histAt`'s `k`-th recorded entry (0-indexed) is literally `(stmt j, res j)`. -/
theorem histAt_find {Nodes FQN Query Relation : Type} [DecidableEq Nodes]
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (n : Nodes) :
    ∀ (N k : Nat), k < turnCount node n N →
      ∃ j, j < N ∧ 1 ≤ j ∧ node j = n ∧ turnCount node n j = k ∧
           (histAt node stmt res n N)[k]? = some (stmt j, res j) := by
  intro N
  induction N with
  | zero => intro k hk; simp [turnCount] at hk
  | succ m ih =>
    intro k hk
    simp only [turnCount] at hk
    by_cases hm : 1 ≤ m ∧ node m = n
    · simp only [hm, and_self, ite_true] at hk
      by_cases hk' : k < turnCount node n m
      · obtain ⟨j, hjN, hj1, hjnode, hjcount, hjentry⟩ := ih k hk'
        refine ⟨j, Nat.lt_succ_of_lt hjN, hj1, hjnode, hjcount, ?_⟩
        simp only [histAt, hm, and_self, ite_true]
        rw [List.getElem?_append_left (by rw [turnCount_eq_length]; exact hk')]
        exact hjentry
      · have hkeq : k = turnCount node n m := by omega
        refine ⟨m, Nat.lt_succ_self m, hm.1, hm.2, hkeq.symm, ?_⟩
        simp only [histAt, hm, and_self, ite_true]
        rw [hkeq, ← turnCount_eq_length node stmt res n m, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self]
        rfl
    · simp only [hm, ite_false] at hk
      obtain ⟨j, hjN, hj1, hjnode, hjcount, hjentry⟩ := ih k hk
      refine ⟨j, Nat.lt_succ_of_lt hjN, hj1, hjnode, hjcount, ?_⟩
      simp only [histAt, hm, ite_false, List.append_nil]
      exact hjentry

/-- Any two positions (within a shared bound `N`) with the same turn count
for `n` give the same `H(n,·)` — a direct corollary of `histAt_prefix`,
since both are then the same-length prefix of the same final list. -/
theorem histAt_turnCount_unique {Nodes FQN Query Relation : Type} [DecidableEq Nodes]
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (n : Nodes) {N i₁ i₂ : Nat} (h₁ : i₁ ≤ N) (h₂ : i₂ ≤ N)
    (heq : turnCount node n i₁ = turnCount node n i₂) :
    histAt node stmt res n i₁ = histAt node stmt res n i₂ := by
  rw [histAt_prefix node stmt res n h₁, histAt_prefix node stmt res n h₂, heq]

/-- Among positions that are actually `n`'s own turns, `turnCount` is
injective: it strictly increases at each one. -/
theorem turn_position_unique {Nodes : Type} [DecidableEq Nodes] (node : Nat → Nodes) (n : Nodes)
    {i₁ i₂ : Nat} (h1₁ : 1 ≤ i₁) (hn₁ : node i₁ = n) (h1₂ : 1 ≤ i₂) (hn₂ : node i₂ = n)
    (heq : turnCount node n i₁ = turnCount node n i₂) : i₁ = i₂ := by
  rcases Nat.lt_trichotomy i₁ i₂ with h | h | h
  · exfalso
    have hstep : turnCount node n (i₁ + 1) = turnCount node n i₁ + 1 := by
      simp only [turnCount, h1₁, hn₁, and_self, ite_true]
    have hmono : turnCount node n (i₁ + 1) ≤ turnCount node n i₂ :=
      turnCount_mono node n (by omega)
    omega
  · exact h
  · exfalso
    have hstep : turnCount node n (i₂ + 1) = turnCount node n i₂ + 1 := by
      simp only [turnCount, h1₂, hn₂, and_self, ite_true]
    have hmono : turnCount node n (i₂ + 1) ≤ turnCount node n i₁ :=
      turnCount_mono node n (by omega)
    omega

/-- `S(i) := fold(exec_E, S₀, [stmt_j : j<i])`. -/
def stateAt {FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    (stmt : Nat → Statement FQN Query)
    (ret : State FQN Relation → Query → Relation) (E : Engine FQN Query MethodName Args)
    (S₀ : State FQN Relation) (i : Nat) : State FQN Relation :=
  (((List.range (i - 1)).map (· + 1)).map stmt).foldl (execE ret E) S₀

/-- `R = (E, P, S₀, schedule)`. `stmt_eq` folds together D7's defining
equation `stmt_i := next(n_i,H(n_i,i))` with (V1) `stmt_i ≠ ⊥` (see file
header). Likewise `res_eq` folds D5's `r_i := r_E(S(i),stmt_i)` together with
the implicit totality D5's "where" clause on `Read` presupposes (gap #1,
documented at `rE`). `valid2` is (V2) verbatim. -/
structure LiveRun {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes]
    (P : Project Nodes FQN Query Relation) (E : Engine FQN Query MethodName Args)
    (ret : State FQN Relation → Query → Relation)
   
    (S₀ : State FQN Relation) where
  N : Nat
  node : Nat → Nodes
  stmt : Nat → Statement FQN Query
  res : Nat → Result Relation
  stmt_eq : ∀ i, 1 ≤ i → i ≤ N → P.nxt (node i) (histAt node stmt res (node i) i) = some (stmt i)
  res_eq : ∀ i, 1 ≤ i → i ≤ N → rE ret E (stateAt stmt ret E S₀ i) (stmt i) = some (res i)
  valid2 : ∀ n, P.nxt n (histAt node stmt res n (N + 1)) = none

/-- `S_final(R) := S(N+1)`. -/
def SFinal {Nodes FQN Query Relation MethodName Args : Type} [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) : State FQN Relation :=
  stateAt R.stmt ret E S₀ (R.N + 1)

/-- `O(R) := { (n, last(H(n,N+1)).Result) : n ∈ Nodes }`, encoded as a
relation rather than a (possibly-partial, gap #2) function of `n`: a node
that never performs a statement has no "last" entry of `H(n,N+1)`, which the
source's set-builder silently presupposes exists. Encoding `O` as membership
sidesteps needing that assumption to state/prove T1's `O`-corollary, exactly
as `res_eq`/`stmt_eq` above sidestep D5/D9's own partiality by phrasing them
as equations that presuppose existence rather than as total functions. -/
def isObs {Nodes FQN Query Relation : Type} [DecidableEq Nodes]
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query) (res : Nat → Result Relation)
    (N : Nat) (n : Nodes) (r : Result Relation) : Prop :=
  (histAt node stmt res n (N + 1)).getLast?.map Prod.snd = some r

/-! ## D8 (Behavioral equivalence & divergence)

`R₁ ≈ R₂ ⟺ Behavior(R₁) = Behavior(R₂)`, i.e. same `S_final` and same `O`
(as a relation, per the note above). Defined only for live runs, as in the
source. -/
def BehEquiv {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀) : Prop :=
  SFinal R₁ = SFinal R₂ ∧ ∀ n r, isObs R₁.node R₁.stmt R₁.res R₁.N n r ↔
                                  isObs R₂.node R₂.stmt R₂.res R₂.N n r

/-! ## D9 (Replay run)

Given `ρ = τ_B(R₁)`, a replay run is built directly against `R₁` rather than
through an intermediate trace object: `ρ` is uniquely determined by `R₁` and
`B` (it is *defined to be* `τ_B(R₁)`, not an independent choice), and D9 only
ever uses two things from it — per-turn `(op,args)` lists for matching (R4,
together with (R3) as the implicit length bound: indexing past the end of
`recording` below fails, i.e. `none`) and, at each turn's last call, the
recorded *statement's own result* to serve — which sidesteps D9's own
partiality when `evs_i = []` (undefined `last` of an empty stretch, "gap #2")
by reading `R₁.res` directly (already well-defined by `LiveRun`) rather than
re-deriving a result from an event list.

We deliberately drop the raw global schedule `R₂'` would otherwise carry:
every observable D9 defines, and everything T1/T2 conclude, is stated purely
per node via `H(n,·)`, and the source's own proof of T1 explicitly concludes
"nothing in this argument refers to a global position or another node's
state... matching is per-node-positional... no coordination between nodes'
relative progress is needed." Building the replay side directly as a
per-node recursion over the recording bakes in exactly that fact rather than
re-deriving it from an otherwise-irrelevant interleaving; every observable
of a `ReplayRun` below is expressible without ever naming a raw position. -/

/-- D7's `H(n,R₁.N+1)`: the `(stmt,result)` pairs `R₁` itself realized for
`n`, in turn order — boundary-independent (unlike `τ_B(R)`, D7's actual
boundary-level trace, computed from this by `eventsOf`). -/
def recordingOf {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (n : Nodes) : History FQN Query Relation :=
  histAt R₁.node R₁.stmt R₁.res n (R₁.N + 1)

/-- D7's `Event := (node, op, args, result)` — one per boundary call. -/
structure Event (Nodes MethodName Args Relation : Type) where
  node : Nodes
  view : CallView MethodName Args
  result : Result Relation

/-- Turn a turn's own list of compiled-call views into `Event`s carrying
node `n`: every call but the last gets the placeholder `Result.ok`, and the
last gets the turn's own served result `r`. Nothing downstream ever reads a
non-last call's own result — D9's `r_i := result(last(ρ_i))` is the only
place any event's `result` field is consulted at all — so this choice is
never observed. -/
def viewsToEvents {Nodes MethodName Args Relation : Type} (n : Nodes) (r : Result Relation) :
    List (CallView MethodName Args) → List (Event Nodes MethodName Args Relation)
  | [] => []
  | [v] => [⟨n, v, r⟩]
  | v :: (w :: ws) => ⟨n, v, Result.ok⟩ :: viewsToEvents n r (w :: ws)

/-- D7's `τ_B(R)` restricted to node `n`, i.e. `ρ|ₙ`: the flat sequence of
`Event`s `n`'s own recorded `(Statement, Result)` history generates at
boundary `B`, under engine `E`, in turn order. -/
def eventsOf {Nodes FQN Query Relation MethodName Args : Type}
    (E : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (n : Nodes) : History FQN Query Relation → List (Event Nodes MethodName Args Relation)
  | [] => []
  | (stmt, r) :: rest =>
      viewsToEvents n r (callsB E adapterView driverView B stmt) ++
        eventsOf E adapterView driverView B n rest

/-! ### Replay, call by call (D9)

Replay matches **calls**, one at a time. Serving a live call looks only at the recorded event at the
cursor: it must match (`m recorded live`), and the call is served that event's result. A turn
(a statement) only groups its calls: it fixes the order they are issued in and says that the result
served for the *last* of them is the turn's result, D9's `r_i := result(last(ρ_i))` (a turn with no
calls is not replayable). `m` is the match relation on call views — equality here, `CVEquiv` (op
exactly, args up to `~_A`) in Module 2 — so one definition serves both. -/

section ReplayWith

variable {Nodes FQN Query Relation MethodName Args : Type}

/-- Serve one live call (view `v`) at cursor `cur`: the recorded event there must match it; the
result served is that event's own. -/
def serveCall (m : CallView MethodName Args → CallView MethodName Args → Prop) [DecidableRel m]
    (ρ : List (Event Nodes MethodName Args Relation)) (cur : Nat) (v : CallView MethodName Args) :
    Option (Result Relation) :=
  match ρ[cur]? with
  | some e => if m e.view v then some e.result else none
  | none => none

/-- Serve a turn's calls in order, one call at a time: the result served for the last call, and the
cursor after the turn. -/
def serveCalls (m : CallView MethodName Args → CallView MethodName Args → Prop) [DecidableRel m]
    (ρ : List (Event Nodes MethodName Args Relation)) :
    Nat → List (CallView MethodName Args) → Option (Result Relation × Nat)
  | _, [] => none
  | cur, [v] => (serveCall m ρ cur v).map (fun r => (r, cur + 1))
  | cur, v :: w :: ws =>
      match serveCall m ρ cur v with
      | none => none
      | some _ => serveCalls m ρ (cur + 1) (w :: ws)

theorem drop_eq_cons_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l.drop i = a :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.drop_eq_getElem_cons hi

/-- Serving a turn's calls succeeds exactly when the next `|vs|` recorded events match them
pointwise, and then advances the cursor past them. -/
theorem serveCalls_spec (m : CallView MethodName Args → CallView MethodName Args → Prop)
    [DecidableRel m] (ρ : List (Event Nodes MethodName Args Relation)) :
    ∀ (vs : List (CallView MethodName Args)) (cur : Nat) (r : Result Relation) (cur' : Nat),
      serveCalls m ρ cur vs = some (r, cur') →
      cur' = cur + vs.length ∧ LForall₂ m (((ρ.drop cur).take vs.length).map Event.view) vs
  | [], cur, r, cur', h => by simp [serveCalls] at h
  | [v], cur, r, cur', h => by
    simp only [serveCalls, Option.map_eq_some_iff] at h
    obtain ⟨r₀, hs, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨-, rfl⟩ := hpair
    unfold serveCall at hs
    cases hρ : ρ[cur]? with
    | none => rw [hρ] at hs; simp at hs
    | some e =>
      rw [hρ] at hs
      by_cases hm : m e.view v
      · refine ⟨rfl, ?_⟩
        rw [drop_eq_cons_of_getElem? hρ]
        simpa using LForall₂.cons hm LForall₂.nil
      · simp [hm] at hs
  | v :: w :: ws, cur, r, cur', h => by
    simp only [serveCalls] at h
    split at h
    · simp at h
    · rename_i r₀ hs
      obtain ⟨hc, hrest⟩ := serveCalls_spec m ρ (w :: ws) (cur + 1) r cur' h
      unfold serveCall at hs
      cases hρ : ρ[cur]? with
      | none => rw [hρ] at hs; simp at hs
      | some e =>
        rw [hρ] at hs
        by_cases hm : m e.view v
        · refine ⟨by simp at hc ⊢; omega, ?_⟩
          rw [drop_eq_cons_of_getElem? hρ]
          have : (e :: ρ.drop (cur + 1)).take ((v :: w :: ws).length) =
              e :: (ρ.drop (cur + 1)).take ((w :: ws).length) := by simp
          rw [this]
          exact LForall₂.cons hm hrest
        · simp [hm] at hs

/-- Node `n`'s replayed history after its first `k` turns, together with its event cursor, by
recursion on `k`: at each turn the next statement `next` produces is compiled by `E₂`, and its calls
are served one at a time against `ρ` from the cursor. `none` = a consumability failure (D10) at or
before turn `k`. -/
def replayEvWith (m : CallView MethodName Args → CallView MethodName Args → Prop) [DecidableRel m]
    (P : Project Nodes FQN Query Relation) (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (ρ : List (Event Nodes MethodName Args Relation)) (n : Nodes) :
    Nat → Option (History FQN Query Relation × Nat)
  | 0 => some ([], 0)
  | k + 1 =>
      match replayEvWith m P E₂ adapterView driverView B ρ n k with
      | none => none
      | some (prev, cur) =>
        match P.nxt n prev with
        | none => none
        | some stmt =>
          match serveCalls m ρ cur (callsB E₂ adapterView driverView B stmt) with
          | none => none
          | some (r, cur') => some (prev ++ [(stmt, r)], cur')

/-- `replayEvWith`'s output history, whenever it succeeds, has length exactly the step count. -/
theorem replayEvWith_length (m : CallView MethodName Args → CallView MethodName Args → Prop)
    [DecidableRel m] (P : Project Nodes FQN Query Relation)
    (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (ρ : List (Event Nodes MethodName Args Relation)) (n : Nodes) :
    ∀ k prev cur, replayEvWith m P E₂ adapterView driverView B ρ n k = some (prev, cur) →
      prev.length = k
  | 0, prev, cur, h => by simp only [replayEvWith, Option.some.injEq, Prod.mk.injEq] at h; simp [← h.1]
  | k + 1, prev, cur, h => by
      simp only [replayEvWith] at h
      split at h
      · exact absurd h (by simp)
      · rename_i prev' cur' heq
        split at h
        · exact absurd h (by simp)
        · rename_i stmt hstmt
          split at h
          · exact absurd h (by simp)
          · rename_i r cur'' hserve
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1, List.length_append, List.length_singleton]
            have := replayEvWith_length m P E₂ adapterView driverView B ρ n k prev' cur' heq
            omega

/-- A successful step `k+1` always extends a successful step `k`'s own output by exactly one
appended entry — replay never revisits or rewrites earlier entries. -/
theorem replayEvWith_succ_append (m : CallView MethodName Args → CallView MethodName Args → Prop)
    [DecidableRel m] (P : Project Nodes FQN Query Relation)
    (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (ρ : List (Event Nodes MethodName Args Relation)) (n : Nodes) (k : Nat) :
    ∀ prev cur, replayEvWith m P E₂ adapterView driverView B ρ n (k + 1) = some (prev, cur) →
      ∃ prev' cur' x, replayEvWith m P E₂ adapterView driverView B ρ n k = some (prev', cur') ∧
        prev = prev' ++ [x] := by
  intro prev cur h
  simp only [replayEvWith] at h
  split at h
  · exact absurd h (by simp)
  · rename_i prev' cur' heq
    split at h
    · exact absurd h (by simp)
    · rename_i stmt hstmt
      split at h
      · exact absurd h (by simp)
      · rename_i r cur'' hserve
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨prev', cur', (stmt, r), heq, h.1.symm⟩

/-- `replayEvWith`'s output history at any intermediate step `k` is exactly the length-`k` prefix of
a later successful output — the fact `ConvergentReplay` (stated only at the *full* length) needs to
give intermediate-turn guarantees. -/
theorem replayEvWith_prefix (m : CallView MethodName Args → CallView MethodName Args → Prop)
    [DecidableRel m] (P : Project Nodes FQN Query Relation)
    (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (ρ : List (Event Nodes MethodName Args Relation)) (n : Nodes) :
    ∀ K full curK, replayEvWith m P E₂ adapterView driverView B ρ n K = some (full, curK) →
      ∀ k, k ≤ K → ∃ cur, replayEvWith m P E₂ adapterView driverView B ρ n k =
        some (full.take k, cur) := by
  intro K
  induction K with
  | zero =>
    intro full curK h k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [replayEvWith, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, by simp only [replayEvWith, List.take_zero]⟩
  | succ K ih =>
    intro full curK h k hk
    obtain ⟨prev', cur', x, heq, hfull⟩ :=
      replayEvWith_succ_append m P E₂ adapterView driverView B ρ n K full curK h
    have hlen' : prev'.length = K :=
      replayEvWith_length m P E₂ adapterView driverView B ρ n K prev' cur' heq
    rcases Nat.lt_or_ge k (K + 1) with hlt | hge
    · have hkK : k ≤ K := by omega
      obtain ⟨cur, hc⟩ := ih prev' cur' heq k hkK
      refine ⟨cur, ?_⟩
      rw [hfull, List.take_append_of_le_length (by omega)]
      exact hc
    · have hkeq : k = K + 1 := by omega
      subst hkeq
      have hfulllen : full.length = K + 1 := by
        rw [hfull, List.length_append, hlen', List.length_singleton]
      rw [List.take_of_length_le (by omega)]
      exact ⟨curK, h⟩

/-- A successful step `k+1`'s own match, exposed directly: the statement `next` produces from step
`k`'s history, and the fact that `E₂`'s compiled views for it match the next stretch of `ρ` pointwise
(each call was matched on its own). -/
theorem replayEvWith_succ_view_match (m : CallView MethodName Args → CallView MethodName Args → Prop)
    [DecidableRel m] (P : Project Nodes FQN Query Relation)
    (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (ρ : List (Event Nodes MethodName Args Relation)) (n : Nodes) (k : Nat) :
    ∀ prev cur, replayEvWith m P E₂ adapterView driverView B ρ n (k + 1) = some (prev, cur) →
      ∃ prev' cur' stmt,
        replayEvWith m P E₂ adapterView driverView B ρ n k = some (prev', cur') ∧
        P.nxt n prev' = some stmt ∧
        cur = cur' + (callsB E₂ adapterView driverView B stmt).length ∧
        LForall₂ m
          (((ρ.drop cur').take (callsB E₂ adapterView driverView B stmt).length).map Event.view)
          (callsB E₂ adapterView driverView B stmt) := by
  intro prev cur h
  simp only [replayEvWith] at h
  split at h
  · exact absurd h (by simp)
  · rename_i prev' cur' heq
    split at h
    · exact absurd h (by simp)
    · rename_i stmt hstmt
      split at h
      · exact absurd h (by simp)
      · rename_i r cur'' hserve
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hc, hm⟩ := serveCalls_spec m ρ _ cur' r cur'' hserve
        exact ⟨prev', cur', stmt, heq, hstmt, by rw [← h.2]; exact hc, hm⟩

end ReplayWith

section Aligned

variable {Nodes FQN Query Relation MethodName Args : Type} [DecidableEq FQN] [DecidableEq Nodes]

/-- `ρ = τ_B(R₁)` is replayable by a replay of `E₂` matching calls with `m`, *and* that replay
reproduces `R₁`'s own per-node history entry for entry — "the replay succeeds, and gets the same answer
`R₁` did." Stated directly, rather than as bare consumability: bare consumability does *not* entail
entry-for-entry convergence on its own (a longer-than-recorded turn can "borrow" a later turn's events
while still reaching a consumed, done state — see the counterexample in
`implementation-deviations.md`). The replay is served with the recorded events themselves, so the
served results are literally `R₁`'s own whatever `m` accepted. -/
def ConvergentReplayWith (m : CallView MethodName Args → CallView MethodName Args → Prop)
    [DecidableRel m] {P : Project Nodes FQN Query Relation}
    {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (B : Boundary) : Prop :=
  ∀ n, ∃ cur,
    replayEvWith m P E₂ adapterView driverView B
        (eventsOf E₁ adapterView driverView B n (recordingOf R₁ n)) n
        (turnCount R₁.node n (R₁.N + 1))
      = some (recordingOf R₁ n, cur) ∧
    cur = (eventsOf E₁ adapterView driverView B n (recordingOf R₁ n)).length

theorem viewsToEvents_length {Nodes MethodName Args Relation : Type} (n : Nodes) (r : Result Relation) :
    ∀ L : List (CallView MethodName Args), (viewsToEvents n r L).length = L.length
  | [] => rfl
  | [_] => rfl
  | _ :: w :: ws => by
      simp only [viewsToEvents, List.length_cons, viewsToEvents_length n r (w :: ws)]

theorem viewsToEvents_view {Nodes MethodName Args Relation : Type} (n : Nodes) (r : Result Relation) :
    ∀ L : List (CallView MethodName Args), (viewsToEvents n r L).map Event.view = L
  | [] => rfl
  | [_] => rfl
  | _ :: w :: ws => by
      simp only [viewsToEvents, List.map_cons, viewsToEvents_view n r (w :: ws)]

theorem eventsOf_append {Nodes FQN Query Relation MethodName Args : Type}
    (E : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary) (n : Nodes) :
    ∀ H1 H2 : History FQN Query Relation,
      eventsOf E adapterView driverView B n (H1 ++ H2) =
        eventsOf E adapterView driverView B n H1 ++ eventsOf E adapterView driverView B n H2
  | [], H2 => by simp [eventsOf]
  | (_, _) :: rest, H2 => by
      simp only [List.cons_append, eventsOf]
      rw [eventsOf_append E adapterView driverView B n rest H2, List.append_assoc]

/-- Per-turn alignment: whenever replaying exactly `k` steps for node `n` succeeds, the cursor it
lands on is exactly the event-count `E₁`'s own compilation of the replayed prefix produces — ruling out
the "borrowed call" ambiguity that bare `ConvergentReplayWith` (checked only at the full length) leaves
open on its own. Combined with `ConvergentReplayWith` (`replayEvWith_prefix` identifies the replayed
prefix as `R₁`'s own recording, turn for turn), this pins the cursor down turn by turn, not just at
the end. -/
def PerTurnAlignedWith (m : CallView MethodName Args → CallView MethodName Args → Prop)
    [DecidableRel m] {P : Project Nodes FQN Query Relation}
    {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (B : Boundary) : Prop :=
  ∀ n k, k ≤ turnCount R₁.node n (R₁.N + 1) →
    ∀ prev cur,
      replayEvWith m P E₂ adapterView driverView B
        (eventsOf E₁ adapterView driverView B n (recordingOf R₁ n)) n k = some (prev, cur) →
      cur = (eventsOf E₁ adapterView driverView B n prev).length

/-- `ConvergentReplayWith` + `PerTurnAlignedWith` recover `(A)` at the `CallView` level, turn by turn:
`m`-agreement of the two engines' own compiled calls. No "borrowed call" ambiguity survives once the
cursor is pinned to the *true* per-turn event count at every step, not just at the end. -/
theorem callsB_agree_of_aligned_with
    (m : CallView MethodName Args → CallView MethodName Args → Prop) [DecidableRel m]
    {P : Project Nodes FQN Query Relation} {E₁ E₂ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (hCV : ConvergentReplayWith m R₁ E₂ adapterView driverView B)
    (hAl : PerTurnAlignedWith m R₁ E₂ adapterView driverView B) :
    ∀ j, 1 ≤ j → j ≤ R₁.N →
      LForall₂ m (callsB E₁ adapterView driverView B (R₁.stmt j))
        (callsB E₂ adapterView driverView B (R₁.stmt j)) := by
  intro j hj1 hjN
  obtain ⟨n, hn⟩ : ∃ n, R₁.node j = n := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, turnCount R₁.node n j = k := ⟨_, rfl⟩
  have hstepk : turnCount R₁.node n (j + 1) = k + 1 := by
    rw [← hk]; simp only [turnCount, hj1, hn, and_self, ite_true]
  have hkN : k + 1 ≤ turnCount R₁.node n (R₁.N + 1) := by
    rw [← hstepk]; exact turnCount_mono R₁.node n (by omega)
  obtain ⟨curFull, hFull, -⟩ := hCV n
  obtain ⟨curk, hk_eq⟩ := replayEvWith_prefix m P E₂ adapterView driverView B
    (eventsOf E₁ adapterView driverView B n (recordingOf R₁ n)) n
    (turnCount R₁.node n (R₁.N + 1)) (recordingOf R₁ n) curFull hFull k (by omega)
  obtain ⟨curk1, hk1_eq⟩ := replayEvWith_prefix m P E₂ adapterView driverView B
    (eventsOf E₁ adapterView driverView B n (recordingOf R₁ n)) n
    (turnCount R₁.node n (R₁.N + 1)) (recordingOf R₁ n) curFull hFull (k + 1) hkN
  have hprevk : (recordingOf R₁ n).take k = histAt R₁.node R₁.stmt R₁.res n j := by
    simp only [recordingOf]
    rw [← hk, ← histAt_prefix R₁.node R₁.stmt R₁.res n (show j ≤ R₁.N + 1 by omega)]
  have hprevk1 : (recordingOf R₁ n).take (k + 1) = histAt R₁.node R₁.stmt R₁.res n (j + 1) := by
    simp only [recordingOf]
    rw [← hstepk, ← histAt_prefix R₁.node R₁.stmt R₁.res n (show j + 1 ≤ R₁.N + 1 by omega)]
  have hnxt : P.nxt n ((recordingOf R₁ n).take k) = some (R₁.stmt j) := by
    rw [hprevk]
    have := R₁.stmt_eq j hj1 hjN
    rwa [hn] at this
  have hsplit : histAt R₁.node R₁.stmt R₁.res n (j + 1) =
      histAt R₁.node R₁.stmt R₁.res n j ++ [(R₁.stmt j, R₁.res j)] := by
    simp only [histAt, hj1, hn, and_self, ite_true]
  have halignk := hAl n k (by omega) _ _ hk_eq
  have halignk1 := hAl n (k + 1) hkN _ _ hk1_eq
  rw [hprevk1, hsplit, eventsOf_append, List.length_append] at halignk1
  simp only [eventsOf, List.append_nil, viewsToEvents_length] at halignk1
  have halignk_hist : curk = (eventsOf E₁ adapterView driverView B n
      (histAt R₁.node R₁.stmt R₁.res n j)).length := by
    rw [← hprevk]; exact halignk
  rw [← halignk_hist] at halignk1
  -- `halignk1 : curk1 = curk + (callsB E₁ adapterView driverView B (R₁.stmt j)).length`
  obtain ⟨prevk', curk', stmt, heqk', hstmtk', hcurk1, hview⟩ :=
    replayEvWith_succ_view_match m P E₂ adapterView driverView B
      (eventsOf E₁ adapterView driverView B n (recordingOf R₁ n)) n k
      ((recordingOf R₁ n).take (k + 1)) curk1 hk1_eq
  have hpk' : prevk' = (recordingOf R₁ n).take k ∧ curk' = curk := by
    have heq2 := heqk'.symm.trans hk_eq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq2
    exact heq2
  obtain ⟨hprevk'eq, hcurk'eq⟩ := hpk'
  have hstmteq : stmt = R₁.stmt j := by
    rw [hprevk'eq] at hstmtk'
    rw [hnxt] at hstmtk'
    exact (Option.some.injEq _ _).mp hstmtk'.symm
  rw [hcurk'eq, hstmteq] at hcurk1
  rw [hcurk'eq, hstmteq] at hview
  -- `hcurk1 : curk1 = curk + (callsB E₂ ... (R₁.stmt j)).length`
  -- `halignk1 : curk1 = curk + (callsB E₁ ... (R₁.stmt j)).length`
  have hlenEq : (callsB E₂ adapterView driverView B (R₁.stmt j)).length =
      (callsB E₁ adapterView driverView B (R₁.stmt j)).length := by omega
  -- Identify the matched slice with `E₁`'s own turn-`j` events directly.
  have hdroptake : (recordingOf R₁ n) = (recordingOf R₁ n).take k ++ (recordingOf R₁ n).drop k :=
    (List.take_append_drop k (recordingOf R₁ n)).symm
  have hdropk1 : (recordingOf R₁ n).drop k =
      [(R₁.stmt j, R₁.res j)] ++ (recordingOf R₁ n).drop (k + 1) := by
    have h1 : (recordingOf R₁ n).take k ++ (recordingOf R₁ n).drop k = recordingOf R₁ n :=
      List.take_append_drop k (recordingOf R₁ n)
    have h2 : (recordingOf R₁ n).take k ++ ([(R₁.stmt j, R₁.res j)] ++ (recordingOf R₁ n).drop (k + 1)) =
        recordingOf R₁ n := by
      rw [← List.append_assoc]
      have heqpre : (recordingOf R₁ n).take k ++ [(R₁.stmt j, R₁.res j)] =
          (recordingOf R₁ n).take (k + 1) := by
        rw [hprevk, hprevk1, hsplit]
      rw [heqpre, List.take_append_drop]
    exact (List.append_right_inj ((recordingOf R₁ n).take k)).mp (h1.trans h2.symm)
  have hslice : (eventsOf E₁ adapterView driverView B n (recordingOf R₁ n)).drop curk =
      eventsOf E₁ adapterView driverView B n ((recordingOf R₁ n).drop k) := by
    have step1 := eventsOf_append E₁ adapterView driverView B n
      ((recordingOf R₁ n).take k) ((recordingOf R₁ n).drop k)
    rw [← hdroptake] at step1
    rw [step1, halignk, List.drop_left]
  rw [hslice, hdropk1, eventsOf_append] at hview
  simp only [eventsOf, List.append_nil] at hview
  rw [hlenEq] at hview
  rw [List.take_append_of_le_length (Nat.le_of_eq (viewsToEvents_length n (R₁.res j)
    (callsB E₁ adapterView driverView B (R₁.stmt j))).symm)] at hview
  rw [List.take_of_length_le (Nat.le_of_eq (viewsToEvents_length n (R₁.res j)
    (callsB E₁ adapterView driverView B (R₁.stmt j)))),
    viewsToEvents_view] at hview
  exact hview

end Aligned

/-- `ρ = τ_B(R₁)` is consumable for a replay of `E₂`, *and* that replay
reproduces `R₁`'s own per-node history entry for entry — "the replay
succeeds, and gets the same answer `R₁` did." D9's (R1)–(R5) (event by
event, not statement-block matching) plus the entry-for-entry equality
are stated directly as one hypothesis, rather than as bare consumability
(reaching a step where `n` is done, D9's (R2), with every recorded event
consumed, D9's (R5)) plus a separately-derived T1: bare consumability,
on D9's own flat-event matching, does *not* entail entry-for-entry
convergence on its own (a longer-than-recorded turn can "borrow" a
later turn's events while still reaching a consumed, done state — see
the counterexample in `implementation-deviations.md`), so stating
convergence directly is the honest hypothesis to work from. -/
def ConvergentReplay {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [DecidableEq MethodName] [DecidableEq Args]
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (B : Boundary) : Prop :=
  ConvergentReplayWith (fun a b => a = b) R₁ E₂ adapterView driverView B

/-- Per-turn alignment: whenever replaying exactly `k` steps for node `n`
succeeds, the cursor it lands on is exactly the event-count `E₁`'s own
compilation of the replayed prefix produces — ruling out the "borrowed
call" ambiguity that bare `ConvergentReplay` (checked only at the full
length) leaves open on its own. Combined with `ConvergentReplay`
(`replayEvWith_prefix` identifies the replayed prefix as `R₁`'s own recording,
turn for turn), this pins the cursor down turn by turn, not just at the
end. -/
def PerTurnAligned {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [DecidableEq MethodName] [DecidableEq Args]
    {P : Project Nodes FQN Query Relation} {E₁ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (E₂ : Engine FQN Query MethodName Args)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (B : Boundary) : Prop :=
  PerTurnAlignedWith (fun a b => a = b) R₁ E₂ adapterView driverView B

/-- `ConvergentReplay` + `PerTurnAligned` recover `(A)` at the `CallView`
level, turn by turn: no "borrowed call" ambiguity survives once the
cursor is pinned to the *true* per-turn event count at every step, not
just at the end. -/
theorem callsB_agree_of_aligned {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [DecidableEq MethodName] [DecidableEq Args]
    {P : Project Nodes FQN Query Relation} {E₁ E₂ : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀)
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args) (B : Boundary)
    (hCV : ConvergentReplay R₁ E₂ adapterView driverView B)
    (hAl : PerTurnAligned R₁ E₂ adapterView driverView B) :
    ∀ j, 1 ≤ j → j ≤ R₁.N →
      callsB E₁ adapterView driverView B (R₁.stmt j) = callsB E₂ adapterView driverView B (R₁.stmt j) :=
  fun j hj1 hjN => LForall₂.eq_of
    (callsB_agree_of_aligned_with (fun a b => a = b) R₁ adapterView driverView B hCV hAl j hj1 hjN)

def TargetFaithful {FQN Query MethodName Args : Type}
    (E : Engine FQN Query MethodName Args) : Prop :=
  (∀ o q o' q', Statement.write o' q' ∈ drvE E (Statement.write o q) → o' = o) ∧
  (∀ q o' q', Statement.write o' q' ∉ drvE E (Statement.read q))

/-- DAG-order (D3): every read of an FQN written by some *other node* in
this run comes after that write, checked against the realized sequence.

The inner turn `j` is exempted whenever it shares `j'`'s node
(`R.node j = R.node j'`), not just when `j = j'`. Same-turn self-reference
(`j = j'`, e.g. an incremental model's self-referential `Write(o,q)` with
`q` reading `o`) would otherwise force `j' < j'` — but the *same* problem
recurs, one level up, for a node's own check-then-write idiom (a read of
`o` at one turn, that same node's write of `o` at a *different* turn):
blanket `DAGOrder` would demand the write precede the read, which is
false whenever the check comes first (as it structurally must — the
whole point of checking is to decide *whether* to write). Exempting same
-node pairs entirely (not just identical turns) covers both: a node's own
turn ordering is fixed by construction in every schedule (`next(n,H)`'s
`k`-th and `(k+1)`-th turns are never reordered relative to each other),
so there's no scheduling freedom for `DAGOrder` to protect against there
— the divergence `DAGOrder` exists to rule out only arises from *cross*
-node interleaving choices. `stateAt_eq_SFinal_of_reads` still needs its
own `target stmt ≠ some o` side condition (the same-turn case); the
same-node-different-turn case is instead resolved directly from
`NodeAgreeConclusion` (`stateAt_other_agree`), with no reference to
`DAGOrder` at all. -/
def DAGOrder {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes]
    (reads : Statement FQN Query → FQN → Prop)
    {P : Project Nodes FQN Query Relation} {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) : Prop :=
  ∀ j', 1 ≤ j' → j' ≤ R.N → ∀ o, reads (R.stmt j') o →
    ∀ j, 1 ≤ j → j ≤ R.N → R.node j ≠ R.node j' → target (R.stmt j) = some o → j < j'

/-- A statement's own embedded query — `def` for a write, `query` for a
read (D1). -/
def qOf {FQN Query : Type} : Statement FQN Query → Query
  | .write _ q => q
  | .read q => q

/-- `(reads-sound)`: `reads` is a sound over-approximation of what `ret`
actually depends on — the hypothesis found missing during mechanization
(see accompanying report) and since added to `formalization-1.md`. Without
it, DAG-order's own claimed schedule-independence is false: a `reads` that
under-reports lets DAG-order admit two schedules that place an
under-reported FQN's writer on either side of a read that secretly depends
on it, yielding different results (concrete counterexample in the report).

Stated for `stmt`'s own query (`qOf stmt`), matching the prose ("for the
stmt whose (compiled) query is q") — not for an independent `q` unrelated
to `stmt`, which would ask `ret` to be insensitive to state differences
outside `reads(stmt)` even when the query has nothing to do with `stmt`.
Applying this to a *compiled* call (itself a `Statement`, since
`DriverCall = Statement`) needs `CompiledReadsSound` to first relate the
compiled call's own reads back to the abstract statement's. -/
def ReadsSound {FQN Query Relation : Type}
    (reads : Statement FQN Query → FQN → Prop)
    (ret : State FQN Relation → Query → Relation) : Prop :=
  ∀ (stmt : Statement FQN Query) (S S' : State FQN Relation),
    (∀ o, reads stmt o → S o = S' o) → ret S (qOf stmt) = ret S' (qOf stmt)

/-! ## Static DAG-order (project-level), replacing per-run DAG-order for the
part of T2's argument that per-run DAG-order cannot support

Counterexample found during mechanization (see report): two nodes each
conditionally write their own target *iff* the other's target does not yet
exist. In any one run, at most one of the two writes ever fires, so the
*realized* sequence trivially satisfies per-run DAG-order — but which one
fires depends on scheduling, so `O(R₁) ≠ O(R₂)` for two live runs of the
*same* engine. Per-run DAG-order cannot see this because it only checks
what happened to be realized, not what the project's `next` could produce
for other, un-taken branches. `StaticPrec` fixes this by relating FQNs
through `next`'s full behavior (quantified over *all* histories, not just
realized ones); requiring it well-founded excludes exactly this project
(`oB ≺ₛ oA` and `oA ≺ₛ oB` simultaneously — a 2-cycle) before any run or
schedule is even considered. -/

/-- `o₁ ≺ₛ o₂` iff `o₁ ≠ o₂` and *some node* has, for some reachable
history, a turn reading `o₁`, and (for some, possibly different,
history) writes `o₂`. The node is shared between the two conjuncts
(only the history may differ) — this is what the prose states; a
version with independent existentials over the node is nearly
tautological (any read-somewhere paired with any write-somewhere),
which breaks well-foundedness for ordinary projects. The `o₁ ≠ o₂`
guard is needed on top of that: without it, a node that reads its own
eventual write-target (e.g. an incremental model reading its own
current table) makes `o ≺ₛ o` hold, which alone defeats well-
foundedness regardless of the node-sharing fix. -/
def StaticPrec {Nodes FQN Query Relation : Type}
    (reads : Statement FQN Query → FQN → Prop)
    (P : Project Nodes FQN Query Relation) (o₁ o₂ : FQN) : Prop :=
  o₁ ≠ o₂ ∧
  ∃ n, (∃ H stmt, P.nxt n H = some stmt ∧ reads stmt o₁) ∧
       (∃ H q, P.nxt n H = some (Statement.write o₂ q))

/-- Global single-writer-per-FQN: at most one node can *ever* (for any
history) realize a write to a given FQN — a project-level property. This is
the *only* single-writer hypothesis T2 needs: an earlier per-run,
position-uniqueness version (at most one *position* in one run targets a
given FQN) turned out to be unnecessary — see `writeChainAgree`, which
handles an FQN written more than once within a run (e.g. a drop-then-recreate
materialization) via the *last* writer rather than assuming a unique one. -/
def UniqueWriterGlobal {Nodes FQN Query Relation : Type}
    (P : Project Nodes FQN Query Relation) : Prop :=
  ∀ o n₁ n₂ H₁ H₂ q₁ q₂,
    P.nxt n₁ H₁ = some (Statement.write o q₁) →
    P.nxt n₂ H₂ = some (Statement.write o q₂) → n₁ = n₂

/-- `exec` at a `Write` only ever changes state at that write's own target
(directly from `execS`'s definition, D2). -/
theorem execS_preserve {FQN Query Relation : Type} [DecidableEq FQN]
    (ret : State FQN Relation → Query → Relation) (S : State FQN Relation)
    (stmt : Statement FQN Query) (o : FQN) (h : target stmt ≠ some o) :
    execS ret S stmt o = S o := by
  cases stmt with
  | write o' q =>
    have hne : o ≠ o' := fun heq => h (heq ▸ rfl)
    simp [execS, hne]
  | read q => rfl

/-- Compiled-call-level reads-soundness: every compiled call `c` a
statement realizes to reads no more than the abstract statement itself
declares. `reads` (D1) is asserted only at the abstract level; nothing
otherwise connects it to what a *compiled* realization actually reads,
which is needed once a single statement can compile to several calls
(D5) and one of those calls' own query needs `ReadsSound` applied to
it directly. -/
def CompiledReadsSound {FQN Query MethodName Args : Type}
    (reads : Statement FQN Query → FQN → Prop)
    (E : Engine FQN Query MethodName Args) : Prop :=
  ∀ stmt c, c ∈ drvE E stmt → ∀ o, reads c o → reads stmt o

/-! ## Level-generic machinery (adapter and driver boundaries share one argument) -/

/-- One boundary's call-level semantics. Driver level: `Call := Statement`,
`step := execS ret`, `ans S (read q) := some (ret S q)`. Adapter level: `Call :=
AdapterCall`, `step := stepA`, `ans := retA`. -/
structure Level (FQN Relation : Type) where
  Call : Type
  step : State FQN Relation → Call → State FQN Relation
  ans : State FQN Relation → Call → Option Relation
  target : Call → Option FQN
  reads : Call → FQN → Prop

/-- How an engine compiles a statement at a level (`drvE E` / `E.α`). -/
abbrev Comp (FQN Query Relation : Type) (L : Level FQN Relation) :=
  Statement FQN Query → List L.Call

def execL {FQN Query Relation : Type} {L : Level FQN Relation}
    (comp : Comp FQN Query Relation L) (S : State FQN Relation)
    (stmt : Statement FQN Query) : State FQN Relation :=
  (comp stmt).foldl L.step S

def rL {FQN Query Relation : Type} {L : Level FQN Relation}
    (comp : Comp FQN Query Relation L) (S : State FQN Relation) :
    Statement FQN Query → Option (Result Relation)
  | .write _ _ => some Result.ok
  | .read q =>
      match (comp (Statement.read q)).getLast? with
      | some c => (L.ans S c).map Result.rel
      | none => none

def stateAtL {FQN Query Relation : Type} {L : Level FQN Relation}
    (comp : Comp FQN Query Relation L) (stmt : Nat → Statement FQN Query)
    (S₀ : State FQN Relation) (i : Nat) : State FQN Relation :=
  (((List.range (i - 1)).map (· + 1)).map stmt).foldl (execL comp) S₀

structure LiveRunL {Nodes FQN Query Relation : Type} [DecidableEq Nodes]
    (P : Project Nodes FQN Query Relation) (L : Level FQN Relation)
    (comp : Comp FQN Query Relation L) (S₀ : State FQN Relation) where
  N : Nat
  node : Nat → Nodes
  stmt : Nat → Statement FQN Query
  res : Nat → Result Relation
  stmt_eq : ∀ i, 1 ≤ i → i ≤ N → P.nxt (node i) (histAt node stmt res (node i) i) = some (stmt i)
  res_eq : ∀ i, 1 ≤ i → i ≤ N → rL comp (stateAtL comp stmt S₀ i) (stmt i) = some (res i)
  valid2 : ∀ n, P.nxt n (histAt node stmt res n (N + 1)) = none

/-- A call changes state only at its own target. -/
def LevelPreserve {FQN Relation : Type} (L : Level FQN Relation) : Prop :=
  ∀ c S o, L.target c ≠ some o → L.step S c o = S o

/-- Generic `ReadsSound` for a level: a call changes state only at its own
target, and the value it writes there depends only on `L.reads c`. -/
structure LevelSound {FQN Relation : Type} (L : Level FQN Relation) : Prop where
  preserve : LevelPreserve L
  reads_sound : ∀ c S S', (∀ o, L.reads c o → S o = S' o) →
    ∀ t, L.target c = some t → L.step S c t = L.step S' c t
  ans_sound : ∀ c S S', (∀ o, L.reads c o → S o = S' o) → L.ans S c = L.ans S' c

/-- Generic `TargetFaithful`: every compiled call that targets anything
targets exactly its statement's target (so a `Read`'s calls never write). -/
def TargetFaithfulL {FQN Query Relation : Type} {L : Level FQN Relation}
    (comp : Comp FQN Query Relation L) : Prop :=
  ∀ stmt c, c ∈ comp stmt → L.target c ≠ none → L.target c = target stmt

/-- Generic `CompiledReadsSound`. -/
def CompiledReadsSoundL {FQN Query Relation : Type} {L : Level FQN Relation}
    (reads : Statement FQN Query → FQN → Prop)
    (comp : Comp FQN Query Relation L) : Prop :=
  ∀ stmt c, c ∈ comp stmt → ∀ o, L.reads c o → reads stmt o

theorem foldl_step_preserve {FQN Relation : Type} (L : Level FQN Relation) (hL : LevelPreserve L)
    (o : FQN) : ∀ (cs : List L.Call) (S : State FQN Relation),
    (∀ c ∈ cs, L.target c ≠ some o) → (cs.foldl L.step S) o = S o
  | [], _, _ => rfl
  | c :: cs, S, h => by
    simp only [List.foldl_cons]
    rw [foldl_step_preserve L hL o cs (L.step S c) (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))]
    exact hL c S o (h c List.mem_cons_self)

theorem execL_preserve {FQN Query Relation : Type} {L : Level FQN Relation} (hL : LevelPreserve L)
    {comp : Comp FQN Query Relation L} (hTF : TargetFaithfulL comp)
    (S : State FQN Relation) (stmt : Statement FQN Query) (o : FQN)
    (h : target stmt ≠ some o) : execL comp S stmt o = S o := by
  apply foldl_step_preserve L hL o
  intro c hc hco
  exact h ((hTF stmt c hc (by rw [hco]; simp)).symm.trans hco)

def SFinalL {Nodes FQN Query Relation : Type} [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {L : Level FQN Relation}
    {comp : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (R : LiveRunL P L comp S₀) : State FQN Relation :=
  stateAtL comp R.stmt S₀ (R.N + 1)

/-- Driver instance: `Call := Statement`, exactly today's `execS`/`ret`. -/
def driverLevel {FQN Query Relation : Type} [DecidableEq FQN]
    (ret : State FQN Relation → Query → Relation)
    (reads : Statement FQN Query → FQN → Prop) : Level FQN Relation where
  Call := Statement FQN Query
  step := execS ret
  ans := fun S c => match c with | .read q => some (ret S q) | .write _ _ => none
  target := target
  reads := reads

/-- Adapter instance: symmetric, with its own `stepA`, `retA`, target, reads. -/
def adapterLevel {FQN Relation MethodName Args : Type}
    (stepA : State FQN Relation → AdapterCall MethodName Args → State FQN Relation)
    (retA : State FQN Relation → AdapterCall MethodName Args → Relation)
    (targetA : AdapterCall MethodName Args → Option FQN)
    (readsA : AdapterCall MethodName Args → FQN → Prop) : Level FQN Relation where
  Call := AdapterCall MethodName Args
  step := stepA
  ans := fun S c => some (retA S c)
  target := targetA
  reads := readsA


namespace Gen

def DAGOrder {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes]
    (reads : Statement FQN Query → FQN → Prop)
    {P : Project Nodes FQN Query Relation} {comp : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R : LiveRunL P L comp S₀) : Prop :=
  ∀ j', 1 ≤ j' → j' ≤ R.N → ∀ o, reads (R.stmt j') o →
    ∀ j, 1 ≤ j → j ≤ R.N → R.node j ≠ R.node j' → target (R.stmt j) = some o → j < j'

/-- Folding `exec_E` over a list of statements none of which target `o`
preserves `o`'s value, given target-faithfulness. -/
theorem foldl_execL_preserve {FQN Query Relation : Type} {L : Level FQN Relation} {comp : Comp FQN Query Relation L} [DecidableEq FQN]
    
    (hL : LevelPreserve L) (hTF : TargetFaithfulL comp)
    (o : FQN) : ∀ (Ls : List (Statement FQN Query)) (S₀ : State FQN Relation),
    (∀ s ∈ Ls, target s ≠ some o) → (Ls.foldl (execL comp) S₀) o = S₀ o
  | [], _, _ => rfl
  | s :: ss, S₀, h => by
    simp only [List.foldl_cons]
    rw [foldl_execL_preserve hL hTF o ss (execL comp S₀ s)
      (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))]
    exact execL_preserve hL hTF S₀ s o (h s (List.mem_cons_self))

/-- `S_final` at position `i` only ever differs from `S₀` at FQNs some
realized `Write` before `i` actually targets. -/
theorem stateAt_preserve {FQN Query Relation : Type} {L : Level FQN Relation} {comp : Comp FQN Query Relation L} [DecidableEq FQN]
    (stmt : Nat → Statement FQN Query)
    
    (hL : LevelPreserve L) (hTF : TargetFaithfulL comp) (S₀ : State FQN Relation) (i : Nat) (o : FQN)
    (h : ∀ j, 1 ≤ j → j < i → target (stmt j) ≠ some o) :
    stateAtL comp stmt S₀ i o = S₀ o := by
  simp only [stateAtL]
  apply foldl_execL_preserve hL hTF o
  intro s hs
  simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hs
  obtain ⟨j, hjlt, hjeq⟩ := hs
  exact hjeq ▸ h (j + 1) (by omega) (by omega)

/-- `S(m+1)` is `S(m)` folded one more step by position `m`'s statement,
for any *realized* position `m ≥ 1` (the same off-by-one guard as
`histAt`/`turnCount`: position `0` is junk). -/
theorem stateAt_succ {FQN Query Relation : Type} {L : Level FQN Relation} {comp : Comp FQN Query Relation L} [DecidableEq FQN]
    (stmt : Nat → Statement FQN Query)
    
    (S₀ : State FQN Relation) (m : Nat) (hm : 1 ≤ m) :
    stateAtL comp stmt S₀ (m + 1) = execL comp (stateAtL comp stmt S₀ m) (stmt m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [stateAtL, Nat.add_sub_cancel_left]
  have h1 : 1 + k + 1 - 1 = k + 1 := by omega
  rw [h1, List.range_succ, List.map_append, List.map_append, List.foldl_append]
  have h2 : (1 : Nat) + k = k + 1 := by omega
  simp [h2]

/-- `S` is unchanged across any range with no write targeting `o`. -/
theorem stateAt_const_range {FQN Query Relation : Type} {L : Level FQN Relation} {comp : Comp FQN Query Relation L} [DecidableEq FQN]
    (stmt : Nat → Statement FQN Query)
    
    (hL : LevelPreserve L) (hTF : TargetFaithfulL comp) (S₀ : State FQN Relation) (o : FQN) (i₁ : Nat) (hi₁ : 1 ≤ i₁) :
    ∀ d, (∀ j, i₁ ≤ j → j < i₁ + d → target (stmt j) ≠ some o) →
      stateAtL comp stmt S₀ (i₁ + d) o = stateAtL comp stmt S₀ i₁ o
  | 0, _ => rfl
  | d + 1, h => by
    have hd : stateAtL comp stmt S₀ (i₁ + d) o = stateAtL comp stmt S₀ i₁ o :=
      stateAt_const_range stmt hL hTF S₀ o i₁ hi₁ d
        (fun j hj1 hj2 => h j hj1 (by omega))
    have hstep : stateAtL comp stmt S₀ (i₁ + d + 1) =
        execL comp (stateAtL comp stmt S₀ (i₁ + d)) (stmt (i₁ + d)) :=
      stateAt_succ stmt S₀ (i₁ + d) (by omega)
    have : i₁ + (d + 1) = i₁ + d + 1 := by omega
    rw [this, hstep, execL_preserve hL hTF _ _ o (h (i₁ + d) (by omega) (by omega)), hd]

/-- The largest position `≤ N` satisfying a decidable predicate, given that
some position does — used below to reason about "the *last* write to `o`"
rather than assuming there is only one (which would rule out, e.g., a
drop-then-recreate materialization realized as two `Write`s to the same
target within one run). -/
theorem exists_greatest_le (Pr : Nat → Prop) [DecidablePred Pr] :
    ∀ N, (∃ p, p ≤ N ∧ Pr p) → ∃ p, p ≤ N ∧ Pr p ∧ ∀ p', p' ≤ N → Pr p' → p' ≤ p
  | 0, ⟨p, hpN, hp⟩ => ⟨0, Nat.le_refl 0, by rwa [Nat.le_zero.mp hpN] at hp, fun p' hp'N _ => hp'N⟩
  | N + 1, hex => by
    by_cases h : Pr (N + 1)
    · exact ⟨N + 1, Nat.le_refl _, h, fun p' hp'N _ => hp'N⟩
    · have hex' : ∃ p, p ≤ N ∧ Pr p := by
        obtain ⟨p, hpN1, hp⟩ := hex
        rcases Nat.lt_or_ge p (N + 1) with hlt | hge
        · exact ⟨p, by omega, hp⟩
        · exfalso
          have heq : p = N + 1 := by omega
          rw [heq] at hp
          exact h hp
      obtain ⟨p, hpN, hp, hmax⟩ := exists_greatest_le Pr N hex'
      refine ⟨p, by omega, hp, fun p' hp'N1 hp' => ?_⟩
      rcases Nat.lt_or_ge p' (N + 1) with hlt | hge
      · exact Nat.le_trans (hmax p' (by omega) hp') (by omega)
      · exfalso
        have heq : p' = N + 1 := by omega
        rw [heq] at hp'
        exact h hp'

/-- The state a read at position `j` (of node `n = R.node j`) sees for any
`o' ∈ reads(R.stmt j)` equals `S_final(R)(o')`: if `o'` has an in-run writer,
DAG-order places it before `j` and target-faithfulness mean nothing *after
the last such writer* ever touches `o'` again — we use only the *last*
writer, not uniqueness of the writer, so this holds even if `o'` is written
more than once within the run; if `o'` has no writer at all,
both are `S₀(o')`.

Requires `¬ ∃ H q, P.nxt (R.node j) H = some (Statement.write o' q)` — `j`'s
own node isn't `o'`'s candidate writer. Needed because `DAGOrder`
exempts same-node reader/writer pairs entirely (not just identical
turns, matching a node's own check-then-write idiom): without this
hypothesis, `o'`'s writer could be a *different* turn of `j`'s own node,
which `DAGOrder` no longer places before `j` — and the claim would be
false there regardless (the read sees the *pre*-write state, not
`SFinalL`), same failure mode as the same-turn case. That same-node case
is resolved separately, via `NodeAgreeConclusion` directly
(`stateAt_other_agree`), not through this lemma. -/
theorem stateAt_eq_SFinal_of_reads {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {comp : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R : LiveRunL P L comp S₀) (hL : LevelPreserve L) (hTF : TargetFaithfulL comp)
    (reads : Statement FQN Query → FQN → Prop) (hDAG : DAGOrder reads R)
    (j : Nat) (hj1 : 1 ≤ j) (hjN : j ≤ R.N) (o' : FQN) (hro' : reads (R.stmt j) o')
    (hnsw : ¬ ∃ H q, P.nxt (R.node j) H = some (Statement.write o' q)) :
    stateAtL comp R.stmt S₀ j o' = SFinalL R o' := by
  by_cases hw : ∃ p, 1 ≤ p ∧ p ≤ R.N ∧ target (R.stmt p) = some o'
  · obtain ⟨p, hpN, ⟨hp1, hpt⟩, hmax⟩ :=
      exists_greatest_le (fun p => 1 ≤ p ∧ target (R.stmt p) = some o') R.N
        (by obtain ⟨p, hp1, hpN, hpt⟩ := hw; exact ⟨p, hpN, hp1, hpt⟩)
    have hnodediff : R.node p ≠ R.node j := by
      intro heq
      apply hnsw
      cases hcs : R.stmt p with
      | write o'' q'' =>
        have hoeq : o'' = o' := by rw [hcs, target] at hpt; injection hpt
        have hnxtp := R.stmt_eq p hp1 hpN
        rw [hcs, heq] at hnxtp
        exact ⟨histAt R.node R.stmt R.res (R.node j) p, q'', by rw [hoeq] at hnxtp; exact hnxtp⟩
      | read _ => rw [hcs, target] at hpt; exact absurd hpt (by simp)
    have hpj : p < j := hDAG j hj1 hjN o' hro' p hp1 hpN hnodediff hpt
    have h1 : stateAtL comp R.stmt S₀ j o' = stateAtL comp R.stmt S₀ (p + 1) o' := by
      have := stateAt_const_range R.stmt hL hTF S₀ o' (p + 1) (by omega) (j - (p + 1))
        (fun q hq1 hq2 heq => by have := hmax q (by omega) ⟨by omega, heq⟩; omega)
      rwa [show p + 1 + (j - (p+1)) = j from by omega] at this
    have h2 : SFinalL R o' = stateAtL comp R.stmt S₀ (p + 1) o' := by
      simp only [SFinalL]
      have := stateAt_const_range R.stmt hL hTF S₀ o' (p + 1) (by omega) (R.N + 1 - (p + 1))
        (fun q hq1 hq2 heq => by have := hmax q (by omega) ⟨by omega, heq⟩; omega)
      rwa [show p + 1 + (R.N + 1 - (p+1)) = R.N + 1 from by omega] at this
    rw [h1, h2]
  · have hw' : ∀ q, 1 ≤ q → q ≤ R.N → target (R.stmt q) ≠ some o' :=
      fun q hq1 hqN heq => hw ⟨q, hq1, hqN, heq⟩
    have h1 : stateAtL comp R.stmt S₀ j o' = S₀ o' :=
      stateAt_preserve R.stmt hL hTF S₀ j o' (fun q hq1 hq2 => hw' q hq1 (by omega))
    have h2 : SFinalL R o' = S₀ o' := by
      simp only [SFinalL]
      exact stateAt_preserve R.stmt hL hTF S₀ (R.N + 1) o' (fun q hq1 hq2 => hw' q hq1 (by omega))
    rw [h1, h2]

/-- If `n` has had zero turns before position `j`, nobody has written `o`
before `j` either — `n` is `o`'s only possible writer (`UniqueWriterGlobal`
+ `hCandidate`), and if some *other* position `p < j` had written `o`, that
position would have to belong to `n` too, contradicting the zero turn
count. Used for `StaticPrec`'s excluded `o' = o` case: a node reading its
own eventual write-target, before ever having written it, just reads the
untouched `S₀`. -/
theorem noWriteBefore_of_turnCount_zero {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {comp : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R : LiveRunL P L comp S₀) (hUWG : UniqueWriterGlobal P)
    (n : Nodes) (o : FQN) (hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q))
    (j : Nat) (hjle : j ≤ R.N + 1) (hjcount : turnCount R.node n j = 0) :
    ∀ p, 1 ≤ p → p < j → target (R.stmt p) ≠ some o := by
  intro p hp1 hpj heq
  have hpN : p ≤ R.N := by omega
  obtain ⟨Hc, qc, hHc⟩ := hCandidate
  have hpeq := R.stmt_eq p hp1 hpN
  cases hst : R.stmt p with
  | write t q =>
    rw [hst] at heq hpeq
    simp only [target] at heq
    have ht : t = o := by injection heq
    rw [ht] at hpeq
    have hnp : R.node p = n := hUWG o (R.node p) n _ Hc q qc hpeq hHc
    have hstep : turnCount R.node n (p + 1) = turnCount R.node n p + 1 := by
      simp only [turnCount, hp1, hnp, and_self, ite_true]
    have hmono : turnCount R.node n (p + 1) ≤ turnCount R.node n j :=
      turnCount_mono R.node n (by omega)
    omega
  | read q => rw [hst] at heq; simp [target] at heq

/-- Wraps `noWriteBefore_of_turnCount_zero` via `stateAt_preserve`: state at
`o` at position `j` is still `S₀ o` when `n` (`o`'s only possible writer)
hasn't had a turn yet. -/
theorem stateAtEq_of_turnCount_zero {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {comp : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R : LiveRunL P L comp S₀) (hL : LevelPreserve L) (hTF : TargetFaithfulL comp) (hUWG : UniqueWriterGlobal P)
    (n : Nodes) (o : FQN) (hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q))
    (j : Nat) (hjle : j ≤ R.N + 1) (hjcount : turnCount R.node n j = 0) :
    stateAtL comp R.stmt S₀ j o = S₀ o :=
  stateAt_preserve R.stmt hL hTF S₀ j o
    (noWriteBefore_of_turnCount_zero R hUWG n o hCandidate j hjle hjcount)

/-- Generalizes `noWriteBefore_of_turnCount_zero` to an arbitrary range:
if `n`'s turn count hasn't moved between positions `a` and `b`, nobody
wrote `o` (n's only possible writer) anywhere in `[a, b)` either — same
argument, just anchored at `a` instead of at the start. -/
theorem noWriteInRange_of_turnCount_eq {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {comp : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R : LiveRunL P L comp S₀) (hUWG : UniqueWriterGlobal P)
    (n : Nodes) (o : FQN) (hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q))
    (a b : Nat) (ha1 : 1 ≤ a) (hble : b ≤ R.N + 1)
    (hcount : turnCount R.node n a = turnCount R.node n b) :
    ∀ p, a ≤ p → p < b → target (R.stmt p) ≠ some o := by
  intro p hpa hpb heq
  have hpN : p ≤ R.N := by omega
  have hp1 : 1 ≤ p := by omega
  obtain ⟨Hc, qc, hHc⟩ := hCandidate
  have hpeq := R.stmt_eq p hp1 hpN
  cases hst : R.stmt p with
  | write t q =>
    rw [hst] at heq hpeq
    simp only [target] at heq
    have ht : t = o := by injection heq
    rw [ht] at hpeq
    have hnp : R.node p = n := hUWG o (R.node p) n _ Hc q qc hpeq hHc
    have hstep : turnCount R.node n (p + 1) = turnCount R.node n p + 1 := by
      simp only [turnCount, hp1, hnp, and_self, ite_true]
    have hmono1 : turnCount R.node n a ≤ turnCount R.node n p :=
      turnCount_mono R.node n (by omega)
    have hmono2 : turnCount R.node n (p + 1) ≤ turnCount R.node n b :=
      turnCount_mono R.node n (by omega)
    omega
  | read q => rw [hst] at heq; simp [target] at heq

/-- Wraps `noWriteInRange_of_turnCount_eq` via `stateAt_const_range`: state
at `o` is unchanged between two positions bracketing no turn of `o`'s
only possible writer. -/
theorem stateAtEq_of_turnCount_eq {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {comp : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R : LiveRunL P L comp S₀) (hL : LevelPreserve L) (hTF : TargetFaithfulL comp) (hUWG : UniqueWriterGlobal P)
    (n : Nodes) (o : FQN) (hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q))
    (a b : Nat) (ha1 : 1 ≤ a) (hab : a ≤ b) (hble : b ≤ R.N + 1)
    (hcount : turnCount R.node n a = turnCount R.node n b) :
    stateAtL comp R.stmt S₀ b o = stateAtL comp R.stmt S₀ a o := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact stateAt_const_range R.stmt hL hTF S₀ o a ha1 d
    (fun p hp1 hp2 => noWriteInRange_of_turnCount_eq R hUWG n o hCandidate a (a + d) ha1 hble hcount p hp1 hp2)

/-- Any position targeting `o` must be node `n`'s turn, given `n` is `o`'s
(global) candidate writer. -/
theorem nodeOfWriter {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes]
    {P : Project Nodes FQN Query Relation} {comp : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R : LiveRunL P L comp S₀) (hUWG : UniqueWriterGlobal P) (n : Nodes) (o : FQN)
    (hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q)) :
    ∀ p, 1 ≤ p → p ≤ R.N → target (R.stmt p) = some o → R.node p = n := by
  obtain ⟨Hc, qc, hHc⟩ := hCandidate
  intro p hp1 hpN heq
  cases hcs : R.stmt p with
  | write o' q' =>
    rw [hcs, target] at heq
    have ho' : o' = o := by injection heq
    have hnxt := R.stmt_eq p hp1 hpN
    rw [hcs] at hnxt
    exact hUWG o (R.node p) n (histAt R.node R.stmt R.res (R.node p) p) Hc q' qc
      (by rw [← ho']; exact hnxt) hHc
  | read _ => rw [hcs, target] at heq; exact absurd heq (by simp)

/-! ## Deriving `(A)` from consumability at the `adapter→driver` boundary

`T2_2_of_A` above takes `(A)` as a hypothesis. The source's actual T2₂
instead assumes `ρ = τ_{adapter→driver}(R₁)` is consumable for some replay of
`E₂`, and *derives* `(A)` from it via T1 plus (R4)'s matching. We mechanize
that derivation here: `List.map`'s injectivity lets us strip `driverView`'s
`CallView` projection off the equality `callsB` supplies at each replayed
turn, recovering the raw `drv_E` equality `(A)` needs. -/

end Gen

/-! # Equivalence-parametrized T2 core

The T2 argument, stated once for any boundary (`Level`) and up to an abstract
equivalence `~_R` on `Relation` (and `~` on calls). Module 1 uses it with `≈`
:= `=` (`T2_of_A_eq` below); Modules 2–4 use it with a normalization setoid. -/

namespace Eqv

/-! ## Value-level equivalences -/

def ResEquiv {Relation : Type} [Setoid Relation] : Result Relation → Result Relation → Prop
  | .ok, .ok => True
  | .rel r, .rel r' => r ≈ r'
  | _, _ => False

theorem ResEquiv.refl {Relation : Type} [Setoid Relation] (r : Result Relation) :
    ResEquiv r r := by cases r with
  | rel r => exact Setoid.refl r
  | ok => trivial

theorem ResEquiv.symm {Relation : Type} [Setoid Relation] {r r' : Result Relation}
    (h : ResEquiv r r') : ResEquiv r' r := by
  cases r <;> cases r' <;> first | exact h.elim | trivial | exact Setoid.symm h

def OptEquiv {Relation : Type} [Setoid Relation] : Option Relation → Option Relation → Prop
  | none, none => True
  | some r, some r' => r ≈ r'
  | _, _ => False

theorem OptEquiv.refl {Relation : Type} [Setoid Relation] (r : Option Relation) :
    OptEquiv r r := by cases r with
  | none => trivial
  | some r => exact Setoid.refl r

theorem OptEquiv.symm {Relation : Type} [Setoid Relation] {r r' : Option Relation}
    (h : OptEquiv r r') : OptEquiv r' r := by
  cases r <;> cases r' <;> first | exact h.elim | trivial | exact Setoid.symm h

theorem OptEquiv.trans {Relation : Type} [Setoid Relation] {r r' r'' : Option Relation}
    (h1 : OptEquiv r r') (h2 : OptEquiv r' r'') : OptEquiv r r'' := by
  cases r <;> cases r' <;> cases r'' <;>
    first | exact h1.elim | exact h2.elim | trivial | exact Setoid.trans h1 h2

def StateEquiv {FQN Relation : Type} [Setoid Relation]
    (S S' : State FQN Relation) : Prop := ∀ o, OptEquiv (S o) (S' o)

def HistEquiv {FQN Query Relation : Type} [Setoid Relation]
    (H H' : History FQN Query Relation) : Prop :=
  LForall₂ (fun a b => a.1 = b.1 ∧ ResEquiv a.2 b.2) H H'

/-- `NextTildeInsensitive`: `next` does not distinguish histories that differ
only in normalization-erased result noise. -/
def NextTildeInsensitive {Nodes FQN Query Relation : Type} [Setoid Relation]
    (P : Project Nodes FQN Query Relation) : Prop :=
  ∀ n H H', HistEquiv H H' → P.nxt n H = P.nxt n H'

/-! ## Level soundness, up to equivalence

`LevelSoundT L` is the equivalence-parametrized form of `LevelSound`: the same
promises (a call is a function of its declared reads, effects only at its
target), but agreement is `~_R`-agreement, plus two congruences: `~`-related
calls have the same target and the same effect/answer on the *same* state. With
`≈` = equality it collapses to `LevelSound`. -/
structure LevelSoundT {FQN Relation : Type} [Setoid Relation] (L : Level FQN Relation)
    [Setoid L.Call] : Prop where
  preserve : LevelPreserve L
  target_pres : ∀ c c' : L.Call, c ≈ c' → L.target c = L.target c'
  reads_sound : ∀ c S S', (∀ o, L.reads c o → OptEquiv (S o) (S' o)) →
    ∀ t, L.target c = some t → OptEquiv (L.step S c t) (L.step S' c t)
  ans_sound : ∀ c S S', (∀ o, L.reads c o → OptEquiv (S o) (S' o)) →
    OptEquiv (L.ans S c) (L.ans S' c)
  step_congr : ∀ c c', c ≈ c' → ∀ S t, L.target c = some t →
    OptEquiv (L.step S c t) (L.step S c' t)
  ans_congr : ∀ c c', c ≈ c' → ∀ S, OptEquiv (L.ans S c) (L.ans S c')

/-! ## Effect calls

A compilation's *effect calls* are the calls that have a target. Every other
call leaves the state untouched (`LevelPreserve`), so a turn's effect on state
is determined by its effect calls alone. The write-turn hypothesis `hAWrite` of
the T2 core is stated over them: it asks for `~`-agreement of the calls that
change state, not of every call a turn makes. -/

/-- The calls of `cs` that have a target. -/
def effCalls {FQN Relation : Type} (L : Level FQN Relation) (cs : List L.Call) : List L.Call :=
  cs.filter (fun c => (L.target c).isSome)

theorem foldl_effCalls {FQN Relation : Type} (L : Level FQN Relation) (hL : LevelPreserve L) :
    ∀ (cs : List L.Call) (S : State FQN Relation),
      cs.foldl L.step S = (effCalls L cs).foldl L.step S
  | [], S => rfl
  | c :: cs, S => by
    by_cases ht : (L.target c).isSome
    · simp only [effCalls, List.filter_cons, ht, ite_true, List.foldl_cons]
      exact foldl_effCalls L hL cs (L.step S c)
    · have hn : L.target c = none := by simpa using ht
      have hS : L.step S c = S := funext fun o => hL c S o (by rw [hn]; simp)
      simp only [effCalls, List.filter_cons, ht, List.foldl_cons, hS]
      exact foldl_effCalls L hL cs S

theorem effCalls_congr {FQN Relation : Type} [Setoid Relation]
    {L : Level FQN Relation} [Setoid L.Call] (hL : LevelSoundT L) :
    ∀ {cs cs' : List L.Call}, LForall₂ (· ≈ ·) cs cs' →
      LForall₂ (· ≈ ·) (effCalls L cs) (effCalls L cs')
  | _, _, .nil => .nil
  | _, _, @LForall₂.cons _ _ _ a b l l' hab hrest => by
    have ht : L.target a = L.target b := hL.target_pres a b hab
    by_cases hs : (L.target a).isSome
    · have hs' : (L.target b).isSome := by rw [← ht]; exact hs
      simp only [effCalls, List.filter_cons, hs, hs', ite_true]
      exact .cons hab (effCalls_congr hL hrest)
    · have hs' : ¬ (L.target b).isSome := by rw [← ht]; exact hs
      simp only [effCalls, List.filter_cons, hs, hs']
      exact effCalls_congr hL hrest

/-! ## The generic per-turn result step and exec-agreement lemmas -/

theorem stepAgree {FQN Query Relation : Type} [Setoid Relation]
    {L : Level FQN Relation} [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    {comp₁ comp₂ : Comp FQN Query Relation L}
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (stmtV : Statement FQN Query) (S₁ S₂ : State FQN Relation)
    (hSagree : ∀ o', reads stmtV o' → OptEquiv (S₁ o') (S₂ o'))
    (hA : LForall₂ (· ≈ ·) (comp₁ stmtV) (comp₂ stmtV))
    (r₁ r₂ : Result Relation)
    (h1 : rL comp₁ S₁ stmtV = some r₁) (h2 : rL comp₂ S₂ stmtV = some r₂) :
    ResEquiv r₁ r₂ := by
  cases stmtV with
  | write o q =>
    simp only [rL] at h1 h2
    rw [← Option.some.inj h1, ← Option.some.inj h2]
    trivial
  | read q =>
    simp only [rL] at h1 h2
    rcases hA.getLast? with ⟨hn1, -⟩ | ⟨a, b, ha, hb, hab⟩
    · rw [hn1] at h1; simp at h1
    · rw [ha] at h1
      rw [hb] at h2
      simp only [Option.map_eq_some_iff] at h1 h2
      obtain ⟨x₁, hx₁, rfl⟩ := h1
      obtain ⟨x₂, hx₂, rfl⟩ := h2
      have hmem : a ∈ comp₁ (Statement.read q) := List.mem_of_getLast? ha
      have e1 := hL.ans_sound a S₁ S₂ (fun o ho => hSagree o (hCRS1 _ a hmem o ho))
      have e2 := hL.ans_congr a b hab S₂
      have := OptEquiv.trans e1 e2
      rw [hx₁, hx₂] at this
      exact this

theorem foldl_step_preserveT {FQN Relation : Type} [Setoid Relation]
    {L : Level FQN Relation} [Setoid L.Call] (hL : LevelSoundT L) (ot : FQN) :
    ∀ (cs cs' : List L.Call), LForall₂ (· ≈ ·) cs cs' →
    (∀ c ∈ cs, L.target c ≠ some ot) →
    ∀ S₁ S₂ : State FQN Relation, OptEquiv (S₁ ot) (S₂ ot) →
    OptEquiv (cs.foldl L.step S₁ ot) (cs'.foldl L.step S₂ ot) := by
  intro cs cs' hcc
  induction hcc with
  | nil => intro _ S₁ S₂ h; exact h
  | @cons c c' cs cs' hcc' hrest ih =>
    intro hLt S₁ S₂ h
    have hc : L.target c ≠ some ot := hLt c List.mem_cons_self
    have hc' : L.target c' ≠ some ot := by rw [← hL.target_pres c c' hcc']; exact hc
    simp only [List.foldl_cons]
    refine ih (fun x hx => hLt x (List.mem_cons_of_mem c hx)) _ _ ?_
    rw [hL.preserve c S₁ ot hc, hL.preserve c' S₂ ot hc']
    exact h

theorem foldl_step_maintainT {FQN Query Relation : Type} [Setoid Relation]
    {L : Level FQN Relation} [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop} {comp₁ : Comp FQN Query Relation L}
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (stmt : Statement FQN Query) (o : FQN) :
    ∀ (cs cs' : List L.Call), LForall₂ (· ≈ ·) cs cs' →
    (∀ c ∈ cs, L.target c = some o ∨ L.target c = none) →
    (∀ c ∈ cs, c ∈ comp₁ stmt) →
    ∀ S₁ S₂ : State FQN Relation,
    (∀ o', reads stmt o' → OptEquiv (S₁ o') (S₂ o')) → OptEquiv (S₁ o) (S₂ o) →
    (∀ o', reads stmt o' → OptEquiv (cs.foldl L.step S₁ o') (cs'.foldl L.step S₂ o')) ∧
    OptEquiv (cs.foldl L.step S₁ o) (cs'.foldl L.step S₂ o) := by
  intro cs cs' hcc
  induction hcc with
  | nil => intro _ _ S₁ S₂ hagree hoagree; exact ⟨hagree, hoagree⟩
  | @cons c c' cs cs' hcc' hrest ih =>
    intro hLtarget hLmem S₁ S₂ hagree hoagree
    have hcex : L.target c = some o ∨ L.target c = none := hLtarget c List.mem_cons_self
    have hcmem : c ∈ comp₁ stmt := hLmem c List.mem_cons_self
    have htgt' : L.target c' = L.target c := (hL.target_pres c c' hcc').symm
    have hoagree' : OptEquiv (L.step S₁ c o) (L.step S₂ c' o) := by
      by_cases ht : L.target c = some o
      · have e1 := hL.reads_sound c S₁ S₂
          (fun o' ho' => hagree o' (hCRS1 stmt c hcmem o' ho')) o ht
        have e2 := hL.step_congr c c' hcc' S₂ o ht
        exact OptEquiv.trans e1 e2
      · have hn : L.target c' ≠ some o := by rw [htgt']; exact ht
        rw [hL.preserve c S₁ o ht, hL.preserve c' S₂ o hn]
        exact hoagree
    have hagree' : ∀ o', reads stmt o' →
        OptEquiv (L.step S₁ c o') (L.step S₂ c' o') := by
      intro o' ho'
      by_cases hne : o' = o
      · rw [hne]; exact hoagree'
      · have hcne : L.target c ≠ some o' := by
          rcases hcex with h | h
          · rw [h]; intro heq; exact hne (Option.some.inj heq).symm
          · rw [h]; simp
        have hcne' : L.target c' ≠ some o' := by rw [htgt']; exact hcne
        rw [hL.preserve c S₁ o' hcne, hL.preserve c' S₂ o' hcne']
        exact hagree o' ho'
    simp only [List.foldl_cons]
    exact ih (fun x hx => hLtarget x (List.mem_cons_of_mem c hx))
      (fun x hx => hLmem x (List.mem_cons_of_mem c hx)) (L.step S₁ c)
      (L.step S₂ c') hagree' hoagree'

/-- **The lockstep fold, over arbitrary call lists.** If the effect calls of `cs₁` and `cs₂` are
pointwise `≈` (`cs₁` made of calls of `comp₁ stmtV`), then from states agreeing on `stmtV`'s reads and at
`ot`, folding the two lists leaves `~_R`-equal values at `ot`. -/
theorem foldl_agreeT_lists {FQN Query Relation : Type} [Setoid Relation]
    {L : Level FQN Relation} [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    {comp₁ : Comp FQN Query Relation L}
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (hTF1 : TargetFaithfulL comp₁)
    (stmtV : Statement FQN Query) (ot : FQN) (cs₁ cs₂ : List L.Call)
    (hsub : ∀ c ∈ cs₁, c ∈ comp₁ stmtV)
    (hA : LForall₂ (· ≈ ·) (effCalls L cs₁) (effCalls L cs₂))
    (S₁ S₂ : State FQN Relation)
    (hSagree : ∀ o', reads stmtV o' → OptEquiv (S₁ o') (S₂ o'))
    (hT : OptEquiv (S₁ ot) (S₂ ot)) :
    OptEquiv (cs₁.foldl L.step S₁ ot) (cs₂.foldl L.step S₂ ot) := by
  rw [foldl_effCalls L hL.preserve cs₁ S₁, foldl_effCalls L hL.preserve cs₂ S₂]
  have hLtarget : ∀ c ∈ effCalls L cs₁, L.target c = target stmtV ∨ L.target c = none := by
    intro c hc
    have hc' : c ∈ comp₁ stmtV := hsub c (List.mem_filter.mp hc).1
    by_cases hn : L.target c = none
    · exact Or.inr hn
    · exact Or.inl (hTF1 stmtV c hc' hn)
  cases stmtV with
  | read q =>
    refine foldl_step_preserveT hL ot _ _ hA ?_ S₁ S₂ hT
    intro c hc
    rcases hLtarget c hc with h | h
    · rw [h]; simp [target]
    · rw [h]; simp
  | write ow qw =>
    by_cases hot : ot = ow
    · have hT' : OptEquiv (S₁ ow) (S₂ ow) := hot ▸ hT
      rw [hot]
      exact (foldl_step_maintainT hL hCRS1 (Statement.write ow qw) ow _ _ hA
        (fun c hc => by simpa [target] using hLtarget c hc)
        (fun c hc => hsub c (List.mem_filter.mp hc).1) S₁ S₂ hSagree hT').2
    · refine foldl_step_preserveT hL ot _ _ hA ?_ S₁ S₂ hT
      intro c hc
      rcases hLtarget c hc with h | h
      · rw [h]; simp only [target]; intro heq; exact hot (Option.some.inj heq).symm
      · rw [h]; simp

theorem execL_agreeT {FQN Query Relation : Type} [Setoid Relation]
    {L : Level FQN Relation} [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    {comp₁ comp₂ : Comp FQN Query Relation L}
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (hTF1 : TargetFaithfulL comp₁)
    (stmtV : Statement FQN Query) (ot : FQN)
    (hA : LForall₂ (· ≈ ·) (effCalls L (comp₁ stmtV)) (effCalls L (comp₂ stmtV)))
    (S₁ S₂ : State FQN Relation)
    (hSagree : ∀ o', reads stmtV o' → OptEquiv (S₁ o') (S₂ o'))
    (hT : OptEquiv (S₁ ot) (S₂ ot)) :
    OptEquiv (execL comp₁ S₁ stmtV ot) (execL comp₂ S₂ stmtV ot) := by
  simp only [execL]
  exact foldl_agreeT_lists hL hCRS1 hTF1 stmtV ot _ _ (fun c hc => hc) hA S₁ S₂ hSagree hT

/-- **Write-turn agreement.** What the T2 core needs of a write turn: from two states that agree on the
statement's reads and at a tracked object, executing the statement under `comp₁` and under `comp₂`
leaves `~_R`-equal values at the tracked object. It follows from pointwise `≈` of the effect calls
(`writeAgree_of_forall₂`, the case of Modules 1–4), and from commuting reorderings of them (Module 5). -/
def WriteAgree {FQN Query Relation : Type} [Setoid Relation] (L : Level FQN Relation)
    (reads : Statement FQN Query → FQN → Prop) (comp₁ comp₂ : Comp FQN Query Relation L)
    (stmtV : Statement FQN Query) : Prop :=
  ∀ (ot : FQN) (S₁ S₂ : State FQN Relation),
    (∀ o', reads stmtV o' → OptEquiv (S₁ o') (S₂ o')) → OptEquiv (S₁ ot) (S₂ ot) →
    OptEquiv (execL comp₁ S₁ stmtV ot) (execL comp₂ S₂ stmtV ot)

theorem writeAgree_of_forall₂ {FQN Query Relation : Type} [Setoid Relation]
    {L : Level FQN Relation} [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    {comp₁ comp₂ : Comp FQN Query Relation L}
    (hL : LevelSoundT L) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (hTF1 : TargetFaithfulL comp₁) (stmtV : Statement FQN Query)
    (hA : LForall₂ (· ≈ ·) (effCalls L (comp₁ stmtV)) (effCalls L (comp₂ stmtV))) :
    WriteAgree L reads comp₁ comp₂ stmtV :=
  fun ot S₁ S₂ hS hT => execL_agreeT hL hCRS1 hTF1 stmtV ot hA S₁ S₂ hS hT

/-! ## Behavioral equivalence, relaxed (D8′), for level-generic runs -/

def ObsEquiv {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀) : Prop :=
  (∀ n r, isObs R₁.node R₁.stmt R₁.res R₁.N n r →
      ∃ r', isObs R₂.node R₂.stmt R₂.res R₂.N n r' ∧ ResEquiv r r') ∧
  (∀ n r, isObs R₂.node R₂.stmt R₂.res R₂.N n r →
      ∃ r', isObs R₁.node R₁.stmt R₁.res R₁.N n r' ∧ ResEquiv r r')

def BehEquiv {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀) : Prop :=
  StateEquiv (SFinalL R₁) (SFinalL R₂) ∧ ObsEquiv R₁ R₂

/-! ## The chain -/

/-- `nodeAgreeT`'s own conclusion, factored out so it can be used as *input*
too — Module 1's `NodeAgreeConclusion` with results relaxed to `~_Res`,
histories to `~` (`HistEquiv`) and state values to `~_R` (`OptEquiv`), while
statements still agree *literally* (that is what `(next-~-insensitive)`
buys, and what `formalization-2.md`'s proof assumes).

As in Module 1, this bundles turn correspondence *and* per-turn state
agreement at one FQN `o` into a single inductive invariant: `valueAgreeBelow`
has to hand back this exact shape for an FQN's candidate writer, not merely
`SFinalL` agreement, so that a node's own read of some *other* FQN it also
writes (same node, different turn — the check-then-write idiom) can be
resolved from this recursively-available fact rather than from `Gen.DAGOrder`,
which no longer orders same-node pairs. -/
abbrev NodeAgreeConclusionT {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {P : Project Nodes FQN Query Relation} {comp₁ comp₂ : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀) (n : Nodes) (o : FQN) : Prop :=
  ∀ k,
    (∀ j, 1 ≤ j → j ≤ R₁.N → R₁.node j = n → turnCount R₁.node n j = k →
      ∃ i, 1 ≤ i ∧ i ≤ R₂.N ∧ R₂.node i = n ∧ turnCount R₂.node n i = k ∧
           R₁.stmt j = R₂.stmt i ∧ ResEquiv (R₁.res j) (R₂.res i) ∧
           HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
                     (histAt R₂.node R₂.stmt R₂.res n i) ∧
           OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o) (stateAtL comp₂ R₂.stmt S₀ i o)) ∧
    (∀ i, 1 ≤ i → i ≤ R₂.N → R₂.node i = n → turnCount R₂.node n i = k →
      ∃ j, 1 ≤ j ∧ j ≤ R₁.N ∧ R₁.node j = n ∧ turnCount R₁.node n j = k ∧
           R₁.stmt j = R₂.stmt i ∧ ResEquiv (R₁.res j) (R₂.res i) ∧
           HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
                     (histAt R₂.node R₂.stmt R₂.res n i) ∧
           OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o) (stateAtL comp₂ R₂.stmt S₀ i o))

/-- The conclusion of `nodeAgreeFinalT`, named so it can be passed around:
`NodeAgreeConclusionT` minus the tracked-FQN component, which the final,
`ValueAgree`-is-already-established pass neither needs nor can state (its
node need not write anything at all). -/
def TurnAgreeSpec {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {P : Project Nodes FQN Query Relation} {comp₁ comp₂ : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀) (n : Nodes) : Prop :=
  ∀ k,
    (∀ j, 1 ≤ j → j ≤ R₁.N → R₁.node j = n → turnCount R₁.node n j = k →
      ∃ i, 1 ≤ i ∧ i ≤ R₂.N ∧ R₂.node i = n ∧ turnCount R₂.node n i = k ∧
           R₁.stmt j = R₂.stmt i ∧ ResEquiv (R₁.res j) (R₂.res i) ∧
           HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
                     (histAt R₂.node R₂.stmt R₂.res n i)) ∧
    (∀ i, 1 ≤ i → i ≤ R₂.N → R₂.node i = n → turnCount R₂.node n i = k →
      ∃ j, 1 ≤ j ∧ j ≤ R₁.N ∧ R₁.node j = n ∧ turnCount R₁.node n j = k ∧
           R₁.stmt j = R₂.stmt i ∧ ResEquiv (R₁.res j) (R₂.res i) ∧
           HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
                     (histAt R₂.node R₂.stmt R₂.res n i))

/-- Module 1's `stateAt_other_agree`, relaxed. Resolves cross-engine state
agreement at a turn's read of some FQN `o'` other than the tracked target
`o`, splitting on whether the current node `n` is *also* `o'`'s candidate
writer: if it is, `Gen.DAGOrder`'s `node(i) ≠ node(i')` restriction puts no
ordering between the read and that write, so `stateAt_eq_SFinal_of_reads`
cannot apply and `valueAgreeBelow`'s packaged `NodeAgreeConclusionT` for `o'`
supplies the fact directly (turn positions matched by
`turn_position_unique`); otherwise the `StaticPrec`/`SFinalL`-bridging route
applies unchanged, with only the final `SFinalL`-to-`SFinalL` link relaxed from
`=` to `~_R` (both bridging steps stay literal — they live inside a single
run). -/
theorem stateAt_other_agreeT {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {reads : Statement FQN Query → FQN → Prop}
    
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (hLP : LevelPreserve L)
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀)
    (hTF1 : TargetFaithfulL comp₁) (hTF2 : TargetFaithfulL comp₂)
    (hDAG1 : Gen.DAGOrder reads R₁) (hDAG2 : Gen.DAGOrder reads R₂)
    (n : Nodes) (o : FQN) (hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q))
    (valueAgreeBelow : ∀ o', StaticPrec reads P o' o →
      OptEquiv (SFinalL R₁ o') (SFinalL R₂ o') ∧
      ∀ n', (∃ H q, P.nxt n' H = some (Statement.write o' q)) →
        NodeAgreeConclusionT R₁ R₂ n' o')
    (j i : Nat) (hj1 : 1 ≤ j) (hjN : j ≤ R₁.N) (hjnode : R₁.node j = n)
    (hi1 : 1 ≤ i) (hiN : i ≤ R₂.N) (hinode : R₂.node i = n)
    (hicount : turnCount R₂.node n i = turnCount R₁.node n j)
    (hnxt : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j))
    (hstmt_eq : R₁.stmt j = R₂.stmt i)
    (o' : FQN) (ho' : reads (R₁.stmt j) o') (heqo : o' ≠ o) :
    OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o') := by
  have hprec : StaticPrec reads P o' o :=
    ⟨heqo, n, ⟨histAt R₁.node R₁.stmt R₁.res n j, R₁.stmt j, hnxt, ho'⟩, hCandidate⟩
  by_cases hself : ∃ H q, P.nxt n H = some (Statement.write o' q)
  · have hconcl := (valueAgreeBelow o' hprec).2 n hself
    obtain ⟨i2, hi2_1, hi2_N, hi2_node, hi2_count, -, -, -, hstateeq⟩ :=
      (hconcl (turnCount R₁.node n j)).1 j hj1 hjN hjnode rfl
    have hii2 : i2 = i :=
      turn_position_unique R₂.node n hi2_1 hi2_node hi1 hinode (hi2_count.trans hicount.symm)
    rwa [hii2] at hstateeq
  · have hv := (valueAgreeBelow o' hprec).1
    have e1 := Gen.stateAt_eq_SFinal_of_reads R₁ hLP hTF1 reads hDAG1 j hj1 hjN o' ho'
      (by rw [hjnode]; exact hself)
    have e2 := Gen.stateAt_eq_SFinal_of_reads R₂ hLP hTF2 reads hDAG2 i hi1 hiN o'
      (hstmt_eq ▸ ho') (by rw [hinode]; exact hself)
    rw [e1, e2]; exact hv

/-- **The per-node argument, relaxed** (Module 1's `nodeAgree`). Given `o`'s
candidate writer `n` and `ValueAgree`-below-`o` in the bundled
`NodeAgreeConclusionT` form, `n`'s entire reactive sequence corresponds turn
by turn between `R₁` and `R₂`, with results `~_Res`-related, histories
`~`-related and the tracked value at `o` `~_R`-related at every turn — all
indexed by `n`'s own turn count, never by raw schedule position.

Two things differ from Module 1 beyond the pointwise relaxation. Statements
still agree *literally* at each turn, but that now comes from
`(next-~-insensitive)` applied to `~`-related histories rather than from
`next`'s determinism on literally equal ones. And the post-turn state step
uses `execL_agreeT` (`foldl_step_maintainT` underneath) in place of
its equality counterpart, so `CompiledReadsSound` is threaded
through to it (alongside `ReadsSound`/`RetCongruent`) exactly as
`stepAgreeT` needs it for the result step below. -/
theorem nodeAgreeT {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (hL : LevelSoundT L)
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀)
    (hTF1 : TargetFaithfulL comp₁) (hTF2 : TargetFaithfulL comp₂)
    (hDAG1 : Gen.DAGOrder reads R₁) (hDAG2 : Gen.DAGOrder reads R₂)
    (hUWG : UniqueWriterGlobal P) (hNTI : NextTildeInsensitive P)
    (n : Nodes) (o : FQN)
    (valueAgreeBelow : ∀ o', StaticPrec reads P o' o →
      OptEquiv (SFinalL R₁ o') (SFinalL R₂ o') ∧
      ∀ n', (∃ H q, P.nxt n' H = some (Statement.write o' q)) →
        NodeAgreeConclusionT R₁ R₂ n' o')
    (hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree L reads comp₁ comp₂ (R₁.stmt j))
    (hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i))
    (hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q)) :
    NodeAgreeConclusionT R₁ R₂ n o := by
  -- Decompose `H(n,·)` at a given position via the (unique) turn just before it.
  have hist1 : ∀ j, j ≤ R₁.N + 1 → ∀ j', 1 ≤ j' → j' < j → R₁.node j' = n →
      turnCount R₁.node n j' + 1 = turnCount R₁.node n j →
      histAt R₁.node R₁.stmt R₁.res n j =
        histAt R₁.node R₁.stmt R₁.res n j' ++ [(R₁.stmt j', R₁.res j')] := by
    intro j hjN j' hj'1 hj'j hj'node hcount
    have hcount' : turnCount R₁.node n (j' + 1) = turnCount R₁.node n j := by
      simp only [turnCount, hj'1, hj'node, and_self, ite_true]; omega
    have heq := histAt_turnCount_unique R₁.node R₁.stmt R₁.res n
      (show j' + 1 ≤ j by omega) (Nat.le_refl j) hcount'
    rw [← heq]; simp only [histAt, hj'1, hj'node, and_self, ite_true]
  have hist2 : ∀ i, i ≤ R₂.N + 1 → ∀ i', 1 ≤ i' → i' < i → R₂.node i' = n →
      turnCount R₂.node n i' + 1 = turnCount R₂.node n i →
      histAt R₂.node R₂.stmt R₂.res n i =
        histAt R₂.node R₂.stmt R₂.res n i' ++ [(R₂.stmt i', R₂.res i')] := by
    intro i hiN i' hi'1 hi'i hi'node hcount
    have hcount' : turnCount R₂.node n (i' + 1) = turnCount R₂.node n i := by
      simp only [turnCount, hi'1, hi'node, and_self, ite_true]; omega
    have heq := histAt_turnCount_unique R₂.node R₂.stmt R₂.res n
      (show i' + 1 ≤ i by omega) (Nat.le_refl i) hcount'
    rw [← heq]; simp only [histAt, hi'1, hi'node, and_self, ite_true]
  have existsNext : ∀ {comp' : Comp FQN Query Relation L} (R' : LiveRunL P L comp' S₀)
      (nn : Nodes) (k' i0 : Nat), i0 ≤ R'.N + 1 → turnCount R'.node nn i0 = k' →
      P.nxt nn (histAt R'.node R'.stmt R'.res nn i0) ≠ none →
      k' < turnCount R'.node nn (R'.N + 1) := by
    intro comp' R' nn k' i0 hi0 hcount hne
    rcases Nat.lt_or_ge k' (turnCount R'.node nn (R'.N + 1)) with h | h
    · exact h
    · exfalso
      have hmono : turnCount R'.node nn i0 ≤ turnCount R'.node nn (R'.N + 1) :=
        turnCount_mono R'.node nn hi0
      have heqc : turnCount R'.node nn i0 = turnCount R'.node nn (R'.N + 1) := by omega
      have heq := histAt_turnCount_unique R'.node R'.stmt R'.res nn hi0 (Nat.le_refl (R'.N + 1)) heqc
      exact hne (by rw [heq]; exact R'.valid2 nn)
  -- Read-agreement at a matched turn pair: the tracked FQN `o` comes from the
  -- invariant being carried, every other FQN from `stateAt_other_agreeT`.
  have hSagreeAt : ∀ j i, 1 ≤ j → j ≤ R₁.N → R₁.node j = n → 1 ≤ i → i ≤ R₂.N →
      R₂.node i = n → turnCount R₂.node n i = turnCount R₁.node n j →
      P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) →
      R₁.stmt j = R₂.stmt i →
      OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o) (stateAtL comp₂ R₂.stmt S₀ i o) →
      ∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o') := by
    intro j i hj1 hjN hjnode hi1 hiN hinode hicount hnxt hstmt_eq hStateO o' ho'
    by_cases heqo : o' = o
    · rw [heqo]; exact hStateO
    · exact stateAt_other_agreeT hL.preserve R₁ R₂ hTF1 hTF2 hDAG1 hDAG2 n o hCandidate valueAgreeBelow
        j i hj1 hjN hjnode hi1 hiN hinode hicount hnxt hstmt_eq o' ho' heqo
  -- The served results at a matched turn pair.
  have resStep : ∀ j i, 1 ≤ j → j ≤ R₁.N → R₁.node j = n → 1 ≤ i → i ≤ R₂.N →
      R₂.node i = n → turnCount R₂.node n i = turnCount R₁.node n j →
      P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) →
      R₁.stmt j = R₂.stmt i →
      OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o) (stateAtL comp₂ R₂.stmt S₀ i o) →
      ResEquiv (R₁.res j) (R₂.res i) := by
    intro j i hj1 hjN hjnode hi1 hiN hinode hicount hnxt hstmt_eq hStateO
    cases hst : R₁.stmt j with
    | write ow qw =>
      have hresA := R₁.res_eq j hj1 hjN
      have hresB := R₂.res_eq i hi1 hiN
      rw [← hstmt_eq] at hresB
      rw [hst] at hresA hresB
      simp only [rL] at hresA hresB
      rw [← Option.some.inj hresA, ← Option.some.inj hresB]
      trivial
    | read qr =>
      have hw : target (R₁.stmt j) = none := by simp [hst, target]
      exact hReadRes j i hj1 hjN hi1 hiN hstmt_eq hw
        (hSagreeAt j i hj1 hjN hjnode hi1 hiN hinode hicount hnxt hstmt_eq hStateO)
  -- The tracked value at `o`, carried across a matched turn pair.
  have postStep : ∀ j i, 1 ≤ j → j ≤ R₁.N → R₁.node j = n → 1 ≤ i → i ≤ R₂.N →
      R₂.node i = n → turnCount R₂.node n i = turnCount R₁.node n j →
      P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) →
      R₁.stmt j = R₂.stmt i →
      OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o) (stateAtL comp₂ R₂.stmt S₀ i o) →
      OptEquiv (stateAtL comp₁ R₁.stmt S₀ (j + 1) o)
               (stateAtL comp₂ R₂.stmt S₀ (i + 1) o) := by
    intro j i hj1 hjN hjnode hi1 hiN hinode hicount hnxt hstmt_eq hStateO
    rw [Gen.stateAt_succ (comp := comp₁) R₁.stmt S₀ j hj1, Gen.stateAt_succ (comp := comp₂) R₂.stmt S₀ i hi1, ← hstmt_eq]
    cases hst : R₁.stmt j with
    | write ow qw =>
      rw [← hst]
      exact hAWrite j hj1 hjN ⟨ow, by simp [hst, target]⟩ o _ _
        (hSagreeAt j i hj1 hjN hjnode hi1 hiN hinode hicount hnxt hstmt_eq hStateO) hStateO
    | read qr =>
      rw [← hst]
      have hne : target (R₁.stmt j) ≠ some o := by simp [hst, target]
      rw [execL_preserve hL.preserve hTF1 (stateAtL comp₁ R₁.stmt S₀ j) (R₁.stmt j) o hne,
        execL_preserve hL.preserve hTF2 (stateAtL comp₂ R₂.stmt S₀ i) (R₁.stmt j) o hne]
      exact hStateO
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have ihF := fun k' (hk' : k' < k) => (ih k' hk').1
    have ihB := fun k' (hk' : k' < k) => (ih k' hk').2
    match k with
    | 0 =>
      refine ⟨?_, ?_⟩
      · intro j hj1 hjN hjnode hjcount
        have hh1 : histAt R₁.node R₁.stmt R₁.res n j = [] :=
          List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hjcount])
        have hR1eq : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
          have := R₁.stmt_eq j hj1 hjN; rwa [hjnode] at this
        have hR1eq' : P.nxt n [] = some (R₁.stmt j) := by rw [← hh1]; exact hR1eq
        have hne0 : P.nxt n (histAt R₂.node R₂.stmt R₂.res n 0) ≠ none := by
          have h0 : histAt R₂.node R₂.stmt R₂.res n 0 = [] := rfl
          rw [h0, hR1eq']; simp
        have hlt : (0 : Nat) < turnCount R₂.node n (R₂.N + 1) :=
          existsNext R₂ n 0 0 (by omega) rfl hne0
        obtain ⟨i, hiN', hi1, hinode, hicount, -⟩ :=
          histAt_find R₂.node R₂.stmt R₂.res n (R₂.N + 1) 0 hlt
        have hi_le : i ≤ R₂.N := by omega
        have hh2 : histAt R₂.node R₂.stmt R₂.res n i = [] :=
          List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hicount])
        have hR2eq : P.nxt n [] = some (R₂.stmt i) := by
          have := R₂.stmt_eq i hi1 hi_le; rwa [hinode, hh2] at this
        have hstmt_eq : R₁.stmt j = R₂.stmt i := by
          have hcomb := hR1eq'.symm.trans hR2eq; injection hcomb
        have hStateO : OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o)
            (stateAtL comp₂ R₂.stmt S₀ i o) := by
          rw [Gen.stateAtEq_of_turnCount_zero R₁ hL.preserve hTF1 hUWG n o hCandidate j (by omega) hjcount,
            Gen.stateAtEq_of_turnCount_zero R₂ hL.preserve hTF2 hUWG n o hCandidate i (by omega) hicount]
          exact OptEquiv.refl _
        exact ⟨i, hi1, hi_le, hinode, hicount, hstmt_eq,
          resStep j i hj1 hjN hjnode hi1 hi_le hinode (hicount.trans hjcount.symm) hR1eq
            hstmt_eq hStateO,
          by rw [hh1, hh2]; exact LForall₂.nil, hStateO⟩
      · intro i hi1 hiN hinode hicount
        have hh2 : histAt R₂.node R₂.stmt R₂.res n i = [] :=
          List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hicount])
        have hR2eq : P.nxt n [] = some (R₂.stmt i) := by
          have := R₂.stmt_eq i hi1 hiN; rwa [hinode, hh2] at this
        have hne0 : P.nxt n (histAt R₁.node R₁.stmt R₁.res n 0) ≠ none := by
          have h0 : histAt R₁.node R₁.stmt R₁.res n 0 = [] := rfl
          rw [h0, hR2eq]; simp
        have hlt : (0 : Nat) < turnCount R₁.node n (R₁.N + 1) :=
          existsNext R₁ n 0 0 (by omega) rfl hne0
        obtain ⟨j, hjN', hj1, hjnode, hjcount, -⟩ :=
          histAt_find R₁.node R₁.stmt R₁.res n (R₁.N + 1) 0 hlt
        have hj_le : j ≤ R₁.N := by omega
        have hh1 : histAt R₁.node R₁.stmt R₁.res n j = [] :=
          List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hjcount])
        have hR1eq : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
          have := R₁.stmt_eq j hj1 hj_le; rwa [hjnode] at this
        have hR1eq' : P.nxt n [] = some (R₁.stmt j) := by rw [← hh1]; exact hR1eq
        have hstmt_eq : R₁.stmt j = R₂.stmt i := by
          have hcomb := hR1eq'.symm.trans hR2eq; injection hcomb
        have hStateO : OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o)
            (stateAtL comp₂ R₂.stmt S₀ i o) := by
          rw [Gen.stateAtEq_of_turnCount_zero R₁ hL.preserve hTF1 hUWG n o hCandidate j (by omega) hjcount,
            Gen.stateAtEq_of_turnCount_zero R₂ hL.preserve hTF2 hUWG n o hCandidate i (by omega) hicount]
          exact OptEquiv.refl _
        exact ⟨j, hj1, hj_le, hjnode, hjcount, hstmt_eq,
          resStep j i hj1 hj_le hjnode hi1 hiN hinode (hicount.trans hjcount.symm) hR1eq
            hstmt_eq hStateO,
          by rw [hh1, hh2]; exact LForall₂.nil, hStateO⟩
    | m + 1 =>
      refine ⟨?_, ?_⟩
      · intro j hj1 hjN hjnode hjcount
        have hmlt : m < turnCount R₁.node n j := by omega
        obtain ⟨j', hj'j, hj'1, hj'node, hj'count, -⟩ :=
          histAt_find R₁.node R₁.stmt R₁.res n j m hmlt
        have hj'_le : j' ≤ R₁.N := by omega
        have hdecomp1 : histAt R₁.node R₁.stmt R₁.res n j =
            histAt R₁.node R₁.stmt R₁.res n j' ++ [(R₁.stmt j', R₁.res j')] :=
          hist1 j (by omega) j' hj'1 hj'j hj'node (by omega)
        obtain ⟨i', hi'1, hi'_le, hi'node, hi'count, hstmt', hres', hHist', hStateO'⟩ :=
          ihF m (by omega) j' hj'1 hj'_le hj'node hj'count
        have hdecomp2 : histAt R₂.node R₂.stmt R₂.res n (i' + 1) =
            histAt R₂.node R₂.stmt R₂.res n i' ++ [(R₂.stmt i', R₂.res i')] := by
          simp only [histAt, hi'1, hi'node, and_self, ite_true]
        have hHeq : HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
            (histAt R₂.node R₂.stmt R₂.res n (i' + 1)) := by
          rw [hdecomp1, hdecomp2]
          exact hHist'.append (LForall₂.cons ⟨hstmt', hres'⟩ LForall₂.nil)
        have hR1eq : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
          have := R₁.stmt_eq j hj1 hjN; rwa [hjnode] at this
        have hne : P.nxt n (histAt R₂.node R₂.stmt R₂.res n (i' + 1)) ≠ none := by
          rw [← hNTI n _ _ hHeq, hR1eq]; simp
        have hi'count' : turnCount R₂.node n (i' + 1) = m + 1 := by
          simp only [turnCount, hi'1, hi'node, and_self, ite_true]; omega
        have hj'count' : turnCount R₁.node n (j' + 1) = m + 1 := by
          simp only [turnCount, hj'1, hj'node, and_self, ite_true]; omega
        have hlt : m + 1 < turnCount R₂.node n (R₂.N + 1) :=
          existsNext R₂ n (m + 1) (i' + 1) (by omega) hi'count' hne
        obtain ⟨i, hiN', hi1, hinode, hicount, -⟩ :=
          histAt_find R₂.node R₂.stmt R₂.res n (R₂.N + 1) (m + 1) hlt
        have hi_le : i ≤ R₂.N := by omega
        have hu : histAt R₂.node R₂.stmt R₂.res n i =
            histAt R₂.node R₂.stmt R₂.res n (i' + 1) :=
          histAt_turnCount_unique R₂.node R₂.stmt R₂.res n
            (show i ≤ R₂.N + 1 by omega) (show i' + 1 ≤ R₂.N + 1 by omega)
            (by rw [hicount, hi'count'])
        have hHeq2 : HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
            (histAt R₂.node R₂.stmt R₂.res n i) := by rw [hu]; exact hHeq
        have hR2eq : P.nxt n (histAt R₂.node R₂.stmt R₂.res n i) = some (R₂.stmt i) := by
          have := R₂.stmt_eq i hi1 hi_le; rwa [hinode] at this
        have hstmt_eq : R₁.stmt j = R₂.stmt i := by
          have hcomb := hNTI n _ _ hHeq2
          rw [hR1eq, hR2eq] at hcomb
          injection hcomb
        have hi'1le : i' + 1 ≤ i := by
          rcases Nat.lt_or_ge i (i' + 1) with hlt' | hge
          · exfalso
            have hmono : turnCount R₂.node n i ≤ turnCount R₂.node n i' :=
              turnCount_mono R₂.node n (by omega)
            omega
          · exact hge
        have hR1eq' : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j') = some (R₁.stmt j') := by
          have := R₁.stmt_eq j' hj'1 hj'_le; rwa [hj'node] at this
        have hPostO' := postStep j' i' hj'1 hj'_le hj'node hi'1 hi'_le hi'node
          (hi'count.trans hj'count.symm) hR1eq' hstmt' hStateO'
        have hBridge1 : stateAtL comp₁ R₁.stmt S₀ j o = stateAtL comp₁ R₁.stmt S₀ (j' + 1) o :=
          Gen.stateAtEq_of_turnCount_eq R₁ hL.preserve hTF1 hUWG n o hCandidate (j' + 1) j (by omega) (by omega)
            (by omega) (hj'count'.trans hjcount.symm)
        have hBridge2 : stateAtL comp₂ R₂.stmt S₀ i o = stateAtL comp₂ R₂.stmt S₀ (i' + 1) o :=
          Gen.stateAtEq_of_turnCount_eq R₂ hL.preserve hTF2 hUWG n o hCandidate (i' + 1) i (by omega) hi'1le
            (by omega) (hi'count'.trans hicount.symm)
        have hStateO : OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o)
            (stateAtL comp₂ R₂.stmt S₀ i o) := by
          rw [hBridge1, hBridge2]; exact hPostO'
        exact ⟨i, hi1, hi_le, hinode, hicount, hstmt_eq,
          resStep j i hj1 hjN hjnode hi1 hi_le hinode (hicount.trans hjcount.symm) hR1eq
            hstmt_eq hStateO,
          hHeq2, hStateO⟩
      · intro i hi1 hiN hinode hicount
        have hmlt : m < turnCount R₂.node n i := by omega
        obtain ⟨i', hi'i, hi'1, hi'node, hi'count, -⟩ :=
          histAt_find R₂.node R₂.stmt R₂.res n i m hmlt
        have hi'_le : i' ≤ R₂.N := by omega
        have hdecomp2 : histAt R₂.node R₂.stmt R₂.res n i =
            histAt R₂.node R₂.stmt R₂.res n i' ++ [(R₂.stmt i', R₂.res i')] :=
          hist2 i (by omega) i' hi'1 hi'i hi'node (by omega)
        obtain ⟨j', hj'1, hj'_le, hj'node, hj'count, hstmt', hres', hHist', hStateO'⟩ :=
          ihB m (by omega) i' hi'1 hi'_le hi'node hi'count
        have hdecomp1 : histAt R₁.node R₁.stmt R₁.res n (j' + 1) =
            histAt R₁.node R₁.stmt R₁.res n j' ++ [(R₁.stmt j', R₁.res j')] := by
          simp only [histAt, hj'1, hj'node, and_self, ite_true]
        have hHeq : HistEquiv (histAt R₁.node R₁.stmt R₁.res n (j' + 1))
            (histAt R₂.node R₂.stmt R₂.res n i) := by
          rw [hdecomp1, hdecomp2]
          exact hHist'.append (LForall₂.cons ⟨hstmt', hres'⟩ LForall₂.nil)
        have hR2eq : P.nxt n (histAt R₂.node R₂.stmt R₂.res n i) = some (R₂.stmt i) := by
          have := R₂.stmt_eq i hi1 hiN; rwa [hinode] at this
        have hne : P.nxt n (histAt R₁.node R₁.stmt R₁.res n (j' + 1)) ≠ none := by
          rw [hNTI n _ _ hHeq, hR2eq]; simp
        have hj'count' : turnCount R₁.node n (j' + 1) = m + 1 := by
          simp only [turnCount, hj'1, hj'node, and_self, ite_true]; omega
        have hi'count' : turnCount R₂.node n (i' + 1) = m + 1 := by
          simp only [turnCount, hi'1, hi'node, and_self, ite_true]; omega
        have hlt : m + 1 < turnCount R₁.node n (R₁.N + 1) :=
          existsNext R₁ n (m + 1) (j' + 1) (by omega) hj'count' hne
        obtain ⟨j, hjN', hj1, hjnode, hjcount, -⟩ :=
          histAt_find R₁.node R₁.stmt R₁.res n (R₁.N + 1) (m + 1) hlt
        have hj_le : j ≤ R₁.N := by omega
        have hu : histAt R₁.node R₁.stmt R₁.res n j =
            histAt R₁.node R₁.stmt R₁.res n (j' + 1) :=
          histAt_turnCount_unique R₁.node R₁.stmt R₁.res n
            (show j ≤ R₁.N + 1 by omega) (show j' + 1 ≤ R₁.N + 1 by omega)
            (by rw [hjcount, hj'count'])
        have hHeq2 : HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
            (histAt R₂.node R₂.stmt R₂.res n i) := by rw [hu]; exact hHeq
        have hR1eq : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
          have := R₁.stmt_eq j hj1 hj_le; rwa [hjnode] at this
        have hstmt_eq : R₁.stmt j = R₂.stmt i := by
          have hcomb := hNTI n _ _ hHeq2
          rw [hR1eq, hR2eq] at hcomb
          injection hcomb
        have hj'1le : j' + 1 ≤ j := by
          rcases Nat.lt_or_ge j (j' + 1) with hlt' | hge
          · exfalso
            have hmono : turnCount R₁.node n j ≤ turnCount R₁.node n j' :=
              turnCount_mono R₁.node n (by omega)
            omega
          · exact hge
        have hR1eq' : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j') = some (R₁.stmt j') := by
          have := R₁.stmt_eq j' hj'1 hj'_le; rwa [hj'node] at this
        have hPostO' := postStep j' i' hj'1 hj'_le hj'node hi'1 hi'_le hi'node
          (hi'count.trans hj'count.symm) hR1eq' hstmt' hStateO'
        have hBridge1 : stateAtL comp₁ R₁.stmt S₀ j o = stateAtL comp₁ R₁.stmt S₀ (j' + 1) o :=
          Gen.stateAtEq_of_turnCount_eq R₁ hL.preserve hTF1 hUWG n o hCandidate (j' + 1) j (by omega) hj'1le
            (by omega) (hj'count'.trans hjcount.symm)
        have hBridge2 : stateAtL comp₂ R₂.stmt S₀ i o = stateAtL comp₂ R₂.stmt S₀ (i' + 1) o :=
          Gen.stateAtEq_of_turnCount_eq R₂ hL.preserve hTF2 hUWG n o hCandidate (i' + 1) i (by omega) (by omega)
            (by omega) (hi'count'.trans hicount.symm)
        have hStateO : OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o)
            (stateAtL comp₂ R₂.stmt S₀ i o) := by
          rw [hBridge1, hBridge2]; exact hPostO'
        exact ⟨j, hj1, hj_le, hjnode, hjcount, hstmt_eq,
          resStep j i hj1 hj_le hjnode hi1 hiN hinode (hicount.trans hjcount.symm) hR1eq
            hstmt_eq hStateO,
          hHeq2, hStateO⟩

/-- `writeChainAgree`, relaxed — and, unlike Module 1's, not an induction at
all. Module 1 had to chain through a run's successive writes of `o` by strong
induction on raw position because its per-node turn correspondence carried no
state; `NodeAgreeConclusionT` already carries the value at `o` at *every*
turn, so the pre-write agreement is just its last component, and all that is
left is one `execL_agreeT` step across the write itself.

`hAWrite` is only ever invoked here at a position already known to be a
`Write` (`target (R₁.stmt j) = some o` is a hypothesis of the very theorem),
so it need only supply `(A~)` there — segmented matching (Module 3) cannot
supply it at `Read` turns at all, only the *conclusion* `(reads-sound-~)`
would otherwise buy. -/
theorem writeChainAgreeT {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    {R₁ : LiveRunL P L comp₁ S₀} {R₂ : LiveRunL P L comp₂ S₀}
    (hL : LevelSoundT L)
    (hTF1 : TargetFaithfulL comp₁) (hTF2 : TargetFaithfulL comp₂)
    (hDAG1 : Gen.DAGOrder reads R₁) (hDAG2 : Gen.DAGOrder reads R₂)
    (n : Nodes) (o : FQN)
    (valueAgreeBelow : ∀ o', StaticPrec reads P o' o →
      OptEquiv (SFinalL R₁ o') (SFinalL R₂ o') ∧
      ∀ n', (∃ H q, P.nxt n' H = some (Statement.write o' q)) →
        NodeAgreeConclusionT R₁ R₂ n' o')
    (hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree L reads comp₁ comp₂ (R₁.stmt j))
    (hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q))
    (hnode : NodeAgreeConclusionT R₁ R₂ n o) :
    ∀ j, 1 ≤ j → j ≤ R₁.N → R₁.node j = n → target (R₁.stmt j) = some o →
      ∃ i, 1 ≤ i ∧ i ≤ R₂.N ∧ R₂.node i = n ∧ target (R₂.stmt i) = some o ∧
           turnCount R₂.node n i = turnCount R₁.node n j ∧
           OptEquiv (stateAtL comp₁ R₁.stmt S₀ (j + 1) o)
                    (stateAtL comp₂ R₂.stmt S₀ (i + 1) o) := by
  intro j hj1 hjN hjnode hjtgt
  obtain ⟨i, hi1, hiN, hinode, hicount, hstmteq, -, -, hbefore⟩ :=
    (hnode (turnCount R₁.node n j)).1 j hj1 hjN hjnode rfl
  have hitgt : target (R₂.stmt i) = some o := by rw [← hstmteq]; exact hjtgt
  have hnxt : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
    have := R₁.stmt_eq j hj1 hjN; rwa [hjnode] at this
  have hSagree : ∀ o', reads (R₁.stmt j) o' →
      OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o') := by
    intro o' ho'
    by_cases heqo : o' = o
    · rw [heqo]; exact hbefore
    · exact stateAt_other_agreeT hL.preserve R₁ R₂ hTF1 hTF2 hDAG1 hDAG2 n o hCandidate valueAgreeBelow
        j i hj1 hjN hjnode hi1 hiN hinode hicount hnxt hstmteq o' ho' heqo
  refine ⟨i, hi1, hiN, hinode, hitgt, hicount, ?_⟩
  rw [Gen.stateAt_succ (comp := comp₁) R₁.stmt S₀ j hj1, Gen.stateAt_succ (comp := comp₂) R₂.stmt S₀ i hi1, ← hstmteq]
  exact hAWrite j hj1 hjN ⟨o, hjtgt⟩ o _ _ hSagree hbefore

/-- **`ValueAgree`, relaxed**: at every FQN, `S_final(R₁) ~_R S_final(R₂)`,
*bundled* — as in Module 1 — with the full `NodeAgreeConclusionT` for that
FQN's candidate writer, since that is the shape the well-founded recursion
needs back from itself. Induction on the static, project-level `StaticPrec`;
Module 1's argument with literal value equality replaced by `~_R`
throughout. -/
theorem valueAgreeT {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (hL : LevelSoundT L)
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀)
    (hTF1 : TargetFaithfulL comp₁) (hTF2 : TargetFaithfulL comp₂)
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : Gen.DAGOrder reads R₁) (hDAG2 : Gen.DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P)) (hNTI : NextTildeInsensitive P)
    (hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree L reads comp₁ comp₂ (R₁.stmt j))
    (hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i)) :
    ∀ o, OptEquiv (SFinalL R₁ o) (SFinalL R₂ o) ∧
      ∀ n, (∃ H q, P.nxt n H = some (Statement.write o q)) →
        NodeAgreeConclusionT R₁ R₂ n o := by
  intro o
  induction o using hSWF.induction with
  | _ o ih =>
    by_cases hw : ∃ n H q, P.nxt n H = some (Statement.write o q)
    · obtain ⟨n, Hc, qc, hHc⟩ := hw
      have hCandidate : ∃ H q, P.nxt n H = some (Statement.write o q) := ⟨Hc, qc, hHc⟩
      have hnode : NodeAgreeConclusionT R₁ R₂ n o :=
        nodeAgreeT hL R₁ R₂ hTF1 hTF2 hDAG1 hDAG2 hUWG hNTI n o ih
          hAWrite hReadRes hCandidate
      have hnodeFull : ∀ n', (∃ H q, P.nxt n' H = some (Statement.write o q)) →
          NodeAgreeConclusionT R₁ R₂ n' o := by
        intro n' hn'
        obtain ⟨H', q', hH'⟩ := hn'
        rw [← hUWG o n n' Hc H' qc q' hHc hH']
        exact hnode
      have hNOf1 := Gen.nodeOfWriter R₁ hUWG n o hCandidate
      have hNOf2 := Gen.nodeOfWriter R₂ hUWG n o hCandidate
      refine ⟨?_, hnodeFull⟩
      by_cases hR1w : ∃ j, 1 ≤ j ∧ j ≤ R₁.N ∧ target (R₁.stmt j) = some o
      · obtain ⟨p, hpN, ⟨hp1, hptgt⟩, hpmax⟩ :=
          Gen.exists_greatest_le (fun p => 1 ≤ p ∧ target (R₁.stmt p) = some o) R₁.N
            (by obtain ⟨j, hj1, hjN, hjtgt⟩ := hR1w; exact ⟨j, hjN, hj1, hjtgt⟩)
        have hpnode : R₁.node p = n := hNOf1 p hp1 hpN hptgt
        obtain ⟨ip, hip1, hipN, hipnode, hiptgt, hipcount, hafter⟩ :=
          writeChainAgreeT hL hTF1 hTF2 hDAG1 hDAG2 n o ih hAWrite hCandidate hnode
            p hp1 hpN hpnode hptgt
        have hconst1 : SFinalL R₁ o = stateAtL comp₁ R₁.stmt S₀ (p + 1) o := by
          simp only [SFinalL]
          have := Gen.stateAt_const_range R₁.stmt hL.preserve hTF1 S₀ o (p + 1) (by omega)
            (R₁.N + 1 - (p + 1)) (fun q' hq'1 hq'2 heq => by
              have := hpmax q' (by omega) ⟨by omega, heq⟩; omega)
          rwa [show (p + 1) + (R₁.N + 1 - (p + 1)) = R₁.N + 1 from by omega] at this
        have hipmax : ∀ q, 1 ≤ q → q ≤ R₂.N → target (R₂.stmt q) = some o → q ≤ ip := by
          intro q hq1 hqN heq
          rcases Nat.lt_or_ge q ip with hlt | hge
          · omega
          · rcases Nat.eq_or_lt_of_le hge with heqip | hgt
            · omega
            · exfalso
              have hqnode : R₂.node q = n := hNOf2 q hq1 hqN heq
              obtain ⟨j'', hj''1, hj''N, hj''node, hj''count, hstmteq'', -, -⟩ :=
                (hnode (turnCount R₂.node n q)).2 q hq1 hqN hqnode rfl
              have hj''tgt : target (R₁.stmt j'') = some o := by rw [hstmteq'']; exact heq
              have hipqcount : turnCount R₂.node n ip < turnCount R₂.node n q := by
                have hstep : turnCount R₂.node n (ip + 1) = turnCount R₂.node n ip + 1 := by
                  simp only [turnCount, hip1, hipnode, and_self, ite_true]
                have hmono : turnCount R₂.node n (ip + 1) ≤ turnCount R₂.node n q :=
                  turnCount_mono R₂.node n (by omega)
                omega
              have hpltj'' : p < j'' := by
                rcases Nat.lt_or_ge p j'' with h | h
                · exact h
                · exfalso
                  have hmono : turnCount R₁.node n j'' ≤ turnCount R₁.node n p :=
                    turnCount_mono R₁.node n h
                  omega
              have := hpmax j'' (by omega) ⟨hj''1, hj''tgt⟩
              omega
        have hconst2 : SFinalL R₂ o = stateAtL comp₂ R₂.stmt S₀ (ip + 1) o := by
          simp only [SFinalL]
          have := Gen.stateAt_const_range R₂.stmt hL.preserve hTF2 S₀ o (ip + 1) (by omega)
            (R₂.N + 1 - (ip + 1)) (fun q' hq'1 hq'2 heq => by
              have := hipmax q' (by omega) (by omega) heq; omega)
          rwa [show (ip + 1) + (R₂.N + 1 - (ip + 1)) = R₂.N + 1 from by omega] at this
        rw [hconst1, hconst2]; exact hafter
      · by_cases hR2w : ∃ i, 1 ≤ i ∧ i ≤ R₂.N ∧ target (R₂.stmt i) = some o
        · obtain ⟨i, hi1, hiN, hitgt⟩ := hR2w
          have hinode : R₂.node i = n := hNOf2 i hi1 hiN hitgt
          obtain ⟨j, hj1, hjN, hjnode, -, hstmteq, -, -⟩ :=
            (hnode (turnCount R₂.node n i)).2 i hi1 hiN hinode rfl
          exact absurd ⟨j, hj1, hjN, hstmteq ▸ hitgt⟩ hR1w
        · have hw1' : ∀ j, 1 ≤ j → j ≤ R₁.N → target (R₁.stmt j) ≠ some o :=
            fun j hj1 hjN heq => hR1w ⟨j, hj1, hjN, heq⟩
          have hw2' : ∀ i, 1 ≤ i → i ≤ R₂.N → target (R₂.stmt i) ≠ some o :=
            fun i hi1 hiN heq => hR2w ⟨i, hi1, hiN, heq⟩
          have e1 : SFinalL R₁ o = S₀ o := by
            simp only [SFinalL]; exact Gen.stateAt_preserve R₁.stmt hL.preserve hTF1 S₀ (R₁.N + 1) o
              (fun j hj1 hj2 => hw1' j hj1 (by omega))
          have e2 : SFinalL R₂ o = S₀ o := by
            simp only [SFinalL]; exact Gen.stateAt_preserve R₂.stmt hL.preserve hTF2 S₀ (R₂.N + 1) o
              (fun i hi1 hi2 => hw2' i hi1 (by omega))
          rw [e1, e2]; exact OptEquiv.refl _
    · have hw' : ∀ n' H q, P.nxt n' H ≠ some (Statement.write o q) :=
        fun n' H q heq => hw ⟨n', H, q, heq⟩
      refine ⟨?_, fun n' hn' => absurd ⟨n', hn'⟩ hw⟩
      have h1 : ∀ j, 1 ≤ j → j ≤ R₁.N → target (R₁.stmt j) ≠ some o := by
        intro j hj1 hjN heq
        cases hcs : R₁.stmt j with
        | write o' q' =>
          rw [hcs, target] at heq
          have ho' : o' = o := by injection heq
          have := R₁.stmt_eq j hj1 hjN
          rw [hcs] at this
          exact hw' (R₁.node j) (histAt R₁.node R₁.stmt R₁.res (R₁.node j) j) q'
            (by rw [← ho']; exact this)
        | read _ => rw [hcs, target] at heq; exact absurd heq (by simp)
      have h2 : ∀ i, 1 ≤ i → i ≤ R₂.N → target (R₂.stmt i) ≠ some o := by
        intro i hi1 hiN heq
        cases hcs : R₂.stmt i with
        | write o' q' =>
          rw [hcs, target] at heq
          have ho' : o' = o := by injection heq
          have := R₂.stmt_eq i hi1 hiN
          rw [hcs] at this
          exact hw' (R₂.node i) (histAt R₂.node R₂.stmt R₂.res (R₂.node i) i) q'
            (by rw [← ho']; exact this)
        | read _ => rw [hcs, target] at heq; exact absurd heq (by simp)
      have e1 : SFinalL R₁ o = S₀ o := by
        simp only [SFinalL]; exact Gen.stateAt_preserve R₁.stmt hL.preserve hTF1 S₀ (R₁.N + 1) o
          (fun j hj1 hj2 => h1 j hj1 (by omega))
      have e2 : SFinalL R₂ o = S₀ o := by
        simp only [SFinalL]; exact Gen.stateAt_preserve R₂.stmt hL.preserve hTF2 S₀ (R₂.N + 1) o
          (fun i hi1 hi2 => h2 i hi1 (by omega))
      rw [e1, e2]; exact OptEquiv.refl _

/-- `stateAt_other_agreeT`'s counterpart for the final pass: `n` is a fully
general node (possibly read-only, tied to no candidate write) and the bundled
`ValueAgree` is already established everywhere, so no `StaticPrec`
indirection is needed — only the same same-node-versus-other-node split. -/
theorem stateAt_other_agree_finalT {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {reads : Statement FQN Query → FQN → Prop}
    
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (hLP : LevelPreserve L)
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀)
    (hTF1 : TargetFaithfulL comp₁) (hTF2 : TargetFaithfulL comp₂)
    (hDAG1 : Gen.DAGOrder reads R₁) (hDAG2 : Gen.DAGOrder reads R₂)
    (hVAfull : ∀ o, OptEquiv (SFinalL R₁ o) (SFinalL R₂ o) ∧
      ∀ n', (∃ H q, P.nxt n' H = some (Statement.write o q)) →
        NodeAgreeConclusionT R₁ R₂ n' o)
    (n : Nodes)
    (j i : Nat) (hj1 : 1 ≤ j) (hjN : j ≤ R₁.N) (hjnode : R₁.node j = n)
    (hi1 : 1 ≤ i) (hiN : i ≤ R₂.N) (hinode : R₂.node i = n)
    (hicount : turnCount R₂.node n i = turnCount R₁.node n j)
    (hstmt_eq : R₁.stmt j = R₂.stmt i)
    (o' : FQN) (ho' : reads (R₁.stmt j) o') :
    OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o') := by
  by_cases hself : ∃ H q, P.nxt n H = some (Statement.write o' q)
  · have hconcl := (hVAfull o').2 n hself
    obtain ⟨i2, hi2_1, hi2_N, hi2_node, hi2_count, -, -, -, hstateeq⟩ :=
      (hconcl (turnCount R₁.node n j)).1 j hj1 hjN hjnode rfl
    have hii2 : i2 = i :=
      turn_position_unique R₂.node n hi2_1 hi2_node hi1 hinode (hi2_count.trans hicount.symm)
    rwa [hii2] at hstateeq
  · have hv := (hVAfull o').1
    have e1 := Gen.stateAt_eq_SFinal_of_reads R₁ hLP hTF1 reads hDAG1 j hj1 hjN o' ho'
      (by rw [hjnode]; exact hself)
    have e2 := Gen.stateAt_eq_SFinal_of_reads R₂ hLP hTF2 reads hDAG2 i hi1 hiN o'
      (hstmt_eq ▸ ho') (by rw [hinode]; exact hself)
    rw [e1, e2]; exact hv

/-- **The per-node turn correspondence for a fully general node, relaxed**
(Module 1's `nodeAgreeFinal`): the same argument as `nodeAgreeT`, but for a
node not tied to any FQN it might write — read-only nodes included — reading
agreement off the now-complete bundled `ValueAgree` instead of the local
`≺ₛ`-below hypothesis that bootstrapped it. Nothing is tracked at an FQN
here, so the conclusion is `TurnAgreeSpec` rather than
`NodeAgreeConclusionT`.

As in `nodeAgreeT`, statements agree literally at each turn — that is what
`(next-~-insensitive)` buys, applied to `~`-related rather than literally
equal histories — while results agree up to `~_Res` and histories up to
`~`. -/
theorem nodeAgreeFinalT {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (hLP : LevelPreserve L)
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀)
    (hTF1 : TargetFaithfulL comp₁) (hTF2 : TargetFaithfulL comp₂)
    (hDAG1 : Gen.DAGOrder reads R₁) (hDAG2 : Gen.DAGOrder reads R₂)
    (hNTI : NextTildeInsensitive P)
    (hVAfull : ∀ o, OptEquiv (SFinalL R₁ o) (SFinalL R₂ o) ∧
      ∀ n', (∃ H q, P.nxt n' H = some (Statement.write o q)) →
        NodeAgreeConclusionT R₁ R₂ n' o)
    (n : Nodes)
    (hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i)) :
    TurnAgreeSpec R₁ R₂ n := by
  -- Decompose `H(n,·)` at a given position via the (unique) turn just before it.
  have hist1 : ∀ j, j ≤ R₁.N + 1 → ∀ j', 1 ≤ j' → j' < j → R₁.node j' = n →
      turnCount R₁.node n j' + 1 = turnCount R₁.node n j →
      histAt R₁.node R₁.stmt R₁.res n j =
        histAt R₁.node R₁.stmt R₁.res n j' ++ [(R₁.stmt j', R₁.res j')] := by
    intro j hjN j' hj'1 hj'j hj'node hcount
    have hcount' : turnCount R₁.node n (j' + 1) = turnCount R₁.node n j := by
      simp only [turnCount, hj'1, hj'node, and_self, ite_true]; omega
    have heq := histAt_turnCount_unique R₁.node R₁.stmt R₁.res n
      (show j' + 1 ≤ j by omega) (Nat.le_refl j) hcount'
    rw [← heq]; simp only [histAt, hj'1, hj'node, and_self, ite_true]
  have hist2 : ∀ i, i ≤ R₂.N + 1 → ∀ i', 1 ≤ i' → i' < i → R₂.node i' = n →
      turnCount R₂.node n i' + 1 = turnCount R₂.node n i →
      histAt R₂.node R₂.stmt R₂.res n i =
        histAt R₂.node R₂.stmt R₂.res n i' ++ [(R₂.stmt i', R₂.res i')] := by
    intro i hiN i' hi'1 hi'i hi'node hcount
    have hcount' : turnCount R₂.node n (i' + 1) = turnCount R₂.node n i := by
      simp only [turnCount, hi'1, hi'node, and_self, ite_true]; omega
    have heq := histAt_turnCount_unique R₂.node R₂.stmt R₂.res n
      (show i' + 1 ≤ i by omega) (Nat.le_refl i) hcount'
    rw [← heq]; simp only [histAt, hi'1, hi'node, and_self, ite_true]
  have existsNext : ∀ {comp' : Comp FQN Query Relation L} (R' : LiveRunL P L comp' S₀)
      (nn : Nodes) (k' i0 : Nat), i0 ≤ R'.N + 1 → turnCount R'.node nn i0 = k' →
      P.nxt nn (histAt R'.node R'.stmt R'.res nn i0) ≠ none →
      k' < turnCount R'.node nn (R'.N + 1) := by
    intro comp' R' nn k' i0 hi0 hcount hne
    rcases Nat.lt_or_ge k' (turnCount R'.node nn (R'.N + 1)) with h | h
    · exact h
    · exfalso
      have hmono : turnCount R'.node nn i0 ≤ turnCount R'.node nn (R'.N + 1) :=
        turnCount_mono R'.node nn hi0
      have heqc : turnCount R'.node nn i0 = turnCount R'.node nn (R'.N + 1) := by omega
      have heq := histAt_turnCount_unique R'.node R'.stmt R'.res nn hi0 (Nat.le_refl (R'.N + 1)) heqc
      exact hne (by rw [heq]; exact R'.valid2 nn)
  -- The shared value-level step, in the form all four branches use it.
  have resStep : ∀ (j i : Nat), 1 ≤ j → j ≤ R₁.N → R₁.node j = n → 1 ≤ i → i ≤ R₂.N →
      R₂.node i = n → turnCount R₂.node n i = turnCount R₁.node n j →
      R₁.stmt j = R₂.stmt i → ResEquiv (R₁.res j) (R₂.res i) := by
    intro j i hj1 hjN hjnode hi1 hiN hinode hicount hstmt_eq
    have hSagree : ∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o') :=
      fun o' ho' => stateAt_other_agree_finalT hLP R₁ R₂ hTF1 hTF2 hDAG1 hDAG2 hVAfull n
        j i hj1 hjN hjnode hi1 hiN hinode hicount hstmt_eq o' ho'
    cases hst : R₁.stmt j with
    | write ow qw =>
      -- A `Write` turn's own result is `Result.ok` on both sides, always —
      -- no cross-engine call agreement is needed at all here (unlike the
      -- *state* propagated through the write, which `nodeAgreeT`'s
      -- `postStep` still needs `(A~)` for).
      have hresA := R₁.res_eq j hj1 hjN
      have hresB := R₂.res_eq i hi1 hiN
      rw [← hstmt_eq, hst] at hresB
      rw [hst] at hresA
      simp only [rL] at hresA hresB
      have e1 : R₁.res j = Result.ok := (Option.some.inj hresA).symm
      have e2 : R₂.res i = Result.ok := (Option.some.inj hresB).symm
      rw [e1, e2]; trivial
    | read qr =>
      have hw : target (R₁.stmt j) = none := by simp [hst, target]
      exact hReadRes j i hj1 hjN hi1 hiN hstmt_eq hw hSagree
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have ihF := fun k' (hk' : k' < k) => (ih k' hk').1
    have ihB := fun k' (hk' : k' < k) => (ih k' hk').2
    match k with
    | 0 =>
      refine ⟨?_, ?_⟩
      · intro j hj1 hjN hjnode hjcount
        have hh1 : histAt R₁.node R₁.stmt R₁.res n j = [] :=
          List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hjcount])
        have hR1eq : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
          have := R₁.stmt_eq j hj1 hjN; rwa [hjnode] at this
        have hR1eq' : P.nxt n [] = some (R₁.stmt j) := by rw [← hh1]; exact hR1eq
        have hne0 : P.nxt n (histAt R₂.node R₂.stmt R₂.res n 0) ≠ none := by
          have h0 : histAt R₂.node R₂.stmt R₂.res n 0 = [] := rfl
          rw [h0, hR1eq']; simp
        have hlt : (0 : Nat) < turnCount R₂.node n (R₂.N + 1) :=
          existsNext R₂ n 0 0 (by omega) rfl hne0
        obtain ⟨i, hiN', hi1, hinode, hicount, -⟩ :=
          histAt_find R₂.node R₂.stmt R₂.res n (R₂.N + 1) 0 hlt
        have hi_le : i ≤ R₂.N := by omega
        have hh2 : histAt R₂.node R₂.stmt R₂.res n i = [] :=
          List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hicount])
        have hR2eq : P.nxt n [] = some (R₂.stmt i) := by
          have := R₂.stmt_eq i hi1 hi_le; rwa [hinode, hh2] at this
        have hstmt_eq : R₁.stmt j = R₂.stmt i := by
          have hcomb := hR1eq'.symm.trans hR2eq; injection hcomb
        refine ⟨i, hi1, hi_le, hinode, hicount, hstmt_eq,
          resStep j i hj1 hjN hjnode hi1 hi_le hinode (hicount.trans hjcount.symm) hstmt_eq, ?_⟩
        rw [hh1, hh2]; exact LForall₂.nil
      · intro i hi1 hiN hinode hicount
        have hh2 : histAt R₂.node R₂.stmt R₂.res n i = [] :=
          List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hicount])
        have hR2eq : P.nxt n [] = some (R₂.stmt i) := by
          have := R₂.stmt_eq i hi1 hiN; rwa [hinode, hh2] at this
        have hne0 : P.nxt n (histAt R₁.node R₁.stmt R₁.res n 0) ≠ none := by
          have h0 : histAt R₁.node R₁.stmt R₁.res n 0 = [] := rfl
          rw [h0, hR2eq]; simp
        have hlt : (0 : Nat) < turnCount R₁.node n (R₁.N + 1) :=
          existsNext R₁ n 0 0 (by omega) rfl hne0
        obtain ⟨j, hjN', hj1, hjnode, hjcount, -⟩ :=
          histAt_find R₁.node R₁.stmt R₁.res n (R₁.N + 1) 0 hlt
        have hj_le : j ≤ R₁.N := by omega
        have hh1 : histAt R₁.node R₁.stmt R₁.res n j = [] :=
          List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hjcount])
        have hR1eq : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
          have := R₁.stmt_eq j hj1 hj_le; rwa [hjnode] at this
        have hR1eq' : P.nxt n [] = some (R₁.stmt j) := by rw [← hh1]; exact hR1eq
        have hstmt_eq : R₁.stmt j = R₂.stmt i := by
          have hcomb := hR1eq'.symm.trans hR2eq; injection hcomb
        refine ⟨j, hj1, hj_le, hjnode, hjcount, hstmt_eq,
          resStep j i hj1 hj_le hjnode hi1 hiN hinode (hicount.trans hjcount.symm) hstmt_eq, ?_⟩
        rw [hh1, hh2]; exact LForall₂.nil
    | m + 1 =>
      refine ⟨?_, ?_⟩
      · intro j hj1 hjN hjnode hjcount
        have hmlt : m < turnCount R₁.node n j := by omega
        obtain ⟨j', hj'j, hj'1, hj'node, hj'count, -⟩ :=
          histAt_find R₁.node R₁.stmt R₁.res n j m hmlt
        have hj'_le : j' ≤ R₁.N := by omega
        have hdecomp1 : histAt R₁.node R₁.stmt R₁.res n j =
            histAt R₁.node R₁.stmt R₁.res n j' ++ [(R₁.stmt j', R₁.res j')] :=
          hist1 j (by omega) j' hj'1 hj'j hj'node (by omega)
        obtain ⟨i', hi'1, hi'_le, hi'node, hi'count, hstmt', hres', hHist'⟩ :=
          ihF m (by omega) j' hj'1 hj'_le hj'node hj'count
        have hdecomp2 : histAt R₂.node R₂.stmt R₂.res n (i' + 1) =
            histAt R₂.node R₂.stmt R₂.res n i' ++ [(R₂.stmt i', R₂.res i')] := by
          simp only [histAt, hi'1, hi'node, and_self, ite_true]
        have hHeq : HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
            (histAt R₂.node R₂.stmt R₂.res n (i' + 1)) := by
          rw [hdecomp1, hdecomp2]
          exact hHist'.append (LForall₂.cons ⟨hstmt', hres'⟩ LForall₂.nil)
        have hR1eq : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
          have := R₁.stmt_eq j hj1 hjN; rwa [hjnode] at this
        have hne : P.nxt n (histAt R₂.node R₂.stmt R₂.res n (i' + 1)) ≠ none := by
          rw [← hNTI n _ _ hHeq, hR1eq]; simp
        have hi'count' : turnCount R₂.node n (i' + 1) = m + 1 := by
          simp only [turnCount, hi'1, hi'node, and_self, ite_true]; omega
        have hlt : m + 1 < turnCount R₂.node n (R₂.N + 1) :=
          existsNext R₂ n (m + 1) (i' + 1) (by omega) hi'count' hne
        obtain ⟨i, hiN', hi1, hinode, hicount, -⟩ :=
          histAt_find R₂.node R₂.stmt R₂.res n (R₂.N + 1) (m + 1) hlt
        have hi_le : i ≤ R₂.N := by omega
        have hu : histAt R₂.node R₂.stmt R₂.res n i =
            histAt R₂.node R₂.stmt R₂.res n (i' + 1) :=
          histAt_turnCount_unique R₂.node R₂.stmt R₂.res n
            (show i ≤ R₂.N + 1 by omega) (show i' + 1 ≤ R₂.N + 1 by omega)
            (by rw [hicount, hi'count'])
        have hHeq2 : HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
            (histAt R₂.node R₂.stmt R₂.res n i) := by rw [hu]; exact hHeq
        have hR2eq : P.nxt n (histAt R₂.node R₂.stmt R₂.res n i) = some (R₂.stmt i) := by
          have := R₂.stmt_eq i hi1 hi_le; rwa [hinode] at this
        have hstmt_eq : R₁.stmt j = R₂.stmt i := by
          have hcomb := hNTI n _ _ hHeq2
          rw [hR1eq, hR2eq] at hcomb
          injection hcomb
        exact ⟨i, hi1, hi_le, hinode, hicount, hstmt_eq,
          resStep j i hj1 hjN hjnode hi1 hi_le hinode (hicount.trans hjcount.symm) hstmt_eq,
          hHeq2⟩
      · intro i hi1 hiN hinode hicount
        have hmlt : m < turnCount R₂.node n i := by omega
        obtain ⟨i', hi'i, hi'1, hi'node, hi'count, -⟩ :=
          histAt_find R₂.node R₂.stmt R₂.res n i m hmlt
        have hi'_le : i' ≤ R₂.N := by omega
        have hdecomp2 : histAt R₂.node R₂.stmt R₂.res n i =
            histAt R₂.node R₂.stmt R₂.res n i' ++ [(R₂.stmt i', R₂.res i')] :=
          hist2 i (by omega) i' hi'1 hi'i hi'node (by omega)
        obtain ⟨j', hj'1, hj'_le, hj'node, hj'count, hstmt', hres', hHist'⟩ :=
          ihB m (by omega) i' hi'1 hi'_le hi'node hi'count
        have hdecomp1 : histAt R₁.node R₁.stmt R₁.res n (j' + 1) =
            histAt R₁.node R₁.stmt R₁.res n j' ++ [(R₁.stmt j', R₁.res j')] := by
          simp only [histAt, hj'1, hj'node, and_self, ite_true]
        have hHeq : HistEquiv (histAt R₁.node R₁.stmt R₁.res n (j' + 1))
            (histAt R₂.node R₂.stmt R₂.res n i) := by
          rw [hdecomp1, hdecomp2]
          exact hHist'.append (LForall₂.cons ⟨hstmt', hres'⟩ LForall₂.nil)
        have hR2eq : P.nxt n (histAt R₂.node R₂.stmt R₂.res n i) = some (R₂.stmt i) := by
          have := R₂.stmt_eq i hi1 hiN; rwa [hinode] at this
        have hne : P.nxt n (histAt R₁.node R₁.stmt R₁.res n (j' + 1)) ≠ none := by
          rw [hNTI n _ _ hHeq, hR2eq]; simp
        have hj'count' : turnCount R₁.node n (j' + 1) = m + 1 := by
          simp only [turnCount, hj'1, hj'node, and_self, ite_true]; omega
        have hlt : m + 1 < turnCount R₁.node n (R₁.N + 1) :=
          existsNext R₁ n (m + 1) (j' + 1) (by omega) hj'count' hne
        obtain ⟨j, hjN', hj1, hjnode, hjcount, -⟩ :=
          histAt_find R₁.node R₁.stmt R₁.res n (R₁.N + 1) (m + 1) hlt
        have hj_le : j ≤ R₁.N := by omega
        have hu : histAt R₁.node R₁.stmt R₁.res n j =
            histAt R₁.node R₁.stmt R₁.res n (j' + 1) :=
          histAt_turnCount_unique R₁.node R₁.stmt R₁.res n
            (show j ≤ R₁.N + 1 by omega) (show j' + 1 ≤ R₁.N + 1 by omega)
            (by rw [hjcount, hj'count'])
        have hHeq2 : HistEquiv (histAt R₁.node R₁.stmt R₁.res n j)
            (histAt R₂.node R₂.stmt R₂.res n i) := by rw [hu]; exact hHeq
        have hR1eq : P.nxt n (histAt R₁.node R₁.stmt R₁.res n j) = some (R₁.stmt j) := by
          have := R₁.stmt_eq j hj1 hj_le; rwa [hjnode] at this
        have hstmt_eq : R₁.stmt j = R₂.stmt i := by
          have hcomb := hNTI n _ _ hHeq2
          rw [hR1eq, hR2eq] at hcomb
          injection hcomb
        exact ⟨j, hj1, hj_le, hjnode, hjcount, hstmt_eq,
          resStep j i hj1 hj_le hjnode hi1 hiN hinode (hicount.trans hjcount.symm) hstmt_eq,
          hHeq2⟩

/-- Two runs matching turn-by-turn for a node realize the same *total* number
of turns for it (unchanged from Module 1 — pure turn bookkeeping). -/
theorem sameTotal {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {P : Project Nodes FQN Query Relation} {comp₁ comp₂ : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    {R₁ : LiveRunL P L comp₁ S₀} {R₂ : LiveRunL P L comp₂ S₀} (n : Nodes)
    (hnode : TurnAgreeSpec R₁ R₂ n) :
    turnCount R₁.node n (R₁.N + 1) = turnCount R₂.node n (R₂.N + 1) := by
  rcases Nat.lt_trichotomy (turnCount R₁.node n (R₁.N + 1)) (turnCount R₂.node n (R₂.N + 1))
    with h | h | h
  · exfalso
    obtain ⟨i, hiN', hi1, hinode, hicount, -⟩ :=
      histAt_find R₂.node R₂.stmt R₂.res n (R₂.N + 1) (turnCount R₁.node n (R₁.N + 1)) h
    have hi_le : i ≤ R₂.N := by omega
    obtain ⟨j, hj1, hjN, hjnode, hjcount, -, -, -⟩ :=
      (hnode (turnCount R₁.node n (R₁.N + 1))).2 i hi1 hi_le hinode hicount
    have hstep : turnCount R₁.node n (j + 1) = turnCount R₁.node n j + 1 := by
      simp only [turnCount, hj1, hjnode, and_self, ite_true]
    have hmono : turnCount R₁.node n (j + 1) ≤ turnCount R₁.node n (R₁.N + 1) :=
      turnCount_mono R₁.node n (by omega)
    omega
  · exact h
  · exfalso
    obtain ⟨j, hjN', hj1, hjnode, hjcount, -⟩ :=
      histAt_find R₁.node R₁.stmt R₁.res n (R₁.N + 1) (turnCount R₂.node n (R₂.N + 1)) h
    have hj_le : j ≤ R₁.N := by omega
    obtain ⟨i, hi1, hiN, hinode, hicount, -, -, -⟩ :=
      (hnode (turnCount R₂.node n (R₂.N + 1))).1 j hj1 hj_le hjnode hjcount
    have hstep : turnCount R₂.node n (i + 1) = turnCount R₂.node n i + 1 := by
      simp only [turnCount, hi1, hinode, and_self, ite_true]
    have hmono : turnCount R₂.node n (i + 1) ≤ turnCount R₂.node n (R₂.N + 1) :=
      turnCount_mono R₂.node n (by omega)
    omega

/-- `O(R₁) ~_O O(R₂)` at a given node (D8′): the last recorded results are
`~_Res`-related, in both directions. -/
theorem isObsAgreeT {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {P : Project Nodes FQN Query Relation} {comp₁ comp₂ : Comp FQN Query Relation L}
    {S₀ : State FQN Relation}
    {R₁ : LiveRunL P L comp₁ S₀} {R₂ : LiveRunL P L comp₂ S₀} (n : Nodes)
    (hnode : TurnAgreeSpec R₁ R₂ n) :
    (∀ r, isObs R₁.node R₁.stmt R₁.res R₁.N n r →
      ∃ r', isObs R₂.node R₂.stmt R₂.res R₂.N n r' ∧ ResEquiv r r') ∧
    (∀ r, isObs R₂.node R₂.stmt R₂.res R₂.N n r →
      ∃ r', isObs R₁.node R₁.stmt R₁.res R₁.N n r' ∧ ResEquiv r r') := by
  have hT := sameTotal n hnode
  rcases Nat.eq_zero_or_pos (turnCount R₁.node n (R₁.N + 1)) with hz | hpos
  · have h1 : histAt R₁.node R₁.stmt R₁.res n (R₁.N + 1) = [] :=
      List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, hz])
    have h2 : histAt R₂.node R₂.stmt R₂.res n (R₂.N + 1) = [] :=
      List.length_eq_zero_iff.mp (by rw [turnCount_eq_length, ← hT, hz])
    constructor
    · intro r hr; simp [isObs, h1] at hr
    · intro r hr; simp [isObs, h2] at hr
  · obtain ⟨j, hjN', hj1, hjnode, hjcount, -⟩ :=
      histAt_find R₁.node R₁.stmt R₁.res n (R₁.N + 1) (turnCount R₁.node n (R₁.N + 1) - 1)
        (by omega)
    have hj_le : j ≤ R₁.N := by omega
    obtain ⟨i, hi1, hiN, hinode, hicount, -, hreseq, -⟩ :=
      (hnode (turnCount R₁.node n (R₁.N + 1) - 1)).1 j hj1 hj_le hjnode hjcount
    have hstepj : turnCount R₁.node n (j + 1) = turnCount R₁.node n j + 1 := by
      simp only [turnCount, hj1, hjnode, and_self, ite_true]
    have hstepi : turnCount R₂.node n (i + 1) = turnCount R₂.node n i + 1 := by
      simp only [turnCount, hi1, hinode, and_self, ite_true]
    have hjlast : turnCount R₁.node n (j + 1) = turnCount R₁.node n (R₁.N + 1) := by omega
    have hilast : turnCount R₂.node n (i + 1) = turnCount R₂.node n (R₂.N + 1) := by omega
    have he1 : histAt R₁.node R₁.stmt R₁.res n (R₁.N + 1) =
        histAt R₁.node R₁.stmt R₁.res n j ++ [(R₁.stmt j, R₁.res j)] := by
      have := histAt_turnCount_unique R₁.node R₁.stmt R₁.res n
        (show j + 1 ≤ R₁.N + 1 by omega) (Nat.le_refl (R₁.N + 1)) hjlast
      rw [← this]; simp only [histAt, hj1, hjnode, and_self, ite_true]
    have he2 : histAt R₂.node R₂.stmt R₂.res n (R₂.N + 1) =
        histAt R₂.node R₂.stmt R₂.res n i ++ [(R₂.stmt i, R₂.res i)] := by
      have := histAt_turnCount_unique R₂.node R₂.stmt R₂.res n
        (show i + 1 ≤ R₂.N + 1 by omega) (Nat.le_refl (R₂.N + 1)) hilast
      rw [← this]; simp only [histAt, hi1, hinode, and_self, ite_true]
    have g1 : isObs R₁.node R₁.stmt R₁.res R₁.N n (R₁.res j) := by
      simp only [isObs, he1]; simp
    have g2 : isObs R₂.node R₂.stmt R₂.res R₂.N n (R₂.res i) := by
      simp only [isObs, he2]; simp
    constructor
    · intro r hr
      have : r = R₁.res j := Option.some.inj (hr.symm.trans g1)
      exact ⟨R₂.res i, g2, this ▸ hreseq⟩
    · intro r hr
      have : r = R₂.res i := Option.some.inj (hr.symm.trans g2)
      exact ⟨R₁.res j, g1, this ▸ ResEquiv.symm hreseq⟩

/-- **T2₂/T2₁'s shared core, given `(A~)`.** Once
`(A~) : drv_{E₁}(stmt) ~_Sˡ drv_{E₂}(stmt)` for every statement `R₁`
realizes, single-writer-per-FQN (global), target-faithfulness,
`(reads-sound-~)`, `(~-target-preserving)`, per-run DAG-order for both,
`StaticPrec` well-founded and `(next-~-insensitive)` give
`S_final(R₁) ~_St S_final(R₂)` and `O(R₁) ~_O O(R₂)` — i.e. `R₁ ≈ R₂` (D8′). -/
theorem T2_of_A {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation] [Setoid L.Call]
    {reads : Statement FQN Query → FQN → Prop}
    
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (hL : LevelSoundT L)
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀)
    (hTF1 : TargetFaithfulL comp₁) (hTF2 : TargetFaithfulL comp₂)
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : Gen.DAGOrder reads R₁) (hDAG2 : Gen.DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P)) (hNTI : NextTildeInsensitive P)
    (hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree L reads comp₁ comp₂ (R₁.stmt j))
    (hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i)) :
    StateEquiv (SFinalL R₁) (SFinalL R₂) ∧ ObsEquiv R₁ R₂ ∧ BehEquiv R₁ R₂ := by
  -- `valueAgreeT` delivers the *bundled* fact (`SFinalL` agreement together
  -- with the full `NodeAgreeConclusionT` for each FQN's candidate writer);
  -- the first projection is the state half of `R₁ ≈ R₂`, the bundle as a
  -- whole is what `nodeAgreeFinalT` needs to cover every node, read-only
  -- ones included. `hAWrite`/`hReadRes` split `(A~)` into its write-turn
  -- call-agreement half and its read-turn result-agreement conclusion —
  -- the split segmented matching (Module 3) forces, since it cannot supply
  -- blanket `(A~)` at `Read` turns at all (see Module 3's `crossReadAgree`).
  have hVAfull := valueAgreeT hL R₁ R₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI
    hAWrite hReadRes
  have hVA : StateEquiv (SFinalL R₁) (SFinalL R₂) := fun o => (hVAfull o).1
  have hO : ObsEquiv R₁ R₂ := by
    constructor
    · intro n r hr
      exact (isObsAgreeT n (nodeAgreeFinalT hL.preserve R₁ R₂ hTF1 hTF2 hDAG1 hDAG2 hNTI
        hVAfull n hReadRes)).1 r hr
    · intro n r hr
      exact (isObsAgreeT n (nodeAgreeFinalT hL.preserve R₁ R₂ hTF1 hTF2 hDAG1 hDAG2 hNTI
        hVAfull n hReadRes)).2 r hr
  exact ⟨hVA, hO, hVA, hO⟩
/-! ## Equality is the special case -/

section EqInst

local instance eqSetoidInst (α : Type) : Setoid α := ⟨Eq, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩

theorem resEquiv_iff {Relation : Type} (r r' : Result Relation) : ResEquiv r r' ↔ r = r' := by
  cases r with
  | ok => cases r' with
    | ok => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | rel b => exact ⟨fun h => h.elim, fun h => by cases h⟩
  | rel a => cases r' with
    | ok => exact ⟨fun h => h.elim, fun h => by cases h⟩
    | rel b => exact ⟨fun h => congrArg Result.rel h, fun h => by injection h⟩

theorem optEquiv_iff {Relation : Type} (r r' : Option Relation) : OptEquiv r r' ↔ r = r' := by
  cases r with
  | none => cases r' with
    | none => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | some b => exact ⟨fun h => h.elim, fun h => by cases h⟩
  | some a => cases r' with
    | none => exact ⟨fun h => h.elim, fun h => by cases h⟩
    | some b => exact ⟨fun h => congrArg some h, fun h => by injection h⟩

theorem histEquiv_iff {FQN Query Relation : Type} (H H' : History FQN Query Relation) :
    HistEquiv H H' ↔ H = H' := by
  unfold HistEquiv
  induction H generalizing H' with
  | nil => cases H' with
    | nil => exact ⟨fun _ => rfl, fun _ => LForall₂.nil⟩
    | cons b l' => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | cons a l ih => cases H' with
    | nil => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | cons b l' =>
      constructor
      · intro h
        cases h with
        | cons hab ht =>
          have h1 : a.1 = b.1 := hab.1
          have h2 : a.2 = b.2 := (resEquiv_iff _ _).1 hab.2
          have h3 := (ih l').1 ht
          rw [Prod.ext h1 h2, h3]
      · intro h
        injection h with h1 h2
        exact LForall₂.cons ⟨congrArg Prod.fst h1, (resEquiv_iff _ _).2 (congrArg Prod.snd h1)⟩
          ((ih l').2 h2)

/-- Level soundness at equality implies level soundness up to the (equality)
equivalence. -/
theorem levelSound_toT {FQN Relation : Type} {L : Level FQN Relation} (hL : LevelSound L) :
    LevelSoundT L where
  preserve := hL.preserve
  target_pres := fun c c' h => congrArg L.target h
  reads_sound := fun c S S' h t ht =>
    (optEquiv_iff _ _).2 (hL.reads_sound c S S' (fun o ho => (optEquiv_iff _ _).1 (h o ho)) t ht)
  ans_sound := fun c S S' h =>
    (optEquiv_iff _ _).2 (hL.ans_sound c S S' (fun o ho => (optEquiv_iff _ _).1 (h o ho)))
  step_congr := fun c c' h S t _ => by
    have : c = c' := h
    subst this; exact OptEquiv.refl _
  ans_congr := fun c c' h S => by
    have : c = c' := h
    subst this; exact OptEquiv.refl _

/-- Module 1's `T2_2_of_A`, derived from the equivalence-parametrized core with
`≈` := `=`. -/
theorem T2_of_A_eq {Nodes FQN Query Relation : Type} {L : Level FQN Relation}
    [DecidableEq FQN] [DecidableEq Nodes]
    {reads : Statement FQN Query → FQN → Prop}
    (hL : LevelSound L)
    {P : Project Nodes FQN Query Relation}
    {comp₁ comp₂ : Comp FQN Query Relation L} {S₀ : State FQN Relation}
    (R₁ : LiveRunL P L comp₁ S₀) (R₂ : LiveRunL P L comp₂ S₀)
    (hTF1 : TargetFaithfulL comp₁) (hTF2 : TargetFaithfulL comp₂)
    (hUWG : UniqueWriterGlobal P) (hCRS1 : CompiledReadsSoundL reads comp₁)
    (hDAG1 : Gen.DAGOrder reads R₁) (hDAG2 : Gen.DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P))
    (hA : ∀ j, 1 ≤ j → j ≤ R₁.N → comp₁ (R₁.stmt j) = comp₂ (R₁.stmt j)) :
    (∀ n, ∀ r, isObs R₁.node R₁.stmt R₁.res R₁.N n r ↔ isObs R₂.node R₂.stmt R₂.res R₂.N n r) ∧
    SFinalL R₁ = SFinalL R₂ := by
  have hLT := levelSound_toT hL
  have hNTI : NextTildeInsensitive P := fun n H H' h => by rw [(histEquiv_iff _ _).1 h]
  have hA' : ∀ j, 1 ≤ j → j ≤ R₁.N →
      LForall₂ (· ≈ ·) (comp₁ (R₁.stmt j)) (comp₂ (R₁.stmt j)) := by
    intro j hj1 hjN
    rw [hA j hj1 hjN]
    exact LForall₂.refl (fun _ => Setoid.refl _) _
  have hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree L reads comp₁ comp₂ (R₁.stmt j) :=
    fun j hj1 hjN _ => writeAgree_of_forall₂ hLT hCRS1 hTF1 _ (effCalls_congr hLT (hA' j hj1 hjN))
  have hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL comp₁ R₁.stmt S₀ j o') (stateAtL comp₂ R₂.stmt S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i) := by
    intro j i hj1 hjN hi1 hiN hstmt_eq _ hSagree
    have hresA := R₁.res_eq j hj1 hjN
    have hresB := R₂.res_eq i hi1 hiN
    rw [← hstmt_eq] at hresB
    exact stepAgree hLT hCRS1 (R₁.stmt j) (stateAtL comp₁ R₁.stmt S₀ j)
      (stateAtL comp₂ R₂.stmt S₀ i) hSagree (hA' j hj1 hjN) _ _ hresA hresB
  have h := T2_of_A hLT R₁ R₂ hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI hAWrite hReadRes
  refine ⟨fun n r => ⟨fun hr => ?_, fun hr => ?_⟩, funext fun o => ?_⟩
  · obtain ⟨r', hr', hrr⟩ := h.2.1.1 n r hr
    rw [(resEquiv_iff _ _).1 hrr]; exact hr'
  · obtain ⟨r', hr', hrr⟩ := h.2.1.2 n r hr
    rw [(resEquiv_iff _ _).1 hrr]; exact hr'
  · exact (optEquiv_iff _ _).1 (h.1 o)

end EqInst

end Eqv

/-! ## Driver instance is sound, and agrees with today's definitions -/

theorem driverLevel_sound {FQN Query Relation : Type} [DecidableEq FQN]
    {ret : State FQN Relation → Query → Relation}
    {reads : Statement FQN Query → FQN → Prop} (hRS : ReadsSound reads ret) :
    LevelSound (driverLevel ret reads) where
  preserve c S o h := execS_preserve ret S c o h
  reads_sound c S S' hag t ht := by
    cases c with
    | write o q =>
      have hto : o = t := Option.some.inj ht
      subst hto
      have := hRS (Statement.write o q) S S' hag
      simp only [driverLevel, execS, qOf] at this ⊢
      simp [this]
    | read q => simp [driverLevel, target] at ht
  ans_sound c S S' hag := by
    cases c with
    | write o q => rfl
    | read q =>
      have := hRS (Statement.read q) S S' hag
      simp only [driverLevel, qOf] at this ⊢
      simp [this]

theorem driverLevel_preserve {FQN Query Relation : Type} [DecidableEq FQN]
    (ret : State FQN Relation → Query → Relation)
    (reads : Statement FQN Query → FQN → Prop) :
    LevelPreserve (driverLevel ret reads) :=
  fun c S o h => execS_preserve ret S c o h

theorem driverLevel_targetFaithful {FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    {ret : State FQN Relation → Query → Relation}
    {reads : Statement FQN Query → FQN → Prop}
    {E : Engine FQN Query MethodName Args} (hTF : TargetFaithful E) :
    TargetFaithfulL (L := driverLevel ret reads) (drvE E) := by
  intro stmt c hc hne
  cases stmt with
  | write o q =>
    cases c with
    | write o'' q'' => exact congrArg some (hTF.1 o q o'' q'' hc)
    | read _ => exact absurd rfl hne
  | read q =>
    cases c with
    | write o'' q'' => exact absurd hc (hTF.2 q o'' q'')
    | read _ => exact absurd rfl hne

theorem driverLevel_compiledReadsSound {FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    {ret : State FQN Relation → Query → Relation}
    {reads : Statement FQN Query → FQN → Prop}
    {E : Engine FQN Query MethodName Args} (hCRS : CompiledReadsSound reads E) :
    CompiledReadsSoundL reads (L := driverLevel ret reads) (drvE E) := hCRS

theorem rL_driver {FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    (ret : State FQN Relation → Query → Relation)
    (reads : Statement FQN Query → FQN → Prop)
    (E : Engine FQN Query MethodName Args) (S : State FQN Relation)
    (stmt : Statement FQN Query) :
    rL (L := driverLevel ret reads) (drvE E) S stmt = rE ret E S stmt := by
  cases stmt with
  | write o q => rfl
  | read q =>
    simp only [rL, rE]
    simp only [driverLevel]
    generalize (drvE E (Statement.read q)).getLast? = g
    cases g with
    | none => rfl
    | some c => cases c <;> rfl

/-- A driver-boundary `LiveRun` is exactly a `LiveRunL` at the driver level. -/
def LiveRun.toL {Nodes FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    [DecidableEq Nodes] {P : Project Nodes FQN Query Relation}
    {E : Engine FQN Query MethodName Args}
    {ret : State FQN Relation → Query → Relation}
   
    {S₀ : State FQN Relation} (reads : Statement FQN Query → FQN → Prop)
    (R : LiveRun P E ret S₀) :
    LiveRunL P (driverLevel ret reads) (drvE E) S₀ where
  N := R.N
  node := R.node
  stmt := R.stmt
  res := R.res
  stmt_eq := R.stmt_eq
  res_eq := fun i h1 h2 => by
    have := R.res_eq i h1 h2
    rw [← rL_driver ret reads E] at this
    exact this
  valid2 := R.valid2

/-- **T2₂, given `(A)`.** The part of T2₂'s argument that runs once
`(A) : ∀ j, drv_{E₁}(stmt_j) = drv_{E₂}(stmt_j)` is in hand: single-writer-
per-FQN (global), target-faithfulness, `(reads-sound)`, per-run DAG-order for
both, and `StaticPrec` well-founded together give `R₁'`s `H(n,·)` equals
`R₂`'s entry for entry for every node, `O(R₁) = O(R₂)`, and
`S_final(R₁) = S_final(R₂)` — hence `R₁ ≈ R₂`, even though the two runs'
schedules may differ entirely and `E₁ ≠ E₂`. `T2_2` below supplies `(A)`
from `ConvergentReplay` + `PerTurnAligned` rather than assuming it. -/
theorem T2_2_of_A {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [DecidableEq MethodName] [DecidableEq Args]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    (hRS : ReadsSound reads ret)
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hTF1 : TargetFaithful E₁) (hTF2 : TargetFaithful E₂)
    (hUWG : UniqueWriterGlobal P) (hCRS1 : CompiledReadsSound reads E₁)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P))
    (hA : ∀ j, 1 ≤ j → j ≤ R₁.N → drvE E₁ (R₁.stmt j) = drvE E₂ (R₁.stmt j)) :
    (∀ n, ∀ r, isObs R₁.node R₁.stmt R₁.res R₁.N n r ↔ isObs R₂.node R₂.stmt R₂.res R₂.N n r) ∧
    SFinal R₁ = SFinal R₂ ∧ BehEquiv R₁ R₂ := by
  have h := Eqv.T2_of_A_eq (driverLevel_sound hRS) (R₁.toL reads) (R₂.toL reads)
    (driverLevel_targetFaithful hTF1) (driverLevel_targetFaithful hTF2) hUWG
    (driverLevel_compiledReadsSound hCRS1) hDAG1 hDAG2 hSWF hA
  exact ⟨h.1, h.2, h.2, h.1⟩
/-- `List.map f` is injective whenever `f` is. -/
theorem list_map_injective {α β : Type} {f : α → β} (hf : Function.Injective f) :
    ∀ l1 l2 : List α, l1.map f = l2.map f → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [hf h1, list_map_injective hf l1 l2 h2]

/-- **T2₂.** `ConvergentReplay` + `PerTurnAligned` at the `adapter→driver`
boundary, plus `driverView` injective, recover `(A)` directly (via
`callsB_agree_of_aligned` + `list_map_injective`) and hand it to
`T2_2_of_A`. -/
theorem T2_2 {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [DecidableEq MethodName] [DecidableEq Args]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (hRS : ReadsSound reads ret) (hCRS1 : CompiledReadsSound reads E₁)
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hTF1 : TargetFaithful E₁) (hTF2 : TargetFaithful E₂)
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P))
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (hDriverInj : Function.Injective driverView)
    (hCV : ConvergentReplay R₁ E₂ adapterView driverView Boundary.adapterDriver)
    (hAl : PerTurnAligned R₁ E₂ adapterView driverView Boundary.adapterDriver) :
    (∀ n, ∀ r, isObs R₁.node R₁.stmt R₁.res R₁.N n r ↔ isObs R₂.node R₂.stmt R₂.res R₂.N n r) ∧
    SFinal R₁ = SFinal R₂ ∧ BehEquiv R₁ R₂ := by
  have hcb := callsB_agree_of_aligned R₁ adapterView driverView Boundary.adapterDriver hCV hAl
  have hA : ∀ j, 1 ≤ j → j ≤ R₁.N → drvE E₁ (R₁.stmt j) = drvE E₂ (R₁.stmt j) := by
    intro j hj1 hjN
    exact list_map_injective hDriverInj _ _ (hcb j hj1 hjN)
  exact T2_2_of_A hRS R₁ R₂ hTF1 hTF2 hUWG hCRS1 hDAG1 hDAG2 hSWF hA

/-! ## Adapter boundary: adapter-level semantics, run link, and T2₁ -/

/-- The adapter level's own semantics: what an adapter call reads, writes, does
to state, and returns. All four are oracles, exactly as `reads`/`ret` are at the
driver level; their meaning is constrained only by `LevelSound`. -/
structure AdapterSem (FQN Relation MethodName Args : Type) where
  step : State FQN Relation → AdapterCall MethodName Args → State FQN Relation
  ret : State FQN Relation → AdapterCall MethodName Args → Relation
  target : AdapterCall MethodName Args → Option FQN
  reads : AdapterCall MethodName Args → FQN → Prop

def AdapterSem.level {FQN Relation MethodName Args : Type}
    (A : AdapterSem FQN Relation MethodName Args) : Level FQN Relation :=
  adapterLevel A.step A.ret A.target A.reads

/-- `E`'s adapter-level compilation `α`, as a `Comp` at the adapter level. -/
def alphaComp {FQN Query Relation MethodName Args : Type}
    (A : AdapterSem FQN Relation MethodName Args)
    (E : Engine FQN Query MethodName Args) : Comp FQN Query Relation A.level :=
  E.α

/-- A driver-boundary run is also an adapter-level run: along it, the adapter
level's own state evolution and results agree with the driver level's. -/
structure RunLink {Nodes FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    [DecidableEq Nodes] {P : Project Nodes FQN Query Relation}
    (A : AdapterSem FQN Relation MethodName Args)
    {ret : State FQN Relation → Query → Relation}
    {E : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) : Prop where
  state_link : ∀ i, stateAtL (alphaComp A E) R.stmt S₀ i = stateAt R.stmt ret E S₀ i
  res_link : ∀ i, 1 ≤ i → i ≤ R.N →
    rL (alphaComp A E) (stateAtL (alphaComp A E) R.stmt S₀ i) (R.stmt i) = some (R.res i)

/-- The same run, viewed at the adapter level. -/
def LiveRun.toAdapter {Nodes FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    [DecidableEq Nodes] {P : Project Nodes FQN Query Relation}
    {A : AdapterSem FQN Relation MethodName Args}
    {ret : State FQN Relation → Query → Relation}
    {E : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) (hk : RunLink A R) :
    LiveRunL P A.level (alphaComp A E) S₀ where
  N := R.N
  node := R.node
  stmt := R.stmt
  res := R.res
  stmt_eq := R.stmt_eq
  res_eq := hk.res_link
  valid2 := R.valid2

/-- **T2₁.** `ConvergentReplay` + `PerTurnAligned` at the `core→adapter`
boundary, plus `adapterView` injective, give `α`-agreement
(`callsB_agree_of_aligned` + `list_map_injective`); the generic argument then
runs at the adapter level, with no assumption about `δ`. `RunLink` says both
runs' adapter-level semantics `A` are coherent with their driver-level behavior. -/
theorem T2_1 {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [DecidableEq MethodName] [DecidableEq Args]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (A : AdapterSem FQN Relation MethodName Args) (hAs : LevelSound A.level)
    (hCRS1 : CompiledReadsSoundL reads (alphaComp (Query := Query) A E₁))
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hk₁ : RunLink A R₁) (hk₂ : RunLink A R₂)
    (hTF1 : TargetFaithfulL (alphaComp (Query := Query) A E₁))
    (hTF2 : TargetFaithfulL (alphaComp (Query := Query) A E₂))
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P))
    (adapterView : AdapterCall MethodName Args → CallView MethodName Args)
    (driverView : DriverCall FQN Query → CallView MethodName Args)
    (hAdapterInj : Function.Injective adapterView)
    (hCV : ConvergentReplay R₁ E₂ adapterView driverView Boundary.coreAdapter)
    (hAl : PerTurnAligned R₁ E₂ adapterView driverView Boundary.coreAdapter) :
    (∀ n, ∀ r, isObs R₁.node R₁.stmt R₁.res R₁.N n r ↔ isObs R₂.node R₂.stmt R₂.res R₂.N n r) ∧
    SFinal R₁ = SFinal R₂ := by
  have hcb := callsB_agree_of_aligned R₁ adapterView driverView Boundary.coreAdapter hCV hAl
  have hα : ∀ j, 1 ≤ j → j ≤ R₁.N → E₁.α (R₁.stmt j) = E₂.α (R₁.stmt j) := by
    intro j hj1 hjN
    exact list_map_injective hAdapterInj _ _ (hcb j hj1 hjN)
  have h := Eqv.T2_of_A_eq hAs (R₁.toAdapter hk₁) (R₂.toAdapter hk₂) hTF1 hTF2 hUWG hCRS1
    hDAG1 hDAG2 hSWF hα
  refine ⟨h.1, ?_⟩
  have e1 : SFinal R₁ = SFinalL (R₁.toAdapter hk₁) := funext fun o => (congrFun (hk₁.state_link _) o).symm
  have e2 : SFinal R₂ = SFinalL (R₂.toAdapter hk₂) := funext fun o => (congrFun (hk₂.state_link _) o).symm
  rw [e1, e2]; exact h.2

namespace Eqv

theorem ResEquiv.trans {Relation : Type} [Setoid Relation] {a b c : Result Relation}
    (h1 : ResEquiv a b) (h2 : ResEquiv b c) : ResEquiv a c := by
  cases a <;> cases b <;> cases c <;>
    first | exact h1.elim | exact h2.elim | trivial | exact Setoid.trans h1 h2

theorem StateEquiv.symm {FQN Relation : Type} [Setoid Relation] {S S' : State FQN Relation}
    (h : StateEquiv S S') : StateEquiv S' S := fun o => OptEquiv.symm (h o)

theorem StateEquiv.trans {FQN Relation : Type} [Setoid Relation] {S S' S'' : State FQN Relation}
    (h1 : StateEquiv S S') (h2 : StateEquiv S' S'') : StateEquiv S S'' :=
  fun o => OptEquiv.trans (h1 o) (h2 o)

/-- Pointwise-`~_Res`-related result functions give `HistEquiv` histories. -/
theorem histAt_equiv {Nodes FQN Query Relation : Type} [DecidableEq Nodes] [Setoid Relation]
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query)
    (res res' : Nat → Result Relation) (N : Nat)
    (h : ∀ j, 1 ≤ j → j ≤ N → ResEquiv (res j) (res' j)) (n : Nodes) :
    ∀ i, i ≤ N + 1 → HistEquiv (histAt node stmt res n i) (histAt node stmt res' n i)
  | 0, _ => LForall₂.nil
  | i + 1, hi => by
    have ih := histAt_equiv node stmt res res' N h n i (by omega)
    simp only [histAt]
    by_cases hc : 1 ≤ i ∧ node i = n
    · rw [if_pos hc, if_pos hc]
      exact ih.append (LForall₂.cons ⟨rfl, h i hc.1 (by omega)⟩ LForall₂.nil)
    · rw [if_neg hc, if_neg hc]
      simpa using ih

/-- `isObs` transfers across pointwise-`~_Res`-related result functions. -/
theorem isObs_equiv {Nodes FQN Query Relation : Type} [DecidableEq Nodes] [Setoid Relation]
    (node : Nat → Nodes) (stmt : Nat → Statement FQN Query)
    (res res' : Nat → Result Relation) (N : Nat)
    (h : ∀ j, 1 ≤ j → j ≤ N → ResEquiv (res j) (res' j)) (n : Nodes) (r : Result Relation)
    (hr : isObs node stmt res N n r) :
    ∃ r', isObs node stmt res' N n r' ∧ ResEquiv r r' := by
  have hH := histAt_equiv node stmt res res' N h n (N + 1) (Nat.le_refl _)
  unfold isObs at hr ⊢
  rcases hH.getLast? with ⟨h1, h2⟩ | ⟨a, b, h1, h2, hab⟩
  · rw [h1] at hr; simp at hr
  · rw [h1] at hr
    simp only [Option.map_some] at hr
    refine ⟨b.2, ?_, ?_⟩
    · rw [h2]; rfl
    · rw [← Option.some.inj hr]; exact hab.2

/-- A driver-boundary run is also an adapter-level run, up to `~_Res`/`~_R`: the
adapter level's own state evolution is `~`-equivalent to the driver level's, and
its result at each turn is `~_Res` to the recorded one. -/
structure RunLinkT {Nodes FQN Query Relation MethodName Args : Type} [DecidableEq FQN]
    [DecidableEq Nodes] [Setoid Relation] {P : Project Nodes FQN Query Relation}
    (A : AdapterSem FQN Relation MethodName Args)
    {ret : State FQN Relation → Query → Relation}
    {E : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) : Prop where
  state_link : ∀ i, StateEquiv (stateAtL (alphaComp A E) R.stmt S₀ i) (stateAt R.stmt ret E S₀ i)
  res_link : ∀ i, 1 ≤ i → i ≤ R.N →
    ∃ r, rL (alphaComp A E) (stateAtL (alphaComp A E) R.stmt S₀ i) (R.stmt i) = some r ∧
      ResEquiv r (R.res i)

open Classical in
/-- The adapter-level run whose results are `A`'s own (not the recorded ones). -/
noncomputable def toAdapterT {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {P : Project Nodes FQN Query Relation}
    {A : AdapterSem FQN Relation MethodName Args}
    {ret : State FQN Relation → Query → Relation}
    {E : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (R : LiveRun P E ret S₀) (hNTI : NextTildeInsensitive P) (hk : RunLinkT A R) :
    LiveRunL P A.level (alphaComp A E) S₀ where
  N := R.N
  node := R.node
  stmt := R.stmt
  res := fun i => if h : 1 ≤ i ∧ i ≤ R.N then Classical.choose (hk.res_link i h.1 h.2) else R.res i
  stmt_eq := fun i h1 h2 => by
    have hres : ∀ j, 1 ≤ j → j ≤ R.N → ResEquiv (R.res j)
        (if h : 1 ≤ j ∧ j ≤ R.N then Classical.choose (hk.res_link j h.1 h.2) else R.res j) := by
      intro j hj1 hjN
      rw [dif_pos ⟨hj1, hjN⟩]
      exact ResEquiv.symm (Classical.choose_spec (hk.res_link j hj1 hjN)).2
    have hH := histAt_equiv R.node R.stmt R.res _ R.N hres (R.node i) i (by omega)
    rw [← hNTI _ _ _ hH]
    exact R.stmt_eq i h1 h2
  res_eq := fun i h1 h2 => by
    show rL (alphaComp A E) (stateAtL (alphaComp A E) R.stmt S₀ i) (R.stmt i) = some
      (if h : 1 ≤ i ∧ i ≤ R.N then Classical.choose (hk.res_link i h.1 h.2) else R.res i)
    rw [dif_pos ⟨h1, h2⟩]
    exact (Classical.choose_spec (hk.res_link i h1 h2)).1
  valid2 := fun n => by
    have hres : ∀ j, 1 ≤ j → j ≤ R.N → ResEquiv (R.res j)
        (if h : 1 ≤ j ∧ j ≤ R.N then Classical.choose (hk.res_link j h.1 h.2) else R.res j) := by
      intro j hj1 hjN
      rw [dif_pos ⟨hj1, hjN⟩]
      exact ResEquiv.symm (Classical.choose_spec (hk.res_link j hj1 hjN)).2
    have hH := histAt_equiv R.node R.stmt R.res _ R.N hres n (R.N + 1) (Nat.le_refl _)
    rw [← hNTI _ _ _ hH]
    exact R.valid2 n

/-- **Adapter-boundary core, given `(A~)` at the adapter level.** The T2 argument
run at the adapter level on the adapter-level runs `toAdapterT` builds, then
transported back to the recorded driver-boundary runs through `RunLinkT`. -/
theorem T2_adapter {Nodes FQN Query Relation MethodName Args : Type}
    [DecidableEq FQN] [DecidableEq Nodes] [Setoid Relation]
    {reads : Statement FQN Query → FQN → Prop}
    {ret : State FQN Relation → Query → Relation}
    {P : Project Nodes FQN Query Relation}
    {E₁ E₂ : Engine FQN Query MethodName Args} {S₀ : State FQN Relation}
    (A : AdapterSem FQN Relation MethodName Args) [Setoid A.level.Call]
    (hAs : LevelSoundT A.level)
    (R₁ : LiveRun P E₁ ret S₀) (R₂ : LiveRun P E₂ ret S₀)
    (hk₁ : RunLinkT A R₁) (hk₂ : RunLinkT A R₂)
    (hTF1 : TargetFaithfulL (alphaComp (Query := Query) A E₁))
    (hTF2 : TargetFaithfulL (alphaComp (Query := Query) A E₂))
    (hUWG : UniqueWriterGlobal P)
    (hDAG1 : DAGOrder reads R₁) (hDAG2 : DAGOrder reads R₂)
    (hSWF : WellFounded (StaticPrec reads P)) (hNTI : NextTildeInsensitive P)
    (hAWrite : ∀ j, 1 ≤ j → j ≤ R₁.N → (∃ o', target (R₁.stmt j) = some o') →
      WriteAgree A.level reads (alphaComp (Query := Query) A E₁) (alphaComp (Query := Query) A E₂)
        (R₁.stmt j))
    (hReadRes : ∀ j i, 1 ≤ j → j ≤ R₁.N → 1 ≤ i → i ≤ R₂.N →
      R₁.stmt j = R₂.stmt i → target (R₁.stmt j) = none →
      (∀ o', reads (R₁.stmt j) o' →
        OptEquiv (stateAtL (alphaComp (Query := Query) A E₁) R₁.stmt S₀ j o')
          (stateAtL (alphaComp (Query := Query) A E₂) R₂.stmt S₀ i o')) →
      ResEquiv (R₁.res j) (R₂.res i)) :
    StateEquiv (SFinal R₁) (SFinal R₂) ∧
    (∀ n r, isObs R₁.node R₁.stmt R₁.res R₁.N n r →
      ∃ r', isObs R₂.node R₂.stmt R₂.res R₂.N n r' ∧ ResEquiv r r') ∧
    (∀ n r, isObs R₂.node R₂.stmt R₂.res R₂.N n r →
      ∃ r', isObs R₁.node R₁.stmt R₁.res R₁.N n r' ∧ ResEquiv r r') := by
  have hres1 : ∀ j, 1 ≤ j → j ≤ R₁.N → ResEquiv (R₁.res j) ((toAdapterT R₁ hNTI hk₁).res j) := by
    intro j hj1 hjN
    show ResEquiv (R₁.res j)
      (if h : 1 ≤ j ∧ j ≤ R₁.N then Classical.choose (hk₁.res_link j h.1 h.2) else R₁.res j)
    rw [dif_pos ⟨hj1, hjN⟩]
    exact ResEquiv.symm (Classical.choose_spec (hk₁.res_link j hj1 hjN)).2
  have hres2 : ∀ j, 1 ≤ j → j ≤ R₂.N → ResEquiv ((toAdapterT R₂ hNTI hk₂).res j) (R₂.res j) := by
    intro j hj1 hjN
    show ResEquiv
      (if h : 1 ≤ j ∧ j ≤ R₂.N then Classical.choose (hk₂.res_link j h.1 h.2) else R₂.res j)
      (R₂.res j)
    rw [dif_pos ⟨hj1, hjN⟩]
    exact (Classical.choose_spec (hk₂.res_link j hj1 hjN)).2
  have hres1' : ∀ j, 1 ≤ j → j ≤ R₁.N → ResEquiv ((toAdapterT R₁ hNTI hk₁).res j) (R₁.res j) :=
    fun j a b => ResEquiv.symm (hres1 j a b)
  have hres2' : ∀ j, 1 ≤ j → j ≤ R₂.N → ResEquiv (R₂.res j) ((toAdapterT R₂ hNTI hk₂).res j) :=
    fun j a b => ResEquiv.symm (hres2 j a b)
  have h := T2_of_A hAs (toAdapterT R₁ hNTI hk₁) (toAdapterT R₂ hNTI hk₂)
    hTF1 hTF2 hUWG hDAG1 hDAG2 hSWF hNTI hAWrite
    (fun j i hj1 hjN hi1 hiN hst hw hag =>
      ResEquiv.trans (hres1' j hj1 hjN)
        (ResEquiv.trans (hReadRes j i hj1 hjN hi1 hiN hst hw hag) (hres2' i hi1 hiN)))
  -- states
  have hS : StateEquiv (SFinal R₁) (SFinal R₂) := by
    have e1 : StateEquiv (SFinal R₁) (SFinalL (toAdapterT R₁ hNTI hk₁)) :=
      StateEquiv.symm (hk₁.state_link (R₁.N + 1))
    have e2 : StateEquiv (SFinalL (toAdapterT R₂ hNTI hk₂)) (SFinal R₂) :=
      hk₂.state_link (R₂.N + 1)
    exact StateEquiv.trans (StateEquiv.trans e1 h.1) e2
  refine ⟨hS, fun n r hr => ?_, fun n r hr => ?_⟩
  · obtain ⟨r1, hr1, e1⟩ := isObs_equiv R₁.node R₁.stmt R₁.res _ R₁.N hres1 n r hr
    obtain ⟨r2, hr2, e2⟩ := h.2.1.1 n r1 hr1
    obtain ⟨r3, hr3, e3⟩ := isObs_equiv R₂.node R₂.stmt _ R₂.res R₂.N hres2 n r2 hr2
    exact ⟨r3, hr3, ResEquiv.trans e1 (ResEquiv.trans e2 e3)⟩
  · obtain ⟨r1, hr1, e1⟩ := isObs_equiv R₂.node R₂.stmt R₂.res _ R₂.N hres2' n r hr
    obtain ⟨r2, hr2, e2⟩ := h.2.1.2 n r1 hr1
    obtain ⟨r3, hr3, e3⟩ := isObs_equiv R₁.node R₁.stmt _ R₁.res R₁.N hres1' n r2 hr2
    exact ⟨r3, hr3, ResEquiv.trans e1 (ResEquiv.trans e2 e3)⟩

end Eqv

end Module1
end Formalization
