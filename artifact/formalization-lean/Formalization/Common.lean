/-
Shared D1/D2 layer for the `formalization-{1..5}` mechanization series.

This file holds exactly the declarations that are *code-identical* in all five
of the original single-file mechanizations
(`../formalization-{1..5}-lean/FormalizationN.lean`): D1's `Statement`/`Result`
and D2's `State`/`DriverCall`/`execS`. Modules 1–5 import it; nothing here is
re-declared downstream.

Doc comments are Module 1's (Modules 2–5 dropped a few of them verbatim, but
the code is byte-identical); no statement or definition has been altered.
-/

set_option autoImplicit false

namespace Formalization

/-! ## D1 (FQN & ground-truth Statement) -/

variable (FQN Query Relation MethodName Args Nodes : Type)

/-- `Statement := Write(target : FQN, def : Query) | Read(query : Query)` -/
inductive Statement (FQN Query : Type) where
  | write (target : FQN) (defQ : Query)
  | read (query : Query)
  deriving DecidableEq

/-- `Result := Relation | ok` -/
inductive Result (Relation : Type) where
  | rel (r : Relation)
  | ok
  deriving DecidableEq

/-! ## D2 (State & ground-truth execution) -/

/-- `State := FQN ⇀ Relation`, modeled as a total function into `Option`. -/
abbrev State (FQN Relation : Type) := FQN → Option Relation

/-- `DriverCall := Statement` -/
abbrev DriverCall (FQN Query : Type) := Statement FQN Query

/-- `exec(S, Write(o,q)) := S[o ↦ ret(S,q)]`, `exec(S, Read(q)) := S`. -/
def execS {FQN Query Relation : Type} [DecidableEq FQN]
    (ret : State FQN Relation → Query → Relation) :
    State FQN Relation → Statement FQN Query → State FQN Relation
  | S, .write o q => fun o' => if o' = o then some (ret S q) else S o'
  | S, .read _ => S

end Formalization
