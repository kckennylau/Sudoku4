/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Tactic.Core
import Mathlib.Lean.Expr.Basic
import Mathlib.Data.Fintype.Basic

/-! # Tactic for destructing Fin n

This is like `fin_cases`, but for `Fin`, so we write `Fin_cases`.
-/

namespace Fin

def CheckFrom {n} (P : Prop) (i : Fin n) (start : Fin n := by exact 0) : Prop :=
  start ≤ i → P

variable {n} {P : Prop} {i start : Fin n}

theorem cases' [NeZero n] (i : Fin n) (s : CheckFrom P i) : P :=
  s <| Nat.zero_le i

theorem CheckFrom.step (next : Fin n) (curr : i = start → P) (ih : CheckFrom P i next)
    (eq : (start : ℕ).succ = next := by rfl) :
    CheckFrom P i start := fun hi ↦
  (eq_or_lt_of_le (α := ℕ) hi).elim (curr <| by rw [Fin.ext_iff, ·]) fun h ↦
    ih <| show (next : ℕ) ≤ i from eq ▸ h

theorem CheckFrom.last (curr : i = start → P) (eq : (start : ℕ).succ = n := by rfl) :
    CheckFrom P i start := fun hi ↦
  curr <| le_antisymm (Nat.le_of_lt_succ <| eq.symm ▸ i.2) hi

end Fin

-- example (P : Fin 4 → Prop) (p : Fin 4) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : P p := by
--   refine p.cases' <| .step 1 ?fc0 <| .step 2 ?fc1 <| .step 3 ?fc2 <| .last ?fc3
--   · rintro rfl; exact h0
--   · rintro rfl; exact h1
--   · rintro rfl; exact h2
--   · rintro rfl; exact h3

namespace Lean.Meta

def mkFinNatLit (nE nonzero : Expr) (i : ℕ) : Expr :=
  have iE := mkRawNatLit i
  mkApp3 (mkConst ``OfNat.ofNat [0]) (mkApp (mkConst ``Fin) nE) iE<|
    mkApp3 (mkConst ``Fin.instOfNat) nE nonzero iE

/-- Makes the expression `eagerReduce (Eq.refl n)`. -/
def eagerReflNat (n : ℕ) : Expr :=
  let nE := mkNatLit n
  mkApp2 (mkConst ``eagerReduce [0]) (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) nE nE) <|
    mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) nE

def finCases' (iID : FVarId) (n : ℕ) (tgt : MVarId) : MetaM (List MVarId) := do
  let typ ← inferType <| .mvar tgt
  if n = 0 then
    if ← isDefEq (.mvar tgt) (mkApp2 (mkConst ``Fin.elim0) typ (.fvar iID)) then
      return []
    else
      return [tgt]
  else
    unless ← isProp typ do throwError "The goal must be a Prop."
    have nE := mkNatLit n
    let nz ← synthInstance =<< mkAppM ``NeZero #[nE]
    let mut new := (← mkFreshExprMVar none default <| .mkSimple s!"fin_tracker").mvarId!
    let mut new_goal : MVarId := default
    have i := Expr.fvar iID
    tgt.assign <| mkApp5 (mkConst ``Fin.cases') nE typ nz i (.mvar new)
    let mut tracker : MVarId := new
    let mut new_goals : Array MVarId := #[]
    let mut start : Expr := mkFinNatLit nE nz 0
    let mut next : Expr := default
    for val in Array.range n.pred do
      next := mkFinNatLit nE nz <| eagerReduce <| val.succ
      new := (← mkFreshExprMVar none default <| .mkSimple s!"fin_tracker_{val}").mvarId!
      new_goal := (← mkFreshExprMVar (some <| .forallE `h (← mkEq i start) typ .default)
        default <| .mkSimple s!"fin_cases_{val}").mvarId!
      tracker.assign <| mkApp8 (mkConst ``Fin.CheckFrom.step) nE typ i start next (.mvar new_goal)
        (.mvar new) (eagerReflNat val.succ)
      start := next
      tracker := new
      let (eq, new_goal') ← new_goal.intro <| .mkSimple s!"fin_temp_{val}"
      (_, new_goal) ← substEq new_goal' eq
      new_goals := new_goals.push new_goal
    have lastNat := eagerReduce n.pred
    have last := mkFinNatLit nE nz lastNat
    new_goal := (← mkFreshExprMVar (some <| .forallE `h (← mkEq i last) typ .default)
      default <| .mkSimple s!"fin_tracker_{lastNat}").mvarId!
    tracker.assign <| mkApp6 (mkConst ``Fin.CheckFrom.last) nE typ i last (.mvar new_goal)
      (eagerReflNat n)
    let (eq, new_goal') ← new_goal.intro <| .mkSimple s!"fin_temp_{lastNat}"
    (_, new_goal) ← substEq new_goal' eq
    return (new_goals.push new_goal).toList

end Lean.Meta

open Lean.Meta

namespace Lean.Elab.Tactic

/-- Perform cases on `i : Fin n`. Substitutes it with the explicit numerals `0`, `1`, `2`, ... -/
elab "Fin_cases " id:ident : tactic => withMainContext do
  let iID ← getFVarId id
  have i := Expr.fvar iID
  let typ ← inferType i
  let (``Fin, #[nE]) := typ.getAppFnArgs | throwError m!"Given {id} should have type `Fin n`."
  let .some n ← liftMetaM <| evalNat nE | throwError m!"{nE} should be an explicit numeral."
  liftMetaTactic <| finCases' iID n

end Lean.Elab.Tactic

-- example (P : Fin 4 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
--     (p q r : Fin 4) : P p := by
--   Fin_cases p
--   · guard_target =ₛ P 0
--     exact h0
--   · guard_target =ₛ P 1
--     exact h1
--   · guard_target =ₛ P 2
--     exact h2
--   · guard_target =ₛ P 3
--     exact h3
