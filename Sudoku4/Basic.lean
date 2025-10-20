/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Sudoku4.FinCases
import Mathlib.Data.Matrix.Reflection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.IntervalCases

namespace Sudoku

abbrev Grid (n : ℕ := 3) (Target : Type := ℕ) : Type :=
  Fin (n.mul n) → Fin (n.mul n) → Target

namespace Grid

-- instance (n T) : CoeFun (Grid n T) (fun _ ↦ Fin (n.mul n) → Fin (n.mul n) → T) where
--   coe := toFun

-- @[simp] lemma toFun_eq_coe {n T} {g : Grid n T} : g.toFun = g := rfl

@[ext] lemma ext {n T} {g₁ g₂ : Grid n T} (h : ∀ i j, g₁ i j = g₂ i j) : g₁ = g₂ :=
  funext₂ h

-- (≤) from a partially filled grid to a more filled grid
-- note the ordering: a filled grid `≤ᵍ` a partially filled grid
def Extends {n T} [Zero T] (g₁ g₂ : Grid n T) : Prop :=
  ∀ i j, g₁ i j = g₂ i j ∨ g₂ i j = 0

theorem Extends.of_bne {n} {g₁ g₂ : Grid n} (h : Extends g₁ g₂) {i j}
    (hne : (g₂ i j).beq 0 = false) : g₁ i j = g₂ i j :=
  (h i j).resolve_right <| Nat.ne_of_beq_eq_false hne

-- instance (n T) [Zero T] : LE (Grid n T) where
--   le := Grid.Extends

-- instance (n T) [Zero T] : PartialOrder (Grid n T) where
--   le_refl _ _ _ := .inl rfl
--   le_trans _ _ _ _ _ _ _ := by
--     unfold_projs at *
--     simp only [Extends, Nat.mul_eq, toFun_eq_coe] at *
--     unfold_projs at *
--     grind
--   le_antisymm g₁ g₂ h₁ h₂ := by
--     ext
--     unfold_projs at *
--     simp only [Extends, Nat.mul_eq, toFun_eq_coe] at *
--     grind

def ofRArray {n T} (a : Lean.RArray T) : Grid n T := fun i j ↦
  a.get <| eagerReduce (n.mul n |>.mul i |>.add j)

end Grid

scoped infix:50 " ≤ᵍ " => Grid.Extends

binder_predicate x " ≤ᵍ " y:term => `($x ≤ᵍ $y)

section Meta

open Lean Elab

syntax num_vec := "[" num,+ "]"

scoped elab "make_grid% " "[" g:num_vec,+ "]" : term => do
  let mut grid : Array (Array ℕ) := #[]
  for row in g.getElems do
    let `(num_vec|[$row:num,*]) := row | throwUnsupportedSyntax
    grid := grid.push (row.getElems.map TSyntax.getNat)
  if h : grid.size = 0 then throwError "Grid cannot be empty." else
  have width := grid[0].size
  have n := width.sqrt
  unless (n.mul n).beq width && width.beq grid.size do throwError m!"Grid must be {n^2}-by-{n^2}!"
  for row in grid do unless row.size = width do throwError "Grid does not have constant width."
  have gridF := grid.flatten
  if h : gridF.size = 0 then throwError "Grid cannot be empty." else
  have r := RArray.ofArray gridF (pos_of_ne_zero h)
  let rE ← r.toExpr (mkConst ``Nat) mkNatLit
  return mkApp3 (mkConst ``Grid.ofRArray) (mkNatLit width.sqrt) (mkConst ``Nat) rE

end Meta

abbrev Rules (n : ℕ) (Target : Type) : Type :=
  Grid n Target → Prop

namespace Rules

def Standard {n : ℕ} : Rules n ℕ := fun g ↦
  -- O(n^4 * log(n))
  (∀ i j, 1 ≤ g i j ∧ g i j ≤ n ^ 2) ∧
  -- O(n^2 * n^2 * log(n))  (bitwise algorithm)
  (∀ i j₁ j₂, g i j₁ = g i j₂ → j₁ = j₂) ∧
  -- O(n^2 * n^2 * log(n))
  (∀ i₁ i₂ j, g i₁ j = g i₂ j → i₁ = i₂) ∧
  -- O(n^2 * n^2 * log(n))
  (∀ (i j i₁ j₁ i₂ j₂ : Fin n), g (finProdFinEquiv (i, i₁)) (finProdFinEquiv (j, j₁)) =
    g (finProdFinEquiv (i, i₂)) (finProdFinEquiv (j, j₂)) → i₁ = i₂ ∧ j₁ = j₂)

namespace Standard

/-- a cell c₁ is looking at c₂ means that they are in the same row, column, or box, and they are not
equal. -/
def Looking {n : ℕ} (i₁ j₁ i₂ j₂ : Fin (n.mul n)) : Prop :=
  (i₁ ≠ i₂ ∨ j₁ ≠ j₂) ∧
  (i₁ = i₂ ∨ j₁ = j₂ ∨ (i₁ / n = i₂ / n ∧ j₁ / n = j₂ / n))

/-- Two cells that are looking at each other cannot have the same value. -/
theorem Looking.ne {n} {g : Grid n} (std : Standard g) {i₁ j₁ i₂ j₂} (look : Looking i₁ j₁ i₂ j₂) :
    g i₁ j₁ ≠ g i₂ j₂ := by
  obtain ⟨ne, rfl | rfl | same⟩ := look
  · exact mt (std.2.1 _ _ _) <| ne.neg_resolve_left rfl
  · exact mt (std.2.2.1 _ _ _) <| ne.neg_resolve_right rfl
  · have h₁ := (finProdFinEquiv (m := n) (n := n)).apply_symm_apply
    have h₂ := finProdFinEquiv_symm_apply (m := n) (n := n)
    have h₃ : i₁.divNat = i₂.divNat := Fin.ext same.1
    have h₄ : j₁.divNat = j₂.divNat := Fin.ext same.2
    have h₅ := (finProdFinEquiv (m := n) (n := n)).symm.injective
    rw [← h₁ i₁, ← h₁ j₁, ← h₁ i₂, ← h₁ j₂, h₂, h₂, h₃, h₄]
    exact mt (std.2.2.2 _ _ _ _ _ _) fun h ↦ ne.elim
      (not_not_intro <| h₅ <| by rw [h₂, h₂, h₃, h.1])
      (not_not_intro <| h₅ <| by rw [h₂, h₂, h₄, h.2])

def Eliminated {n} (g : Grid n) (i j : Fin (n.mul n)) (val : ℕ) (start := 1) : Prop :=
  ∀ val', start ≤ val' → val' ≤ n ^ 2 → val' = val ∨ ∃ i' j', Looking i j i' j' ∧ g i' j' = val'

/-- Eliminates all other possibilities for a given cell using the row rule, column rules, and box
rule. -/
theorem elim {n} {g : Grid n} (r : Standard g) {i j val} (cert : Eliminated g i j val) :
    g i j = val :=
  (r.1 i j).elim fun lo hi ↦ (cert (g i j) lo hi).resolve_right fun ⟨_, _, look, eq⟩ ↦
    look.ne r eq.symm

section

/-- Eliminate one value. -/
def Eliminate₁ {n} (g : Grid n) (i j : Fin (n.mul n)) (val val' : ℕ) : Prop :=
  val' = val ∨ ∃ i' j', Looking i j i' j' ∧ g i' j' = val'

variable {n} {g : Grid n} {i j : Fin (n.mul n)} {val val' start : ℕ}

theorem Eliminated.step (next : ℕ) (now : Eliminate₁ g i j val start)
    (ih : Eliminated g i j val next) (eq : start.succ = next := by rfl) :
    Eliminated g i j val start := fun _ lo hi ↦
  (eq_or_lt_of_le lo).elim (fun h ↦ h ▸ now) (fun lt ↦ ih _ (eq ▸ lt) hi)

theorem Eliminated.finish : Eliminated g i j val (n.mul n |>.succ) := fun _ lo hi ↦
  absurd (lo.trans hi) <| sq n ▸ Nat.not_succ_le_self _

theorem Eliminate₁.self : Eliminate₁ g i j val val :=
  .inl rfl

theorem Eliminate₁.row {j'} (h : g i j' = val')
    (ne : (j : ℕ).beq j' = false := by exact eagerReduce (Eq.refl false)) :
    Eliminate₁ g i j val val' :=
  .inr ⟨i, j', ⟨.inr <| Fin.val_ne_iff.mp <| Nat.ne_of_beq_eq_false ne, .inl rfl⟩, h⟩

theorem Eliminate₁.column {i'} (h : g i' j = val')
    (ne : (i : ℕ).beq i' = false := by exact eagerReduce (Eq.refl false)) :
    Eliminate₁ g i j val val' :=
  .inr ⟨i', j, ⟨.inl <| Fin.val_ne_iff.mp <| Nat.ne_of_beq_eq_false ne, .inr <| .inl rfl⟩, h⟩

theorem Eliminate₁.box {i' j'} (h : g i' j' = val')
    (cert : (((i : ℕ).div n |>.beq ((i' : ℕ).div n)) &&
      (((j : ℕ).div n |>.beq ((j' : ℕ).div n)) &&
        !((i : ℕ).beq i' && (j : ℕ).beq j'))) = true := by exact eagerReduce (Eq.refl true)) :
    Eliminate₁ g i j val val' := by
  simp only [Bool.and_eq_true, Bool.not_and, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, Nat.beq_eq] at cert
  refine .inr ⟨_, _, ⟨?_, .inr <| .inr ⟨cert.1, cert.2.1⟩⟩, h⟩
  simp_rw [← Fin.val_ne_iff]
  exact cert.2.2

theorem Eliminate₁.box' (i j i₁ j₁ i₂ j₂ : Fin n)
    (h : g (finProdFinEquiv (i, i₂)) (finProdFinEquiv (j, j₂)) = val')
    (ne : ((i₁ : ℕ).beq i₂ && (j₁ : ℕ).beq j₂) = false := by exact eagerReduce (Eq.refl false)) :
    Eliminate₁ g (finProdFinEquiv (i, i₁)) (finProdFinEquiv (j, j₁)) val val' := by
  refine .inr ⟨_, _, ⟨?_, .inr <| .inr ⟨?_, ?_⟩⟩, h⟩
  · simp_rw [finProdFinEquiv.injective.ne_iff, ne_eq, Prod.mk.injEq, true_and, ← Fin.val_ne_iff]
    simp_rw [Bool.and_eq_false_iff, Bool.eq_false_iff, ne_eq, Nat.beq_eq] at ne
    exact ne
  · change ((finProdFinEquiv.symm (finProdFinEquiv (i, i₁))).1 : ℕ) =
      ((finProdFinEquiv.symm (finProdFinEquiv (i, i₂))).1 : ℕ)
    simp_rw [Equiv.symm_apply_apply]
  · change ((finProdFinEquiv.symm (finProdFinEquiv (j, j₁))).1 : ℕ) =
      ((finProdFinEquiv.symm (finProdFinEquiv (j, j₂))).1 : ℕ)
    simp_rw [Equiv.symm_apply_apply]

end

end Rules.Standard

structure Solvable {n T} [Zero T] (g : Grid n T) (r : Rules n T) : Prop where
  solvable : ∃! g', g' ≤ᵍ g ∧ r g'

theorem Solvable.intro {n T} [Zero T] {g : Grid n T} {r : Rules n T} (sol : Grid n T)
    (h : ∀ g' ≤ᵍ g, r g' → g' = sol) (extend : sol ≤ᵍ g) (hsol : r sol) : Solvable g r :=
  .mk <| .intro sol ⟨extend, hsol⟩ fun _ ⟨h₁, h₂⟩ ↦ h _ h₁ h₂

def test1 : Grid 2 := make_grid%
 [[1, 2, 3, 4],
  [3, 4, 1, 2],
  [2, 1, 0, 3],
  [4, 3, 2, 1]]

-- (heartbeats)
-- 2997709: elab
--  396693: typecheck
set_option trace.profiler.useHeartbeats true
-- set_option trace.profiler true
/- Breakdown:
 660000: 15 given clues (each from 53000 to 35000 decreasing)
 180366: inferring 1 clue
 118921: fin_cases (5 times)
 507069: 16 assumptions (60000 to 5000 each)
 196299: first decide
1345291: second decide
-/
theorem solvable_test1 : Solvable test1 .Standard := by
  refine .intro ?_ (fun g extend std ↦ ?main) ?_ ?_
  case main =>
    -- auto
    have g_0_0 : g 0 0 = 1 := extend.of_bne (eagerReduce (Eq.refl false)) -- 54202
    have g_0_1 : g 0 1 = 2 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_0_2 : g 0 2 = 3 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_0_3 : g 0 3 = 4 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_1_0 : g 1 0 = 3 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_1_1 : g 1 1 = 4 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_1_2 : g 1 2 = 1 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_1_3 : g 1 3 = 2 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_2_0 : g 2 0 = 2 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_2_1 : g 2 1 = 1 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_2_3 : g 2 3 = 3 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_3_0 : g 3 0 = 4 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_3_1 : g 3 1 = 3 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_3_2 : g 3 2 = 2 := extend.of_bne (eagerReduce (Eq.refl false))
    have g_3_3 : g 3 3 = 1 := extend.of_bne (eagerReduce (Eq.refl false))

    have g_2_2 : g 2 2 = 4 := by
      -- auto
      refine std.elim ?_ -- 5375
      refine .step 2 (.row g_2_1) ?_ -- 37161
      refine .step 3 (.column g_3_2) ?_ -- 39342
      refine .step 4 (.box g_2_3) ?_ -- 49044
      refine .step 5 .self ?_ -- 24758
      exact .finish -- 6558

    -- auto
    let result := make_grid% [[1,2,3,4],[3,4,1,2],[2,1,4,3],[4,3,2,1]]
    change g = result
    ext i j; Fin_cases i <;> Fin_cases j <;> assumption

  -- auto
  · unfold_projs
    unfold Grid.Extends
    decide

  -- auto
  · unfold Rules.Standard
    decide

end Sudoku
