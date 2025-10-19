/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Data.Matrix.Reflection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.IntervalCases

namespace Sudoku

@[ext] structure Grid (n : ℕ := 3) (Target : Type := ℕ) : Type where ofFun ::
  toFun : Fin (n.mul n) → Fin (n.mul n) → Target

namespace Grid

instance (n T) : FunLike (Grid n T) (Fin (n.mul n)) (Fin (n.mul n) → T) where
  coe := toFun
  coe_injective' _ _ := congrArg Grid.ofFun

@[simp] lemma toFun_eq_coe {n T} {g : Grid n T} : g.toFun = g := rfl

lemma ext' {n T} {g₁ g₂ : Grid n T} (h : ∀ i j, g₁ i j = g₂ i j) : g₁ = g₂ :=
  Grid.ext <| funext₂ h

-- (≤) from a partially filled grid to a more filled grid
def IsExtension {n T} [Zero T] (g₁ g₂ : Grid n T) : Prop :=
  ∀ i j, g₁ i j = g₂ i j ∨ g₁ i j = 0

theorem IsExtension.of_bne {n} {g₁ g₂ : Grid n} (h : IsExtension g₁ g₂) {i j}
    (hne : (g₁ i j).beq 0 = false) : g₂ i j = g₁ i j :=
  ((h i j).resolve_right <| Nat.ne_of_beq_eq_false hne).symm

instance (n T) [Zero T] : LE (Grid n T) where
  le := Grid.IsExtension

instance (n T) [Zero T] : PartialOrder (Grid n T) where
  le_refl _ _ _ := .inl rfl
  le_trans _ _ _ _ _ _ _ := by
    unfold_projs at *
    simp only [IsExtension, Nat.mul_eq, toFun_eq_coe] at *
    unfold_projs at *
    grind
  le_antisymm g₁ g₂ h₁ h₂ := by
    ext
    unfold_projs at *
    simp only [IsExtension, Nat.mul_eq, toFun_eq_coe] at *
    grind

def ofRArray {n T} (a : Lean.RArray T) : Grid n T :=
  .ofFun fun i j ↦ a.get (n.mul n |>.mul i |>.add j)

end Grid

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

def Rules.standard {n : ℕ} : Rules n ℕ := fun g ↦
  -- O(n^4 * log(n))
  (∀ i j, 1 ≤ g i j ∧ g i j ≤ n ^ 2) ∧
  -- O(n^2 * n^2 * log(n))  (bitwise algorithm)
  (∀ i j₁ j₂, g i j₁ = g i j₂ → j₁ = j₂) ∧
  -- O(n^2 * n^2 * log(n))
  (∀ i₁ i₂ j, g i₁ j = g i₂ j → i₁ = i₂) ∧
  -- O(n^2 * n^2 * log(n))
  (∀ (i j i₁ j₁ i₂ j₂ : Fin n), g (finProdFinEquiv (i, i₁)) (finProdFinEquiv (j, j₁)) =
    g (finProdFinEquiv (i, i₂)) (finProdFinEquiv (j, j₂)) → i₁ = i₂ ∧ j₁ = j₂)

structure Solvable {n T} [Zero T] (g : Grid n T) (r : Rules n T) : Prop where
  solvable : ∃! g', g ≤ g' ∧ r g'

def test1 : Grid 2 := make_grid%
 [[1, 2, 3, 4],
  [3, 4, 1, 2],
  [2, 1, 0, 3],
  [4, 3, 2, 1]]

-- 626 ms
set_option trace.profiler true
theorem solvable_test1 : Solvable test1 .standard := by
  refine .mk <| .intro ?_ ?_ fun g ⟨extend, rules⟩ ↦ ?main
  case main =>
  -- auto
    have g_0_0 : g 0 0 = 1 := extend.of_bne (eagerReduce (Eq.refl false))
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
      obtain ⟨h1, h2⟩ := rules.1 2 2
      have h3 (j) := rules.2.1 2 j 2
      generalize g 2 2 = g22 at *
      interval_cases g22
      · exact absurd (h3 1 g_2_1) (by decide)
      · exact absurd (h3 0 g_2_0) (by decide)
      · exact absurd (h3 3 g_2_3) (by decide)
      · rfl

    -- auto
    let r := by_elab
      Lean.RArray.toExpr (Lean.mkConst ``Nat) Lean.mkNatLit <|
        .ofFn ![1,2,3,4,3,4,1,2,2,1,4,3,4,3,2,1] (Nat.succ_pos _)
    change g = .ofFun ![![1, 2, 3, 4], ![3, 4, 1, 2], ![2, 1, 4, 3], ![4, 3, 2, 1]]
    ext i j; fin_cases i <;> fin_cases j <;> assumption

  -- auto
  · unfold_projs
    unfold Rules.standard Grid.IsExtension
    decide

end Sudoku
