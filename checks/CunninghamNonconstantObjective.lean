import checks.CunninghamRewardTranslation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

/- Exact feasible witnesses in the actual Lean LP. The two vectors were
obtained independently from the source equations. Kernel evaluation, rather
than an imported open theorem or an external arithmetic oracle, checks them. -/
namespace CunninghamNonconstantObjective
open FriedmannCunningham FriedmannSimplex CunninghamRewardTranslation
open scoped BigOperators

def point (changed : Bool) (j : Fin (cols 3)) : ℚ :=
  (if changed then
    match j.val with
    | 0 => 132931707866401 | 3 => 2882401 | 7 => 20176804
    | 9 => 17294403 | 12 => 8647201 | 13 => 5764801
    | 14 => 8647201 | 15 => 5764801 | 17 => 28824009
    | 19 => 25941606 | _ => 0
  else
    match j.val with
    | 0 => 132931713631201 | 4 => 2882401 | 7 => 17294404
    | 9 => 14412003 | 12 => 5764801 | 13 => 5764801
    | 14 => 5764801 | 15 => 5764801 | 17 => 28824009
    | 19 => 25941607 | _ => 0) / 2882401

theorem points_feasible : feasible (program 3) (point false) ∧
    feasible (program 3) (point true) := by
  unfold feasible
  simp only [funext_iff]
  repeat' constructor
  all_goals intro i
  all_goals fin_cases i
  all_goals try change (∑ j : Fin 20, (program 3).A _ j * point _ j) = 1
  all_goals simp only [Fin.sum_univ_succ]
  all_goals norm_num [program, coefficient, rowName, columnName, rows, cols, scale,
    epsilon, indicator, point, Fin.sum_univ_zero, Finset.sum_range_succ]
  all_goals simp only [reduceCtorEq, ↓reduceIte, false_and, Finset.filter_false,
    Finset.card_empty, Nat.cast_zero, zero_mul, add_zero, sub_zero]
  all_goals norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]

def omittedContribution (x : Fin (cols 3) → ℚ) : ℚ :=
  objective (program 3) x -
    ∑ j, displayedRewardCoefficient 3 (columnName 3 j) * x j

theorem omittedContribution_eq (x : Fin (cols 3) → ℚ) :
    omittedContribution x = (rewardG 3 1 + epsilon 3 * rewardH 3 1) *
      ∑ j, boundaryWeight (columnName 3 j) * x j :=
  program_objective_difference 3 x

theorem omittedContribution_ne :
    omittedContribution (point false) ≠ omittedContribution (point true) := by
  rw [omittedContribution_eq, omittedContribution_eq]
  change (rewardG 3 1 + epsilon 3 * rewardH 3 1) *
      (∑ j : Fin 20, boundaryWeight (columnName 3 j) * point false j) ≠
    (rewardG 3 1 + epsilon 3 * rewardH 3 1) *
      (∑ j : Fin 20, boundaryWeight (columnName 3 j) * point true j)
  simp only [Fin.sum_univ_succ]
  norm_num [rewardG, rewardH, epsilon, scale, boundaryWeight, indicator,
    columnName, point, reduceCtorEq, Fin.sum_univ_zero]
  simp only [reduceCtorEq, ↓reduceIte]
  norm_num

/-- There are two feasible points of the actual LP at which the omitted
objective contribution differs. The contribution therefore cannot be removed
as a constant on the feasible polytope. -/
theorem nonconstant_on_feasible :
    ∃ x y : Fin (cols 3) → ℚ,
      feasible (program 3) x ∧ feasible (program 3) y ∧
        omittedContribution x ≠ omittedContribution y :=
  ⟨point false, point true, points_feasible.1, points_feasible.2,
    omittedContribution_ne⟩

theorem no_constant_offset :
    ¬∃ C : ℚ, ∀ x : Fin (cols 3) → ℚ,
      feasible (program 3) x → omittedContribution x = C :=
  fun ⟨_, h⟩ => omittedContribution_ne
    ((h _ points_feasible.1).trans (h _ points_feasible.2).symm)

end CunninghamNonconstantObjective

#print axioms CunninghamNonconstantObjective.points_feasible
#print axioms CunninghamNonconstantObjective.omittedContribution_eq
#print axioms CunninghamNonconstantObjective.omittedContribution_ne
#print axioms CunninghamNonconstantObjective.nonconstant_on_feasible
#print axioms CunninghamNonconstantObjective.no_constant_offset

