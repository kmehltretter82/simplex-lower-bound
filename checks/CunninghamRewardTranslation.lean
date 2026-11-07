import Definitions.Def_friedmann_cunningham
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Audit certificate for elimination of the bottom random gadget in the
Avis--Friedmann construction.  This file imports definitions only, never the
open lower-bound theorem targets.  Its equations model Figure 7 together with
the boundary transition shown in Figure 8 of the accepted manuscript.

The certificate proves algebraic preservation of the local Bellman equations
and agreement with the actual LP objective coefficients.  It does not prove
the lower bound, nor turn the human reading of a diagram into a kernel fact.
-/

namespace CunninghamRewardTranslation

open FriedmannCunningham
open scoped BigOperators

/-- Values at the three eliminated vertices, before any collapse. -/
structure BottomValues where
  g : ℚ
  f : ℚ
  h : ℚ

/-- The graph gives `g → F`, `F → h` with probability `ε`, `F → e`
with probability `1-ε`, and `h → a`. Rewards occur on `g → F` and `h → a`.
`a` and `e` are continuation values at the retained decision vertices.
These three equations are independent of the collapsed LP coefficients. -/
def BottomEquations (rg rh ε a e : ℚ) (v : BottomValues) : Prop :=
  v.g = rg + v.f ∧
  v.f = ε * v.h + (1 - ε) * e ∧
  v.h = rh + a

/-- Eliminating the two downstream intermediate values preserves exactly
the expected reward and the two continuation probabilities. -/
theorem eliminate_bottom (rg rh ε a e : ℚ) (v : BottomValues)
    (hv : BottomEquations rg rh ε a e v) :
    v.g = (rg + ε * rh) + ε * a + (1 - ε) * e := by
  rw [hv.1, hv.2.1, hv.2.2]
  ring

/-- A solution of the expanded equations exists for every pair of continuation
values; the preceding implication is not based on inconsistent hypotheses. -/
def expandBottom (rg rh ε a e : ℚ) : BottomValues where
  g := rg + (ε * (rh + a) + (1 - ε) * e)
  f := ε * (rh + a) + (1 - ε) * e
  h := rh + a

theorem expandBottom_valid (rg rh ε a e : ℚ) :
    BottomEquations rg rh ε a e (expandBottom rg rh ε a e) :=
  ⟨rfl, rfl, rfl⟩

theorem expandBottom_value (rg rh ε a e : ℚ) :
    (expandBottom rg rh ε a e).g =
      (rg + ε * rh) + ε * a + (1 - ε) * e :=
  eliminate_bottom rg rh ε a e _ (expandBottom_valid rg rh ε a e)

/-- All three named incoming actions carry the reward of the eliminated
bottom gadget in the actual mission definition, for every size parameter. -/
theorem boundary_objective_coefficients (n : ℕ) :
    objectiveCoefficient n ⟨.b, 2, false⟩ = rewardG n 1 + epsilon n * rewardH n 1 ∧
    objectiveCoefficient n ⟨.c, 2, false⟩ = rewardG n 1 + epsilon n * rewardH n 1 ∧
    objectiveCoefficient n ⟨.d, 2, false⟩ = rewardG n 1 + epsilon n * rewardH n 1 := by
  simp [objectiveCoefficient, indicator]

/-- The same incoming actions send `ε` flow to `a₂` and `1-ε` to `e₁`.
Conservation matrix entries are the negative incoming probabilities. -/
theorem boundary_conservation_entries (n : ℕ) :
    coefficient n (.a, 2) ⟨.b, 2, false⟩ = -epsilon n ∧
    coefficient n (.a, 2) ⟨.c, 2, false⟩ = -epsilon n ∧
    coefficient n (.a, 2) ⟨.d, 2, false⟩ = -epsilon n ∧
    coefficient n (.e, 1) ⟨.b, 2, false⟩ = -(1 - epsilon n) ∧
    coefficient n (.e, 1) ⟨.c, 2, false⟩ = -(1 - epsilon n) ∧
    coefficient n (.e, 1) ⟨.d, 2, false⟩ = -(1 - epsilon n) := by
  simp [coefficient, indicator]

/-- The central source-to-code certificate: for each of the three incoming
actions, the expanded graph value is exactly the Bellman right-hand side
using the mission's actual objective and conservation matrix coefficients. -/
theorem bottom_graph_matches_boundary_action (n : ℕ) (k : Kind)
    (hk : k = .b ∨ k = .c ∨ k = .d) (a e : ℚ) (v : BottomValues)
    (hv : BottomEquations (rewardG n 1) (rewardH n 1) (epsilon n) a e v) :
    v.g = objectiveCoefficient n ⟨k, 2, false⟩ -
      coefficient n (.a, 2) ⟨k, 2, false⟩ * a -
      coefficient n (.e, 1) ⟨k, 2, false⟩ * e := by
  rcases hk with rfl | rfl | rfl
  all_goals simpa [objectiveCoefficient, coefficient, indicator, -neg_sub] using
    eliminate_bottom (rewardG n 1) (rewardH n 1) (epsilon n) a e v hv

/-- The reward-based reading of the displayed objective, before the three
incoming bottom-gadget contributions are inserted.  This is deliberately
named "displayedReward": the paper writes priority notation in that formula,
so it is not a claim that this is a completely literal transcription. -/
def displayedRewardCoefficient (n : ℕ) (v : Name) : ℚ :=
  match v.kind, v.one with
  | .a, true | .b, true | .c, true => rewardG n v.level + epsilon n * rewardH n v.level
  | .d, true | .e, true => epsilon n * rewardH n v.level
  | .e, false => 1
  | _, _ => 0

def boundaryWeight (v : Name) : ℚ :=
  indicator v .b 2 false + indicator v .c 2 false + indicator v .d 2 false

theorem coefficient_difference (n : ℕ) (v : Name) :
    objectiveCoefficient n v = displayedRewardCoefficient n v +
      (rewardG n 1 + epsilon n * rewardH n 1) * boundaryWeight v := rfl

/-- For any finite collection of actions and any flow assignment, the total
objective difference is exactly the omitted expected reward times the total
flow through the three incoming actions. No feasibility or asymptotic claim
is assumed or concluded. -/
theorem objective_difference {α : Type*} [Fintype α]
    (n : ℕ) (name : α → Name) (flow : α → ℚ) :
    (∑ j, objectiveCoefficient n (name j) * flow j) -
      (∑ j, displayedRewardCoefficient n (name j) * flow j) =
      (rewardG n 1 + epsilon n * rewardH n 1) *
        ∑ j, boundaryWeight (name j) * flow j := by
  simp_rw [coefficient_difference, add_mul]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, add_sub_cancel_left]

theorem program_objective_difference (n : ℕ) (flow : Fin (cols n) → ℚ) :
    (∑ j, (program n).c j * flow j) -
      (∑ j, displayedRewardCoefficient n (columnName n j) * flow j) =
      (rewardG n 1 + epsilon n * rewardH n 1) *
        ∑ j, boundaryWeight (columnName n j) * flow j :=
  objective_difference n (columnName n) flow

/-- Interior levels split the remaining probability equally between two
retained decision vertices. This is distinct from the boundary equation. -/
def InteriorEquations (rg rh ε a d e : ℚ) (v : BottomValues) : Prop :=
  v.g = rg + v.f ∧
  v.f = ε * v.h + ((1 - ε) / 2) * d + ((1 - ε) / 2) * e ∧
  v.h = rh + a

theorem eliminate_interior (rg rh ε a d e : ℚ) (v : BottomValues)
    (hv : InteriorEquations rg rh ε a d e v) :
    v.g = (rg + ε * rh) + ε * a +
      ((1 - ε) / 2) * d + ((1 - ε) / 2) * e := by
  rw [hv.1, hv.2.1, hv.2.2]
  ring

/-- The first switch out of the all-zero policy has advantage `N-1` when
the zero-action continuation from `e₁` has value `1+g₁`. This conditional
algebraic fact does not assert that every policy is absorbing. -/
theorem first_switch_advantage (N ε a e : ℚ) (v : BottomValues)
    (hv : BottomEquations (-N) (N ^ 2) ε a e v)
    (he : e = 1 + v.g) : v.f - e = N - 1 := by
  rw [he, hv.1]
  ring

end CunninghamRewardTranslation

#print axioms CunninghamRewardTranslation.eliminate_bottom
#print axioms CunninghamRewardTranslation.expandBottom_valid
#print axioms CunninghamRewardTranslation.expandBottom_value
#print axioms CunninghamRewardTranslation.boundary_objective_coefficients
#print axioms CunninghamRewardTranslation.boundary_conservation_entries
#print axioms CunninghamRewardTranslation.bottom_graph_matches_boundary_action
#print axioms CunninghamRewardTranslation.coefficient_difference
#print axioms CunninghamRewardTranslation.objective_difference
#print axioms CunninghamRewardTranslation.program_objective_difference
#print axioms CunninghamRewardTranslation.eliminate_interior
#print axioms CunninghamRewardTranslation.first_switch_advantage
