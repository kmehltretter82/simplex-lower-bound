import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 8: a realizable AUSO of dimension 5(n−1), with both signed
directions ordered as in (1), and a complete walk of length at least 2^n. -/
theorem auso_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    realizesCube n hn ∧
    ∃ (c : Fin (cols n) → ℚ) (T : ℕ) (s : ℕ → MDPState n),
      isAUSO n hn c ∧
      (∀ σ τ, cubeOrientation n hn (program n).c σ τ → cubeOrientation n hn c σ τ) ∧
      cubeRun n hn c s T ∧ 2 ^ n ≤ T := by
  sorry

end FriedmannCunningham
