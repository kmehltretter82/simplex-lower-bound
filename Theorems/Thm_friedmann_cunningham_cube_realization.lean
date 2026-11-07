import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Lemma 12: an actual polytope realization, with an objective that orients
every cube edge and retains the original strict improvements. -/
theorem cube_realization (n : ℕ) (hn : 3 ≤ n) :
    realizesCube n hn ∧
    ∃ c : Fin (cols n) → ℚ, isAUSO n hn c ∧
      ∀ σ τ, cubeOrientation n hn (program n).c σ τ → cubeOrientation n hn c σ τ := by
  sorry

end FriedmannCunningham
