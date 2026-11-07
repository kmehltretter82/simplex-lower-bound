import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 7: the graph-derived LP, the prescribed order and initial basis,
at least 2^n pivots, and strict objective increase on every pivot. -/
theorem simplex_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → FriedmannSimplex.State (rows n) (cols n)),
      s 0 = initialState n hn ∧
      FriedmannSimplex.cunninghamRun (program n) (order n) s T ∧
      2 ^ n ≤ T ∧
      ∀ t, t < T →
        FriedmannSimplex.basicObjective (program n) (s t).basis <
          FriedmannSimplex.basicObjective (program n) (s (t + 1)).basis := by
  sorry

end FriedmannCunningham
