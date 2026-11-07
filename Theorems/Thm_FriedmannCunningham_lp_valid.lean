import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Construction validity needed by the §4.2 policy/BFS correspondence.
The graph-derived reward retains the aliases discussed in the source notes. -/
theorem lp_valid (n : ℕ) (hn : 3 ≤ n) :
    FriedmannSimplex.bounded (program n) ∧
    ∀ σ : Policy n,
      FriedmannSimplex.basicFeasible (program n) (policyBasis n hn σ) ∧
        ∀ i, 0 < FriedmannSimplex.basicValues (program n) (policyBasis n hn σ) i := by
  sorry

end FriedmannCunningham
