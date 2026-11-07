import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

open scoped BigOperators

/-- Figure 7 and Lemma 8, after eliminating the random vertices: each action's
transition row is substochastic and every policy's transient matrix is invertible. -/
theorem mdp_valid (n : ℕ) (hn : 3 ≤ n) :
    (∀ r b q, 0 ≤ transition n hn r b q) ∧
    (∀ r b, (∑ q : Fin (rows n), transition n hn r b q) ≤ 1) ∧
    (∀ σ : Policy n,
      (FriedmannSimplex.basisMatrix (program n) (policyBasis n hn σ)).det ≠ 0) := by
  sorry

end FriedmannCunningham
