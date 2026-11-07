import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

open scoped BigOperators

/-- The §4.2–4.3 correspondence, including Lemma 11's objective identity. -/
theorem policy_pivot (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    FriedmannSimplex.basicObjective (program n) (policyBasis n hn σ) =
      (∑ r : Fin (rows n), policyValue n hn σ r) ∧
    ∀ r,
      (mdpImproving n hn σ r ↔
        FriedmannSimplex.improving (program n) (policyBasis n hn σ)
          (actionColumn n hn r (!σ r))) ∧
      (mdpImproving n hn σ r →
        FriedmannSimplex.pivot (program n) (policyBasis n hn σ)
          (actionColumn n hn r (!σ r))
          (policyBasis n hn (Function.update σ r (!σ r)))) := by
  sorry

end FriedmannCunningham
