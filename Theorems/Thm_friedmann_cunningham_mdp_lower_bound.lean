import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 6, expressed on the equivalent decision-state MDP. -/
theorem mdp_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → MDPState n), mdpRun n hn s T ∧ 2 ^ n ≤ T := by
  sorry

end FriedmannCunningham
