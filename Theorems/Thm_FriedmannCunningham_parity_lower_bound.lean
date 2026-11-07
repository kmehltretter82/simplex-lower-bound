import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 4, with the explicit Figure 2 graph and multiplicity valuations. -/
theorem parity_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → ParityState n), parityRun n hn s T ∧ 2 ^ n ≤ T := by
  sorry

end FriedmannCunningham
