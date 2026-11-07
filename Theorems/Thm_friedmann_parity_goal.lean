import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannParity

theorem exponential_deterministic :
    ExponentialLocal ∧ ExponentialGlobal ∧ FriedmannDiscounted.Exponential ∧
      FriedmannDiscounted.ExponentialMeanViaReduction ∧ FriedmannStochastic.Exponential := by
  sorry

end FriedmannParity
