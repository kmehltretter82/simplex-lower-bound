import Solutions.Sol_friedmann_parity_local
import Solutions.Sol_friedmann_parity_payoff
import Solutions.Sol_friedmann_parity_stochastic

set_option autoImplicit false

namespace FriedmannParity

theorem exponential_deterministic :
    ExponentialLocal ∧ ExponentialGlobal ∧ FriedmannDiscounted.Exponential ∧
      FriedmannDiscounted.ExponentialMeanViaReduction ∧ FriedmannStochastic.Exponential :=
  ⟨exponential_local, exponential_global, exponential_payoff.1, exponential_payoff.2,
    exponential_stochastic⟩

end FriedmannParity
