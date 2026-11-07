import Solutions.Sol_friedmann_parity_binary

set_option autoImplicit false

namespace FriedmannParity

theorem exponential_local : ExponentialLocal := by
  rcases exponential_binary with ⟨C, hC, hExp⟩
  refine ⟨C, hC, fun n hn => ?_⟩
  rcases hExp false n hn with ⟨N, G, ι, _, hedge, hprio, hhard⟩
  exact ⟨N, G, ι, hedge, hprio, hhard⟩

theorem exponential_global : ExponentialGlobal := by
  rcases exponential_binary with ⟨C, hC, hExp⟩
  refine ⟨C, hC, fun n hn => ?_⟩
  rcases hExp true n hn with ⟨N, G, ι, _, hedge, hprio, hhard⟩
  exact ⟨N, G, ι, hedge, hprio, hhard⟩

end FriedmannParity
