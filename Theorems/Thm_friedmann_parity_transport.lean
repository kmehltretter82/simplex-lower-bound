import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannParity

theorem sink_discounted_order {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (ι : V → V) (sink : V) (hSink : IsSinkGame G ι sink)
    (σ : V → V) (hσ : Legal G false σ)
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) (v w : V) :
    ValueLT G (value G σ v) (value G σ w) ↔
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v <
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ w := by
  sorry

end FriedmannParity
