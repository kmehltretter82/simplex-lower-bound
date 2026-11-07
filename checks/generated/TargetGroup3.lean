import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannDiscounted

theorem discounted_bellman {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V) :
    (∀ v, playValue G σ τ v = G.reward v + G.discount *
      playValue G σ τ (if G.arena.owner v = false then σ v else τ v)) ∧
    ∀ x : V → ℚ,
      (∀ v, x v = G.reward v + G.discount *
        x (if G.arena.owner v = false then σ v else τ v)) → x = playValue G σ τ := by
  sorry

end FriedmannDiscounted


namespace FriedmannParity

theorem exponential_deterministic :
    ExponentialLocal ∧ ExponentialGlobal ∧ FriedmannDiscounted.Exponential ∧
      FriedmannDiscounted.ExponentialMeanViaReduction ∧ FriedmannStochastic.Exponential := by
  sorry

end FriedmannParity


namespace FriedmannParity

theorem exponential_payoff : FriedmannDiscounted.Exponential ∧
    FriedmannDiscounted.ExponentialMeanViaReduction := by
  sorry

end FriedmannParity


namespace FriedmannParity

theorem exponential_stochastic : FriedmannStochastic.Exponential := by
  sorry

end FriedmannParity


namespace FriedmannStochastic

theorem absorption_values {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (hσ : Legal G 0 σ) (hτ : Legal G 1 τ) :
    (1 - transition G σ τ).det ≠ 0 ∧
    playValue G σ τ G.win = 1 ∧ playValue G σ τ G.lose = 0 ∧
    (∀ v, 0 ≤ playValue G σ τ v ∧ playValue G σ τ v ≤ 1) ∧
    (∀ v, v ≠ G.win → v ≠ G.lose →
      playValue G σ τ v = ∑ w, transition G σ τ v w * playValue G σ τ w) := by
  sorry

end FriedmannStochastic


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
