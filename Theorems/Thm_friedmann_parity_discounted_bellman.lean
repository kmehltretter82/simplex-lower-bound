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
