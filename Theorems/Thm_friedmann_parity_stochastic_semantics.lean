import Definitions.Def_friedmann_payoff

set_option autoImplicit false

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
