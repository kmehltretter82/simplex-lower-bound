import Definitions.Def_friedmann_parity

set_option autoImplicit false

namespace FriedmannParity

theorem counterstrategy_exists {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V) (hσ : Legal G false σ) :
    ∃ τ, OptimalCounterstrategy G σ τ ∧ ∀ v, value G σ v = playValue G σ τ v := by
  sorry

end FriedmannParity
