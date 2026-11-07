import Definitions.Def_friedmann_parity

set_option autoImplicit false

namespace FriedmannParity

theorem improvement_strict {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ σ' : V → V)
    (hσ : Legal G false σ) (hi : Improvable G σ) (hs : Improvement G σ σ') :
    (∀ v, ValueLE G (value G σ v) (value G σ' v)) ∧
    ∃ v, ValueLT G (value G σ v) (value G σ' v) := by
  sorry

end FriedmannParity
