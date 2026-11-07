import Definitions.Def_friedmann_parity

set_option autoImplicit false

namespace FriedmannParity

theorem nonimprovable_solves {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V)
    (hσ : Legal G false σ) (hstop : ¬ Improvable G σ) :
    (WinningRegion G false = {v | (value G σ v).cyclePriority % 2 = 0}) ∧
    (WinningRegion G true = {v | (value G σ v).cyclePriority % 2 = 1}) ∧
    (∀ v, (value G σ v).cyclePriority % 2 = 0 → Wins G false σ v) ∧
    (∀ τ, OptimalCounterstrategy G σ τ →
      ∀ v, (value G σ v).cyclePriority % 2 = 1 → Wins G true τ v) ∧
    (∀ ρ, Legal G false ρ → ∀ v, ValueLE G (value G ρ v) (value G σ v)) := by
  sorry

end FriedmannParity
