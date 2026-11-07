import Definitions.Def_friedmann_zadeh

set_option autoImplicit false

namespace FriedmannZadeh

/-- Radix realization of the standard priority-multiplicity valuation order.
Source: Avis--Friedmann, §2.2, used for the repeated-priority counter here. -/
theorem valuation (n : ℕ) (hn : 0 < n) (σ τ ρ υ : Strategy n)
    (v w : Node n) :
    (pgPlayScore σ τ v < pgPlayScore ρ υ w) ↔
      countValueLT (FriedmannParity.playValue (parityGame n) σ τ v)
        (FriedmannParity.playValue (parityGame n) ρ υ w) := by sorry

end FriedmannZadeh
