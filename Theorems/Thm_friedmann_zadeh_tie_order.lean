import Definitions.Def_friedmann_zadeh

set_option autoImplicit false

namespace FriedmannZadeh

/-- Concrete completion of the partial ordering in §6.2 / Definition 7. -/
theorem tie_order (n : ℕ) (hn : 0 < n) (ctx : Context)
    (σ : Strategy n) (hσ : legal σ) (target : Node n)
    (ht : target = entryAt n 1 ∨ target = selectorAt n 0) :
    linearExtension ctx σ target (sourceRank ctx σ target) := by sorry

end FriedmannZadeh
