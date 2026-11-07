import Definitions.Def_friedmann_zadeh

set_option autoImplicit false

namespace FriedmannZadeh

/-- Table 1 and the explicit deterministic-vertex occupancy representation. -/
theorem size (n : ℕ) (hn : 0 < n) :
    Fintype.card (Node n) = 16 * n - 6 ∧
    rowCount n = 14 * n - 6 ∧ columnCount n = 26 * n - 12 := by sorry

end FriedmannZadeh
