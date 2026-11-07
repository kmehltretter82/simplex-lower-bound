import Definitions.Def_friedmann_zadeh

set_option autoImplicit false

namespace FriedmannZadeh

/-- Section 5, with every count and every pivot preserved by the occupancy LP. -/
theorem lp_transfer (n N : ℕ) (ε : ℚ) (hp : Parameters n N ε)
    (s : ℕ → CounterState n) (T : ℕ) (hs : mdpRun N ε s T) :
    ∃ z : ℕ → LPState (rowCount n) (columnCount n),
      InducedSimplexRun n N ε z T ∧
      ∀ t, t ≤ T → represents (s t).strategy (z t).basis ∧
        ∀ j, (z t).count j = (s t).count (columnAt n j).val := by sorry

end FriedmannZadeh
