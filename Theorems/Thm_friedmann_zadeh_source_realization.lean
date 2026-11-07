import Definitions.Def_friedmann_zadeh

set_option autoImplicit false

namespace FriedmannZadeh

/-- Agreement of the implemented valuation-defined transition direction with
the source's phase-defined direction, on an entire canonical enumeration.
Both the execution and the partition into source transitions are conclusions.
-/
theorem source_realization (n N : ℕ) (ε : ℚ) (hp : Parameters n N ε) :
    ∀ ctx : Context, ∃ T, ∃ s : ℕ → CounterState n, ∃ cut : ℕ → ℕ,
      (if ctx = .parity then pgRun s T else mdpRun N ε s T) ∧
      cut 0 = 0 ∧
      (∀ b, b < 2 ^ n → cut b ≤ T ∧ Canonical ctx b (s (cut b)).strategy) ∧
      (∀ b, b + 1 < 2 ^ n → cut b < cut (b+1) ∧ ∀ t,
        cut b ≤ t → t < cut (b+1) →
          sourceStep ctx b N ε (s t) (s (t+1))) := by sorry

end FriedmannZadeh
