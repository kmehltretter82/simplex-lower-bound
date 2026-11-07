import Definitions.Def_friedmann_zadeh

set_option autoImplicit false

namespace FriedmannZadeh

/-- Canonical-strategy enumeration, the consequence of Lemma 6 used in Thm 4. -/
theorem counter_coverage (n N : ℕ) (ε : ℚ) (hp : Parameters n N ε) :
    (∃ T s, pgRun (n := n) s T ∧ ∀ b, b < 2 ^ n →
      ∃ t, t ≤ T ∧ Canonical .parity b (s t).strategy) ∧
    (∃ T s, mdpRun (n := n) N ε s T ∧ ∀ b, b < 2 ^ n →
      ∃ t, t ≤ T ∧ Canonical .mdp b (s t).strategy) := by sorry

end FriedmannZadeh
