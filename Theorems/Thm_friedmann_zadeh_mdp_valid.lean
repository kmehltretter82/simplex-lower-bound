import Definitions.Def_friedmann_zadeh

set_option autoImplicit false

namespace FriedmannZadeh

/-- Transition-probability and initial-policy obligations for §4 / Lemma 1. -/
theorem mdp_valid (n N : ℕ) (ε : ℚ) (hp : Parameters n N ε) :
    legal (initial (n := n)) ∧ proper ε (initial (n := n)) ∧
    ∀ σ : Strategy n, legal σ → ∀ v,
      (∀ w, 0 ≤ transition ε σ v w) ∧ ∑ w, transition ε σ v w = 1 := by sorry

end FriedmannZadeh
