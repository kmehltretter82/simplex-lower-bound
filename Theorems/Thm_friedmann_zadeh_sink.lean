import Definitions.Def_friedmann_zadeh

set_option autoImplicit false

namespace FriedmannZadeh

/-- Lemma 1, parity part, with a common minimizing counterstrategy. -/
theorem sink (n : ℕ) (hn : 0 < n) (σ : Strategy n) (hσ : PgReachable σ) :
    ∃ τ, PgCounterstrategy σ τ ∧ ∀ v, ∃ t : ℕ,
      ∀ k, t ≤ k → FriedmannParity.play (parityGame n) σ τ v k = .sink := by sorry

end FriedmannZadeh
