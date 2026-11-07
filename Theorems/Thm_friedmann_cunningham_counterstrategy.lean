import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Lemma 1 on the explicit repeated-priority family. A single legal opponent
strategy minimizes the multiplicity valuation from every starting vertex. -/
theorem counterstrategy (n : ℕ) (hn : 3 ≤ n)
    (σ : Fin (vertices n) → Fin (vertices n))
    (hσ : FriedmannParity.Legal (parityGame n) false σ) :
    ∃ τ : Fin (vertices n) → Fin (vertices n),
      FriedmannParity.Legal (parityGame n) true τ ∧
      ∀ v τ', FriedmannParity.Legal (parityGame n) true τ' →
        FriedmannMultiplicity.ValueLE (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ τ v)
          (FriedmannParity.playValue (parityGame n) σ τ' v) := by
  sorry

end FriedmannCunningham
