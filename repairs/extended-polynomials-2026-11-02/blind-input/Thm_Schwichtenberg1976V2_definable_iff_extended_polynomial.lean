import Definitions.Def_Schwichtenberg1976V2_Lambda
namespace Schwichtenberg1976V2


theorem definable_iff_extended_polynomial
    (k : Nat) (f : (Fin k → Nat) → Nat) :
    (IsPiecewisePolynomial k f ↔ IsExtendedPolyInd f) ∧
    (IsLambdaDefinable k f ↔ IsExtendedPolyInd f) ∧
    (IsLambdaDefinable k f ↔ IsPiecewisePolynomial k f) := by
  sorry

end Schwichtenberg1976V2