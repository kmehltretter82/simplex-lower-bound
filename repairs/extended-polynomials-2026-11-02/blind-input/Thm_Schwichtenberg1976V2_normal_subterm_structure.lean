import Definitions.Def_Schwichtenberg1976V2_Lambda
namespace Schwichtenberg1976V2


theorem normal_subterm_structure
    (Fs : List Var) (α : Var) (r : Term)
    (hFs : ∀ F ∈ Fs, F.ty = Ty.nu)
    (hα : α.ty = Ty.endo)
    (hr_ty : HasType r Ty.endo)
    (hr_norm : IsBetaNormal r)
    (hr_fv : ∀ v ∈ freeVars r, v ∈ Fs ∨ v = α) :
    (∀ s τ, IsSubterm s r → HasType s τ → τ = .zero ∨ τ = Ty.endo ∨ τ = Ty.nu) ∧
    (∀ s, IsSubterm s r → HasType s Ty.nu → ∃ F ∈ Fs, s = .var F) ∧
    (∀ s, IsSubterm s r → HasType s Ty.endo → IsType00Subterm Fs α s) := by
  sorry

end Schwichtenberg1976V2