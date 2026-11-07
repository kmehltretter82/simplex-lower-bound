import Definitions.Def_Schwichtenberg1976V2_Lambda
namespace Schwichtenberg1976V2


theorem subterm_polynomial_lemma
    (k : Nat) (Fs : Fin k → Var) (α : Var)
    (hFs_ty : ∀ i : Fin k, (Fs i).ty = Ty.nu)
    (hFs_inj : Function.Injective Fs)
    (hα_ty : α.ty = Ty.endo)
    (s : Term)
    (hs : IsType00Subterm (List.ofFn Fs) α s) :
    s = .var α ∨
    ∃ (P : (Fin k → Nat) → Nat) (z : Var),
      IsPolynomial P ∧
      z.ty = .zero ∧
      ∀ v : Fin k → Nat,
        (∀ i : Fin k, v i ≠ 0) →
        ∃ y : Var,
          y.ty = .zero ∧
          (z = y ∨ z ∈ freeVars s) ∧
          ReducesTo
            (substMany s ((List.finRange k).map (fun i => (Fs i, churchNumeral (v i)))))
            (.lam y (iterApp (.var α) (.var z) (P v))) := by
  sorry

end Schwichtenberg1976V2