import Std



namespace Schwichtenberg1976V2


inductive Ty where
  | zero : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty


def endo : Ty := .arr .zero .zero


def nu : Ty := .arr endo endo


def nuArity : Nat → Ty
  | 0 => nu
  | k + 1 => .arr nu (nuArity k)

end Ty


structure Var where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr


inductive Term where
  | var : Var → Term
  | app : Term → Term → Term
  | lam : Var → Term → Term
  deriving DecidableEq, Repr

namespace Term


def appMany : Term → List Term → Term
  | t, [] => t
  | t, s :: ss => appMany (.app t s) ss


def lamMany : List Var → Term → Term
  | [], t => t
  | x :: xs, t => .lam x (lamMany xs t)

end Term


inductive HasType : Term → Ty → Prop where
  | var (x : Var) :
      HasType (.var x) x.ty
  | app {t s : Term} {σ τ : Ty} :
      HasType t (.arr σ τ) →
      HasType s σ →
      HasType (.app t s) τ
  | lam (x : Var) {t : Term} {τ : Ty} :
      HasType t τ →
      HasType (.lam x t) (.arr x.ty τ)


def freeVarOccurrences : Term → List Var
  | .var x => [x]
  | .app t s => freeVarOccurrences t ++ freeVarOccurrences s
  | .lam x t => (freeVarOccurrences t).filter (· != x)


def freeVars (t : Term) : List Var :=
  (freeVarOccurrences t).eraseDups


def allVars : Term → List Var
  | .var x => [x]
  | .app t s => allVars t ++ allVars s
  | .lam x t => x :: allVars t


def IsClosed (t : Term) : Prop :=
  freeVars t = []


def maxVarId : Term → Nat
  | .var x => x.id
  | .app t s => Nat.max (maxVarId t) (maxVarId s)
  | .lam x t => Nat.max x.id (maxVarId t)


def freshVarFor (τ : Ty) (preferred : Nat) (t : Term) : Var :=
  let candidate : Var := ⟨preferred, τ⟩
  if candidate ∈ freeVarOccurrences t then ⟨maxVarId t + 1, τ⟩ else candidate


def renameFreeVar (t : Term) (x y : Var) : Term :=
  match t with
  | .var v => if v == x then .var y else .var v
  | .app r s => .app (renameFreeVar r x y) (renameFreeVar s x y)
  | .lam v body =>
      if v == x then .lam v body else .lam v (renameFreeVar body x y)


def rawSize : Term → Nat
  | .var _ => 1
  | .app t s => rawSize t + rawSize s + 1
  | .lam _ t => rawSize t + 1

theorem renameFreeVar_rawSize (t : Term) (x y : Var) :
    rawSize (renameFreeVar t x y) = rawSize t := by
  induction t with
  | var v => simp only [renameFreeVar]; split <;> rfl
  | app r s ihr ihs => simp [renameFreeVar, rawSize, ihr, ihs]
  | lam v body ih =>
      simp only [renameFreeVar]
      split
      · rfl
      · simp [rawSize, ih]


def substTerm (t : Term) (x : Var) (s : Term) : Term :=
  match t with
  | .var v => if v == x then s else .var v
  | .app r u => .app (substTerm r x s) (substTerm u x s)
  | .lam v body =>
      if v == x then
        .lam v body
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarId body) (Nat.max (maxVarId s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .lam v' (substTerm (renameFreeVar body v v') x s)
      else
        .lam v (substTerm body x s)
termination_by rawSize t
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega


def substMany : Term → List (Var × Term) → Term
  | t, [] => t
  | t, (x, s) :: rest => substMany (substTerm t x s) rest


inductive AlphaEq : Term → Term → Prop where
  | refl (t : Term) : AlphaEq t t
  | symm {t s : Term} : AlphaEq t s → AlphaEq s t
  | trans {t s u : Term} : AlphaEq t s → AlphaEq s u → AlphaEq t u
  | app {t t' s s' : Term} :
      AlphaEq t t' → AlphaEq s s' → AlphaEq (.app t s) (.app t' s')
  | lam_rename (x y : Var) (t : Term) :
      x.ty = y.ty →
      (y = x ∨ y ∉ allVars t) →
      AlphaEq (.lam x t) (.lam y (renameFreeVar t x y))
  | lam_congr (x : Var) {t s : Term} :
      AlphaEq t s → AlphaEq (.lam x t) (.lam x s)


inductive ReducesTo : Term → Term → Prop where
  | beta (x : Var) (t s : Term) :
      ReducesTo (.app (.lam x t) s) (substTerm t x s)
  | app {t t' s s' : Term} :
      ReducesTo t t' → ReducesTo s s' → ReducesTo (.app t s) (.app t' s')
  | lam (x : Var) {t t' : Term} :
      ReducesTo t t' → ReducesTo (.lam x t) (.lam x t')
  | refl_alpha {t t' : Term} :
      AlphaEq t t' → ReducesTo t t'
  | trans {t t' t'' : Term} :
      ReducesTo t t' → ReducesTo t' t'' → ReducesTo t t''


def hasBetaRedex : Term → Bool
  | .var _ => false
  | .app (.lam _ _) _ => true
  | .app t s => hasBetaRedex t || hasBetaRedex s
  | .lam _ t => hasBetaRedex t


def IsBetaNormal (t : Term) : Prop :=
  hasBetaRedex t = false


inductive IsSubterm : Term → Term → Prop where
  | refl (t : Term) : IsSubterm t t
  | appLeft {s t u : Term} : IsSubterm s t → IsSubterm s (.app t u)
  | appRight {s t u : Term} : IsSubterm s u → IsSubterm s (.app t u)
  | lamBody {s t : Term} (x : Var) : IsSubterm s t → IsSubterm s (.lam x t)


def TermEq (t s : Term) : Prop :=
  ∃ u v : Term,
    IsBetaNormal u ∧ IsBetaNormal v ∧
    ReducesTo t u ∧ ReducesTo s v ∧ AlphaEq u v


def iterApp (α base : Term) : Nat → Term
  | 0 => base
  | n + 1 => .app α (iterApp α base n)


def iterTerm (α : Term) (xId : Nat := 0) (n : Nat) : Term :=
  let x := freshVarFor .zero xId α
  .lam x (iterApp α (.var x) n)


def churchNumeral (n : Nat) : Term :=
  let α : Var := ⟨1, Ty.endo⟩
  let x : Var := ⟨0, .zero⟩
  .lam α (.lam x (iterApp (.var α) (.var x) n))


def compTerm (τ : Ty) (t s : Term) (xId : Nat := 2) : Term :=
  let x := freshVarFor τ xId (.app t s)
  .lam x (.app t (.app s (.var x)))


def addComb : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let G : Var := ⟨4, Ty.nu⟩
  let α : Var := ⟨1, Ty.endo⟩
  .lam F (.lam G (.lam α (compTerm .zero (.app (.var F) (.var α)) (.app (.var G) (.var α)) 0)))


def mulComb : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let G : Var := ⟨4, Ty.nu⟩
  .lam F (.lam G (compTerm Ty.endo (.var F) (.var G) 1))


def constComb (k : Nat) : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let α : Var := ⟨1, Ty.endo⟩
  .lam F (.lam α (iterTerm (.var α) 0 k))


def condComb : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let G : Var := ⟨4, Ty.nu⟩
  let H : Var := ⟨5, Ty.nu⟩
  let α : Var := ⟨1, Ty.endo⟩
  let x : Var := ⟨0, .zero⟩
  let y : Var := ⟨2, .zero⟩
  .lam F (.lam G (.lam H (.lam α (.lam x
    (.app
      (.app (.var H) (.lam y (.app (.app (.var G) (.var α)) (.var x))))
      (.app (.app (.var F) (.var α)) (.var x)))))))


def condNat (n m i : Nat) : Nat :=
  if i == 0 then n else m


def numeralArgs : (k : Nat) → (Fin k → Nat) → List Term
  | 0, _ => []
  | k + 1, v =>
      churchNumeral (v ⟨0, Nat.zero_lt_succ k⟩) ::
        numeralArgs k (fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)


def DefinesFunction (k : Nat) (t : Term) (f : (Fin k → Nat) → Nat) : Prop :=
  HasType t (Ty.nuArity k) ∧
  IsClosed t ∧
  ∀ v : Fin k → Nat,
    ReducesTo (Term.appMany t (numeralArgs k v)) (churchNumeral (f v))


def IsLambdaDefinable (k : Nat) (f : (Fin k → Nat) → Nat) : Prop :=
  ∃ t : Term, DefinesFunction k t f


inductive IsPolynomial : {k : Nat} → ((Fin k → Nat) → Nat) → Prop where
  | const {k : Nat} (c : Nat) :
      IsPolynomial (k := k) (fun _ => c)
  | proj {k : Nat} (i : Fin k) :
      IsPolynomial (k := k) (fun v => v i)
  | add {k : Nat} {P Q : (Fin k → Nat) → Nat} :
      IsPolynomial P → IsPolynomial Q →
      IsPolynomial (k := k) (fun v => P v + Q v)
  | mul {k : Nat} {P Q : (Fin k → Nat) → Nat} :
      IsPolynomial P → IsPolynomial Q →
      IsPolynomial (k := k) (fun v => P v * Q v)


inductive IsExtendedPolyInd : {k : Nat} → ((Fin k → Nat) → Nat) → Prop where
  | const {k : Nat} (c : Nat) :
      IsExtendedPolyInd (k := k) (fun _ => c)
  | proj {k : Nat} (i : Fin k) :
      IsExtendedPolyInd (k := k) (fun v => v i)
  | add {k : Nat} {f g : (Fin k → Nat) → Nat} :
      IsExtendedPolyInd f → IsExtendedPolyInd g →
      IsExtendedPolyInd (k := k) (fun v => f v + g v)
  | mul {k : Nat} {f g : (Fin k → Nat) → Nat} :
      IsExtendedPolyInd f → IsExtendedPolyInd g →
      IsExtendedPolyInd (k := k) (fun v => f v * g v)
  | cond {k : Nat} {f g h : (Fin k → Nat) → Nat} :
      IsExtendedPolyInd f → IsExtendedPolyInd g → IsExtendedPolyInd h →
      IsExtendedPolyInd (k := k) (fun v => condNat (f v) (g v) (h v))
  | comp {k m : Nat} {g : (Fin m → Nat) → Nat} {hs : Fin m → (Fin k → Nat) → Nat} :
      IsExtendedPolyInd g →
      (∀ j : Fin m, IsExtendedPolyInd (hs j)) →
      IsExtendedPolyInd (k := k) (fun v => g (fun j => hs j v))


def IsPiecewisePolynomial (k : Nat) (f : (Fin k → Nat) → Nat) : Prop :=
  ∀ σ : Fin k → Bool,
    ∃ P : (Fin k → Nat) → Nat,
      IsPolynomial P ∧
      ∀ v : Fin k → Nat, (∀ i : Fin k, (v i != 0) = σ i) → f v = P v

mutual
  
  inductive IsBasicType00 (Fs : List Var) (α : Var) : Term → Prop where
    | alpha :
        IsBasicType00 Fs α (.var α)
    | appF {F : Var} {s : Term} :
        F ∈ Fs →
        IsType00Subterm Fs α s →
        IsBasicType00 Fs α (.app (.var F) s)

  
  inductive IsBasicType00Chain (Fs : List Var) (α : Var) : Var → Term → Prop where
    | base (z : Var) :
        z.ty = .zero →
        IsBasicType00Chain Fs α z (.var z)
    | step {z : Var} {s₁ body : Term} :
        IsBasicType00 Fs α s₁ →
        IsBasicType00Chain Fs α z body →
        IsBasicType00Chain Fs α z (.app s₁ body)

  
  inductive IsType00Subterm (Fs : List Var) (α : Var) : Term → Prop where
    | basic {s : Term} :
        IsBasicType00 Fs α s →
        IsType00Subterm Fs α s
    | chainLam (y z : Var) {body : Term} :
        y.ty = .zero →
        z.ty = .zero →
        IsBasicType00Chain Fs α z body →
        IsType00Subterm Fs α (.lam y body)
end

end Schwichtenberg1976V2
