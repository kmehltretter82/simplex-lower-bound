import Std

/-!
# Term system for non-size-increasing polynomial-time computation (ABHS 2004, Section 2)

Source: Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg,
"An arithmetic for non-size-increasing polynomial-time computation",
*Theoretical Computer Science* 318(1–2), 2004, pp. 3–27, Section 2 (pp. 3–9).

This module formalizes:
- Definition 2.1: Finite linear types (`Ty`) and Remark 2.3 abbreviations (`B`, `N`, `Bin`).
- Definition 2.2: Set model carrier `SetModel` (`S^ρ`).
- Definition 2.4 & 2.5: Raw terms (`Term`) and typed constants (`Const`).
- Definition 2.6: Linear typing judgment `HasType` (`r^ρ`) and weak typing `WeaklyTyped`
  (Section 3.1, p. 10).
- Definition 2.8, 2.9, 2.10: Lists (`listEntryCount`, `IsListTerm`), conversions (`ConvStep`),
  one-step reduction (`RedStep`), multi-step reduction (`RedStar`, `RedSteps`), and normal
  forms (`IsNormal`).
- Definition 2.12 & Proposition 2.13: Almost closed terms (`IsAlmostClosed`) and canonical
  normal forms (`HasCanonicalNormalForm`).
- Definition 2.14, 2.15, 2.16: Projections `pi0`, `pi1` and pairing helpers.
- Definition 2.17 & 2.20: List bound `#_n(r)` (`hashBound`), polynomial step measure
  `ϑ_n(r)` (`theta`), bounded-free-variable reduction `RedStepBounded` (`r →_n r'`),
  iteration nesting depth (`iterNesting`), and syntactical length (`termLength`).
- Definition 2.24: Data types (`IsDataType`), data objects (`IsDataObject`), and
  non-size-increasing polynomial-time computability on data objects.
-/

namespace ABHS2004

/-- Definition 2.1 (Finite linear types, p. 3):
`ρ, σ ::= U | ⋄ | L(ρ) | ρ ⊸ σ | ρ ⊗ σ | ρ × σ | ρ + σ`. -/
inductive Ty where
  | unit : Ty
  | diamond : Ty
  | list : Ty → Ty
  | lolli : Ty → Ty → Ty
  | tensor : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Remark 2.3 (p. 3): Booleans `B := U + U`. -/
def bool : Ty := .sum .unit .unit

/-- Remark 2.3 (p. 3): Unary natural numbers `N := L(U)`. -/
def nat : Ty := .list .unit

/-- Remark 2.3 (p. 3): Binary natural numbers `Bin := L(B)`. -/
def bin : Ty := .list bool

/-- Iterated linear function type `ρ₁ ⊸ ⋯ ⊸ ρₙ ⊸ τ`. -/
def lolliMany : List Ty → Ty → Ty
  | [], τ => τ
  | ρ :: ρs, τ => .lolli ρ (lolliMany ρs τ)

end Ty

/-- Definition 2.2 (Set model, p. 3):
In the naive set model every type `ρ` is interpreted by the set `S^ρ`, where `U` is a
singleton set, `⋄` is an unspecified nonempty set (modeled here by `Unit`), `L(ρ)` is `List S^ρ`,
`ρ ⊸ σ` is the full function space `S^ρ → S^σ`, `ρ ⊗ σ` and `ρ × σ` are the Cartesian product,
and `ρ + σ` is the disjoint sum. -/
def SetModel : Ty → Type
  | .unit => PUnit
  | .diamond => Unit
  | .list ρ => List (SetModel ρ)
  | .lolli ρ σ => SetModel ρ → SetModel σ
  | .tensor ρ σ => SetModel ρ × SetModel σ
  | .prod ρ σ => SetModel ρ × SetModel σ
  | .sum ρ σ => Sum (SetModel ρ) (SetModel σ)

/-- Typed term variable `x^ρ` (p. 4). Each variable has an identifier and a fixed type `ρ`. -/
structure Var where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr

/-- Definition 2.5 (Constants, p. 4). -/
inductive Const where
  | eps : Const
  | nil : Ty → Const
  | cons : Ty → Const
  | tensorIntro : Ty → Ty → Const
  | tensorElim : Ty → Ty → Ty → Const
  | prodIntro : Ty → Ty → Ty → Const
  | fst : Ty → Ty → Const
  | snd : Ty → Ty → Const
  | inl : Ty → Ty → Const
  | inr : Ty → Ty → Const
  | sumElim : Ty → Ty → Ty → Const
  deriving DecidableEq, Repr

/-- Type assignment `c : ρ` for constants from Definition 2.5 (p. 4). -/
def Const.ty : Const → Ty
  | .eps => .unit
  | .nil ρ => .list ρ
  | .cons ρ => .lolli .diamond (.lolli ρ (.lolli (.list ρ) (.list ρ)))
  | .tensorIntro ρ σ => .lolli ρ (.lolli σ (.tensor ρ σ))
  | .tensorElim ρ σ τ => .lolli (.tensor ρ σ) (.lolli (.lolli ρ (.lolli σ τ)) τ)
  | .prodIntro ρ σ τ =>
      .lolli (.lolli τ ρ) (.lolli (.lolli τ σ) (.lolli τ (.prod ρ σ)))
  | .fst ρ σ => .lolli (.prod ρ σ) ρ
  | .snd ρ σ => .lolli (.prod ρ σ) σ
  | .inl ρ σ => .lolli ρ (.sum ρ σ)
  | .inr ρ σ => .lolli σ (.sum ρ σ)
  | .sumElim ρ σ τ =>
      .lolli (.sum ρ σ) (.lolli (.prod (.lolli ρ τ) (.lolli σ τ)) τ)

/-- Constructors of the term calculus (Axiom 22, p. 15 & Remark 3.11(4), p. 16):
`ε, ⊗⁺, inl, inr, nil, cons`. -/
def Const.isConstructor : Const → Bool
  | .eps => true
  | .tensorIntro _ _ => true
  | .inl _ _ => true
  | .inr _ _ => true
  | .nil _ => true
  | .cons _ => true
  | _ => false

/-- Definition 2.4 (Terms, p. 4):
`r, s ::= x^ρ | c | λx^ρ r | rs | r{s}`. -/
inductive Term where
  | var : Var → Term
  | const : Const → Term
  | lam : Var → Term → Term
  | app : Term → Term → Term
  | iter : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Multi-argument application `r s₁ ... sₙ`. -/
def appMany : Term → List Term → Term
  | r, [] => r
  | r, s :: ss => appMany (.app r s) ss

/-- Multi-variable lambda abstraction `λ x₁ ... xₙ. r`. -/
def lamMany : List Var → Term → Term
  | [], r => r
  | x :: xs, r => .lam x (lamMany xs r)

/-- Identity combinator `id_ρ := λ x^ρ. x^ρ`. -/
def idTerm (ρ : Ty) : Term :=
  let x : Var := ⟨0, ρ⟩
  .lam x (.var x)

/-- Boolean constant `tt := inl_{U,U} ε` (Remark 3.2, p. 10). -/
def tt : Term := .app (.const (.inl .unit .unit)) (.const .eps)

/-- Boolean constant `ff := inr_{U,U} ε` (Remark 3.2, p. 10). -/
def ff : Term := .app (.const (.inr .unit .unit)) (.const .eps)

/-- Zero numeral `0 := nil_U` (Example 2.15, p. 6). -/
def zeroNat : Term := .const (.nil .unit)

/-- Successor operation `S d r := cons_U d ε r` (Example 2.15, p. 6). -/
def succNat (d r : Term) : Term :=
  .app (.app (.app (.const (.cons .unit)) d) (.const .eps)) r

/-- Definition 2.14 (Projections, p. 6):
`π₀(r) := ⊗⁻_{ρσρ} r (λx^ρ, y^σ. x)`. -/
def pi0 (ρ σ : Ty) (r : Term) : Term :=
  let x : Var := ⟨0, ρ⟩
  let y : Var := ⟨1, σ⟩
  .app (.app (.const (.tensorElim ρ σ ρ)) r) (.lam x (.lam y (.var x)))

/-- Definition 2.14 (Projections, p. 6):
`π₁(r) := ⊗⁻_{ρσσ} r (λx^ρ, y^σ. y)`. -/
def pi1 (ρ σ : Ty) (r : Term) : Term :=
  let x : Var := ⟨0, ρ⟩
  let y : Var := ⟨1, σ⟩
  .app (.app (.const (.tensorElim ρ σ σ)) r) (.lam x (.lam y (.var y)))

end Term

/-- Free variable occurrences of a term `r`, as a list preserving multiplicity
(Definition 2.4, p. 4 and Definition 2.20, p. 8: `|FV(s)|` is the number of occurrences
of free variables in `s`). -/
def freeVarOccurrences : Term → List Var
  | .var x => [x]
  | .const _ => []
  | .lam x r => (freeVarOccurrences r).filter (· != x)
  | .app r s => freeVarOccurrences r ++ freeVarOccurrences s
  | .iter r s => freeVarOccurrences r ++ freeVarOccurrences s

/-- Underlying set of free variables `FV(r)` (represented as a duplicate-free list). -/
def freeVars (r : Term) : List Var :=
  (freeVarOccurrences r).eraseDups

/-- Number of occurrences of free variables `|FV(r)|` (Definition 2.20, p. 8). -/
def freeVarCount (r : Term) : Nat :=
  (freeVarOccurrences r).length

/-- Disjointness of free variables `FV(r) ∩ FV(s) = ∅`. -/
def DisjointFV (r s : Term) : Prop :=
  ∀ v, v ∈ freeVarOccurrences r → v ∉ freeVarOccurrences s

/-- A term is closed if `FV(r) = ∅`. -/
def IsClosed (r : Term) : Prop :=
  freeVarOccurrences r = []

/-- Definition 2.12 (Almost closed terms, p. 6):
A term is almost closed if all its free variables are of type `⋄`. -/
def IsAlmostClosed (r : Term) : Prop :=
  ∀ v ∈ freeVarOccurrences r, v.ty = .diamond

/-- Maximum variable id occurring anywhere in a term (bound or free). -/
def maxVarId : Term → Nat
  | .var x => x.id
  | .const _ => 0
  | .lam x r => Nat.max x.id (maxVarId r)
  | .app r s => Nat.max (maxVarId r) (maxVarId s)
  | .iter r s => Nat.max (maxVarId r) (maxVarId s)

/-- Replace free occurrences of variable `x` with variable `y` in `r`. -/
def renameFreeVar (r : Term) (x y : Var) : Term :=
  match r with
  | .var v => if v == x then .var y else .var v
  | .const c => .const c
  | .lam v body =>
      if v == x then .lam v body else .lam v (renameFreeVar body x y)
  | .app t s => .app (renameFreeVar t x y) (renameFreeVar s x y)
  | .iter t s => .iter (renameFreeVar t x y) (renameFreeVar s x y)

/-- Syntactic size of a raw term used for termination of capture-avoiding substitution. -/
def rawSize : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .lam _ r => rawSize r + 1
  | .app r s => rawSize r + rawSize s + 1
  | .iter r s => rawSize r + rawSize s + 1

theorem renameFreeVar_rawSize (r : Term) (x y : Var) :
    rawSize (renameFreeVar r x y) = rawSize r := by
  induction r with
  | var v =>
      simp only [renameFreeVar]
      split <;> rfl
  | const c => rfl
  | lam v body ih =>
      simp only [renameFreeVar]
      split
      · rfl
      · simp [rawSize, ih]
  | app t s iht ihs =>
      simp [renameFreeVar, rawSize, iht, ihs]
  | iter t s iht ihs =>
      simp [renameFreeVar, rawSize, iht, ihs]

/-- Capture-avoiding substitution `r[s/x]` (Definition 2.4, p. 4):
substitutes `s` for every free occurrence of `x` in `r`, renaming bound variables in `r`
if necessary to avoid capturing free variables of `s`. -/
def substTerm (r : Term) (x : Var) (s : Term) : Term :=
  match r with
  | .var v => if v == x then s else .var v
  | .const c => .const c
  | .lam v body =>
      if v == x then
        .lam v body
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarId body) (Nat.max (maxVarId s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .lam v' (substTerm (renameFreeVar body v v') x s)
      else
        .lam v (substTerm body x s)
  | .app t u => .app (substTerm t x s) (substTerm u x s)
  | .iter t u => .iter (substTerm t x s) (substTerm u x s)
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

/-- Simultaneous substitution `r[s₁/x₁, ..., sₙ/xₙ]` applied sequentially. -/
def substMany : Term → List (Var × Term) → Term
  | r, [] => r
  | r, (x, s) :: rest => substMany (substTerm r x s) rest

/-- Definition 2.6 (Typing, pp. 4–5):
The relation `HasType r ρ` (`r^ρ`, read "`r` has type `ρ`"). -/
inductive HasType : Term → Ty → Prop where
  | var (x : Var) :
      HasType (.var x) x.ty
  | const (c : Const) :
      HasType (.const c) c.ty
  | lam (x : Var) {r : Term} {σ : Ty} :
      HasType r σ →
      HasType (.lam x r) (.lolli x.ty σ)
  | app {r s : Term} {ρ σ : Ty} :
      HasType r (.lolli ρ σ) →
      HasType s ρ →
      DisjointFV r s →
      HasType (.app r s) σ
  | iter {r s : Term} {ρ τ : Ty} :
      HasType r (.list ρ) →
      HasType s (.lolli .diamond (.lolli ρ (.lolli τ τ))) →
      IsClosed s →
      HasType (.iter r s) (.lolli τ τ)

/-- Weak typing (Section 3.1, p. 10):
"all restrictions on free variables (when typing terms of the form `rs` or `r{s}`) are dropped." -/
inductive WeaklyTyped : Term → Ty → Prop where
  | var (x : Var) :
      WeaklyTyped (.var x) x.ty
  | const (c : Const) :
      WeaklyTyped (.const c) c.ty
  | lam (x : Var) {r : Term} {σ : Ty} :
      WeaklyTyped r σ →
      WeaklyTyped (.lam x r) (.lolli x.ty σ)
  | app {r s : Term} {ρ σ : Ty} :
      WeaklyTyped r (.lolli ρ σ) →
      WeaklyTyped s ρ →
      WeaklyTyped (.app r s) σ
  | iter {r s : Term} {ρ τ : Ty} :
      WeaklyTyped r (.list ρ) →
      WeaklyTyped s (.lolli .diamond (.lolli ρ (.lolli τ τ))) →
      WeaklyTyped (.iter r s) (.lolli τ τ)

/-- Definition 2.8 (Lists, p. 5):
Terms of the form `cons_ρ d₁ r₁ (... (cons_ρ dₙ rₙ nil_ρ))` are lists with `n` entries.
`listEntryCount t` returns `some n` if `t` has this spine with `n` entries, and `none` otherwise. -/
def listEntryCount : Term → Option Nat
  | .const (.nil _) => some 0
  | .app (.app (.app (.const (.cons _)) _) _) l =>
      match listEntryCount l with
      | some k => some (k + 1)
      | none => none
  | _ => none

/-- Predicate asserting that `t` is a list in the sense of Definition 2.8 (p. 5). -/
def IsListTerm (t : Term) : Prop :=
  ∃ n, listEntryCount t = some n

/-- Definition 2.9 (Conversions, p. 5): `r ↦ r'`. -/
inductive ConvStep : Term → Term → Prop where
  | beta (x : Var) (r s : Term) :
      ConvStep (.app (.lam x r) s) (substTerm r x s)
  | tensorBeta (ρ σ τ : Ty) (r s t : Term) :
      ConvStep
        (.app (.app (.const (.tensorElim ρ σ τ))
          (.app (.app (.const (.tensorIntro ρ σ)) r) s)) t)
        (.app (.app t r) s)
  | fstBeta (ρ σ τ : Ty) (r s t : Term) :
      ConvStep
        (.app (.const (.fst ρ σ))
          (.app (.app (.app (.const (.prodIntro ρ σ τ)) r) s) t))
        (.app r t)
  | sndBeta (ρ σ τ : Ty) (r s t : Term) :
      ConvStep
        (.app (.const (.snd ρ σ))
          (.app (.app (.app (.const (.prodIntro ρ σ τ)) r) s) t))
        (.app s t)
  | inlBeta (ρ σ τ : Ty) (r s : Term) :
      ConvStep
        (.app (.app (.const (.sumElim ρ σ τ))
          (.app (.const (.inl ρ σ)) r)) s)
        (.app (.app (.const (.fst (.lolli ρ τ) (.lolli σ τ))) s) r)
  | inrBeta (ρ σ τ : Ty) (r s : Term) :
      ConvStep
        (.app (.app (.const (.sumElim ρ σ τ))
          (.app (.const (.inr ρ σ)) r)) s)
        (.app (.app (.const (.snd (.lolli ρ τ) (.lolli σ τ))) s) r)
  | iterNil (ρ : Ty) (s t : Term) :
      ConvStep (.app (.iter (.const (.nil ρ)) s) t) t
  | iterCons (ρ : Ty) (d r l s t : Term) :
      IsListTerm l →
      ConvStep
        (.app (.iter (.app (.app (.app (.const (.cons ρ)) d) r) l) s) t)
        (.app (.app (.app s d) r) (.app (.iter l s) t))

/-- Definition 2.10 (Reduction, p. 5): `r → r'`.
To reduce a term we may convert anywhere, except under `λ`. -/
inductive RedStep : Term → Term → Prop where
  | conv {r r' : Term} :
      ConvStep r r' → RedStep r r'
  | appLeft {r r' : Term} (s : Term) :
      RedStep r r' → RedStep (.app r s) (.app r' s)
  | appRight (r : Term) {s s' : Term} :
      RedStep s s' → RedStep (.app r s) (.app r s')
  | iterLeft {r r' : Term} (s : Term) :
      RedStep r r' → RedStep (.iter r s) (.iter r' s)
  | iterRight (r : Term) {s s' : Term} :
      RedStep s s' → RedStep (.iter r s) (.iter r s')

/-- Reflexive-transitive closure of reduction `r →* r'` (p. 6). -/
inductive RedStar : Term → Term → Prop where
  | refl (r : Term) : RedStar r r
  | step {r s t : Term} : RedStep r s → RedStar s t → RedStar r t

/-- Exact `k`-step reduction chain `r →^k r'`. -/
inductive RedSteps : Nat → Term → Term → Prop where
  | zero (r : Term) : RedSteps 0 r r
  | succ {k : Nat} {r s t : Term} :
      RedStep r s → RedSteps k s t → RedSteps (k + 1) r t

/-- A term is normal if it cannot be reduced (p. 6). -/
def IsNormal (r : Term) : Prop :=
  ¬ ∃ r', RedStep r r'

/-- Proposition 2.13 (Canonical forms of normal almost closed terms, p. 6):
- `U`: `ε`
- `⋄`: variable
- `L(ρ)`: list
- `ρ ⊗ σ`: `⊗⁺ r s`
- `ρ × σ`: `×⁺_{ρ,σ,τ} r s t`
- `ρ + σ`: `inl r` or `inr r`
- `ρ ⊸ σ`: `λx r` or `c r⃗` or `r{s}`. -/
def HasCanonicalNormalForm (τ : Ty) (w : Term) : Prop :=
  match τ with
  | .unit => w = .const .eps
  | .diamond => ∃ x : Var, x.ty = .diamond ∧ w = .var x
  | .list _ => IsListTerm w
  | .tensor ρ σ => ∃ r s, w = .app (.app (.const (.tensorIntro ρ σ)) r) s
  | .prod ρ σ => ∃ ν r s t, w = .app (.app (.app (.const (.prodIntro ρ σ ν)) r) s) t
  | .sum ρ σ =>
      (∃ r, w = .app (.const (.inl ρ σ)) r) ∨
      (∃ r, w = .app (.const (.inr ρ σ)) r)
  | .lolli _ _ =>
      (∃ x r, w = .lam x r) ∨
      (∃ c args, w = Term.appMany (.const c) args) ∨
      (∃ r s, w = .iter r s)

/-- Definition 2.17 (p. 7): `#_n(r)` returns `k` if `r` is a list with `k` entries and `k ≤ n`,
and `n` otherwise. -/
def hashBound (n : Nat) (r : Term) : Nat :=
  match listEntryCount r with
  | some k => if k ≤ n then k else n
  | none => n

/-- Definition 2.17 (pp. 7–8): Step-bounding functional `ϑ_n(r)`. -/
def theta (n : Nat) : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .app r s => theta n r + theta n s
  | .lam _ r => theta n r + 1
  | .iter r s => theta n r + (hashBound n r + 1) * theta n s

/-- Nesting depth of `{.}` in a term `r` (Section 2.3, pp. 7–9). -/
def iterNesting : Term → Nat
  | .var _ => 0
  | .const _ => 0
  | .lam _ r => iterNesting r
  | .app r s => Nat.max (iterNesting r) (iterNesting s)
  | .iter r s => Nat.max (iterNesting r) (iterNesting s + 1)

/-- Ordinary syntactical length `length(s)` of a term (Proposition 2.23, p. 9). -/
def termLength : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .lam _ r => termLength r + 1
  | .app r s => termLength r + termLength s
  | .iter r s => termLength r + termLength s

/-- Predicate stating that a term contains no `{.}` (Proposition 2.23, p. 9). -/
def IsIterFree (r : Term) : Prop :=
  iterNesting r = 0

/-- Definition 2.20 (p. 8): `r →_n r'` holds if `r → r'` by converting a subterm `s` of `r`
with `|FV(s)| ≤ n`, where `|FV(s)|` is the number of occurrences of free variables in `s`. -/
inductive RedStepBounded (n : Nat) : Term → Term → Prop where
  | conv {r r' : Term} :
      ConvStep r r' →
      freeVarCount r ≤ n →
      RedStepBounded n r r'
  | appLeft {r r' : Term} (s : Term) :
      RedStepBounded n r r' →
      RedStepBounded n (.app r s) (.app r' s)
  | appRight (r : Term) {s s' : Term} :
      RedStepBounded n s s' →
      RedStepBounded n (.app r s) (.app r s')
  | iterLeft {r r' : Term} (s : Term) :
      RedStepBounded n r r' →
      RedStepBounded n (.iter r s) (.iter r' s)
  | iterRight (r : Term) {s s' : Term} :
      RedStepBounded n s s' →
      RedStepBounded n (.iter r s) (.iter r s')

/-- Definition 2.24 (Data types, p. 9):
A type is called a data type if it is built from `U`, `L(.)`, `⊗`, and `+` only. -/
inductive IsDataType : Ty → Prop where
  | unit : IsDataType .unit
  | list {ρ : Ty} : IsDataType ρ → IsDataType (.list ρ)
  | tensor {ρ σ : Ty} : IsDataType ρ → IsDataType σ → IsDataType (.tensor ρ σ)
  | sum {ρ σ : Ty} : IsDataType ρ → IsDataType σ → IsDataType (.sum ρ σ)

/-- Definition 2.24 (Data objects, p. 9):
A data object of data type `τ` is an almost closed term `w^τ` in normal form. -/
def IsDataObject (τ : Ty) (w : Term) : Prop :=
  IsDataType τ ∧ HasType w τ ∧ IsAlmostClosed w ∧ IsNormal w

/-- A tuple of terms `ws` is a tuple of data objects of types `τs` with pairwise disjoint
free variables (and disjoint from a given program term `r`), so that the application
`r w₁ ... wₙ` is well-typed. -/
inductive ValidDataInputs : Term → List Ty → List Term → Prop where
  | nil (r : Term) : ValidDataInputs r [] []
  | cons {r : Term} {τ : Ty} {w : Term} {τs : List Ty} {ws : List Term} :
      IsDataObject τ w →
      DisjointFV r w →
      ValidDataInputs (.app r w) τs ws →
      ValidDataInputs r (τ :: τs) (w :: ws)

/-- Sum of syntactical lengths of a tuple of input terms. -/
def totalTermLength : List Term → Nat
  | [] => 0
  | w :: ws => termLength w + totalTermLength ws

/-- Sum of free-variable counts of a tuple of input terms. -/
def totalFreeVarCount : List Term → Nat
  | [] => 0
  | w :: ws => freeVarCount w + totalFreeVarCount ws

/-- A function `B : Nat → Nat` is bounded by a polynomial of degree at most `d`
if there exist constants `c₀, c₁ : Nat` such that `B n ≤ c₀ * (n + 1)^d + c₁` for all `n`. -/
def BoundedByPolyOfDegree (B : Nat → Nat) (d : Nat) : Prop :=
  ∃ c₀ c₁ : Nat, ∀ n : Nat, B n ≤ c₀ * (n + 1) ^ d + c₁

end ABHS2004


/-!
# Linear Arithmetic for Non-Size-Increasing Polytime Computation (ABHS 2004, Section 3)

Source: Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg,
"An arithmetic for non-size-increasing polynomial-time computation",
*Theoretical Computer Science* 318(1–2), 2004, pp. 3–27, Section 3 (pp. 10–19).

This module formalizes:
- Section 3.1: Predicate symbols (`PredSym`), formulas (`Formula`, Definition 3.1),
  abbreviations `bot`, `neg`, `iff` (Remark 3.2), computational content `tau` (Definition 3.3),
  type cleaning `cleanTy` and `tauClean` (Definition 3.4), and Harrop / computationally
  irrelevant formulas `IsHarrop` (Definition 3.5).
- Section 3.2: Assumption variables (`AssumpVar`), core axioms (Definition 3.8, equations
  (3)–(25)), raw proof terms (`ProofTerm`, Definition 3.6), and the two-zone natural
  deduction system `Derives Π Γ M A` (`Π | Γ ⊢ M : A`, Definition 3.7).
-/

namespace ABHS2004

/-- Predicate symbols different from the existence predicates `E_ρ`, including
equality `=_ρ` and arbitrary fixed-arity predicate symbols `P, Q` (Section 3.1, p. 10). -/
inductive PredSym where
  | eq (ρ : Ty) : PredSym
  | rel (id : Nat) (arity : List Ty) : PredSym
  deriving DecidableEq, Repr

/-- Arity (list of argument types) of a predicate symbol. -/
def PredSym.arity : PredSym → List Ty
  | .eq ρ => [ρ, ρ]
  | .rel _ tys => tys

/-- A list of terms `rs` is weakly typed according to the arity `tys` (Section 3.1, p. 10). -/
inductive WeaklyTypedList : List Term → List Ty → Prop where
  | nil : WeaklyTypedList [] []
  | cons {r : Term} {ρ : Ty} {rs : List Term} {ρs : List Ty} :
      WeaklyTyped r ρ →
      WeaklyTypedList rs ρs →
      WeaklyTypedList (r :: rs) (ρ :: ρs)

/-- Definition 3.1 (Formulas, p. 10):
`A, B, C ::= P(r⃗) | E_ρ(r) | A → B | A ⊗ B | A ∧ B | A ∨ B | ∀x^ρ A | ∃x^ρ A`. -/
inductive Formula where
  | pred : PredSym → List Term → Formula
  | existPred : Ty → Term → Formula
  | imp : Formula → Formula → Formula
  | tensor : Formula → Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | all : Var → Formula → Formula
  | ex : Var → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

/-- Equality formula `r =_ρ s` (Section 3.1, p. 10). -/
def eqForm (ρ : Ty) (r s : Term) : Formula :=
  .pred (.eq ρ) [r, s]

/-- Remark 3.2 (p. 10): Falsity `⊥ := (tt =_B ff)`. -/
def bot : Formula :=
  eqForm Ty.bool Term.tt Term.ff

/-- Remark 3.2 (p. 10): Negation `¬A := A → ⊥`. -/
def neg (A : Formula) : Formula :=
  .imp A bot

/-- Bi-implication `A ↔ B := (A → B) ∧ (B → A)`. -/
def iffForm (A B : Formula) : Formula :=
  .conj (.imp A B) (.imp B A)

/-- Iterated implication `A₁ → ⋯ → Aₙ → B`. -/
def impMany : List Formula → Formula → Formula
  | [], B => B
  | A :: As, B => .imp A (impMany As B)

/-- Iterated universal quantification `∀ x₁ ... xₙ. A`. -/
def allMany : List Var → Formula → Formula
  | [], A => A
  | x :: xs, A => .all x (allMany xs A)

/-- Iterated existential quantification `∃ x₁ ... xₙ. A`. -/
def exMany : List Var → Formula → Formula
  | [], A => A
  | x :: xs, A => .ex x (exMany xs A)

/-- Relativized universal quantification `∀ x⃗. E(x⃗) → B` (p. 14, 26). -/
def allRel : List Var → Formula → Formula
  | [], B => B
  | x :: xs, B => .all x (.imp (.existPred x.ty (.var x)) (allRel xs B))

/-- Corollary 4.8 (p. 23): The formula `✸ := ∃ p^⋄. E_⋄(p)`. -/
def lozenge : Formula :=
  let p : Var := ⟨0, .diamond⟩
  .ex p (.existPred .diamond (.var p))

end Formula

/-- Free term variables `FV(A)` of a formula `A`. -/
def freeVarsFormula : Formula → List Var
  | .pred _ rs => (rs.foldr (fun r acc => freeVarOccurrences r ++ acc) []).eraseDups
  | .existPred _ r => freeVars r
  | .imp A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .tensor A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .conj A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .disj A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .all x A => (freeVarsFormula A).filter (· != x)
  | .ex x A => (freeVarsFormula A).filter (· != x)

/-- Maximum variable id occurring in a list of terms. -/
def maxVarIdList : List Term → Nat
  | [] => 0
  | r :: rs => Nat.max (maxVarId r) (maxVarIdList rs)

/-- Maximum variable id occurring anywhere in a formula. -/
def maxVarIdFormula : Formula → Nat
  | .pred _ rs => maxVarIdList rs
  | .existPred _ r => maxVarId r
  | .imp A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .tensor A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .conj A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .disj A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .all x A => Nat.max x.id (maxVarIdFormula A)
  | .ex x A => Nat.max x.id (maxVarIdFormula A)

/-- Rename free occurrences of term variable `x` to `y` in a formula `A`. -/
def renameFreeVarFormula (A : Formula) (x y : Var) : Formula :=
  match A with
  | .pred P rs => .pred P (rs.map (fun r => renameFreeVar r x y))
  | .existPred ρ r => .existPred ρ (renameFreeVar r x y)
  | .imp B C => .imp (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .tensor B C => .tensor (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .conj B C => .conj (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .disj B C => .disj (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .all v B => if v == x then .all v B else .all v (renameFreeVarFormula B x y)
  | .ex v B => if v == x then .ex v B else .ex v (renameFreeVarFormula B x y)

/-- Structural size of a formula used for termination of capture-avoiding substitution. -/
def formulaSize : Formula → Nat
  | .pred _ _ => 1
  | .existPred _ _ => 1
  | .imp B C => formulaSize B + formulaSize C + 1
  | .tensor B C => formulaSize B + formulaSize C + 1
  | .conj B C => formulaSize B + formulaSize C + 1
  | .disj B C => formulaSize B + formulaSize C + 1
  | .all _ B => formulaSize B + 1
  | .ex _ B => formulaSize B + 1

theorem renameFreeVarFormula_size (A : Formula) (x y : Var) :
    formulaSize (renameFreeVarFormula A x y) = formulaSize A := by
  induction A with
  | pred P rs => rfl
  | existPred ρ r => rfl
  | imp B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | tensor B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | conj B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | disj B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | all v B ih =>
      simp only [renameFreeVarFormula]
      split
      · rfl
      · simp [formulaSize, ih]
  | ex v B ih =>
      simp only [renameFreeVarFormula]
      split
      · rfl
      · simp [formulaSize, ih]

/-- Capture-avoiding substitution `A[s/x]` of term `s` for variable `x` in formula `A`. -/
def substFormula (A : Formula) (x : Var) (s : Term) : Formula :=
  match A with
  | .pred P rs => .pred P (rs.map (fun r => substTerm r x s))
  | .existPred ρ r => .existPred ρ (substTerm r x s)
  | .imp B C => .imp (substFormula B x s) (substFormula C x s)
  | .tensor B C => .tensor (substFormula B x s) (substFormula C x s)
  | .conj B C => .conj (substFormula B x s) (substFormula C x s)
  | .disj B C => .disj (substFormula B x s) (substFormula C x s)
  | .all v B =>
      if v == x then
        .all v B
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarId s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .all v' (substFormula (renameFreeVarFormula B v v') x s)
      else
        .all v (substFormula B x s)
  | .ex v B =>
      if v == x then
        .ex v B
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarId s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .ex v' (substFormula (renameFreeVarFormula B v v') x s)
      else
        .ex v (substFormula B x s)
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

/-- Sequential substitution of multiple terms into a formula. -/
def substFormulaMany : Formula → List (Var × Term) → Formula
  | A, [] => A
  | A, (x, s) :: rest => substFormulaMany (substFormula A x s) rest

/-- Definition 3.3 (Computational content, p. 11):
For a formula `A`, `tau A` (`τ(A)`) is the type of its potential realizers. -/
def tau : Formula → Ty
  | .existPred ρ _ => ρ
  | .pred _ _ => .unit
  | .imp A B => .lolli (tau A) (tau B)
  | .tensor A B => .tensor (tau A) (tau B)
  | .conj A B => .prod (tau A) (tau B)
  | .disj A B => .sum (tau A) (tau B)
  | .all _ A => tau A
  | .ex _ A => tau A

/-- Definition 3.4 (Cleaning of types, pp. 11–12): `c(ρ)`. -/
def cleanTy : Ty → Ty
  | .unit => .unit
  | .diamond => .diamond
  | .lolli ρ σ =>
      let cρ := cleanTy ρ
      let cσ := cleanTy σ
      if cσ == .unit then .unit
      else if cρ == .unit then cσ
      else .lolli cρ cσ
  | .tensor ρ σ =>
      let cρ := cleanTy ρ
      let cσ := cleanTy σ
      if cσ == .unit then cρ
      else if cρ == .unit then cσ
      else .tensor cρ cσ
  | .prod ρ σ =>
      let cρ := cleanTy ρ
      let cσ := cleanTy σ
      if cσ == .unit then cρ
      else if cρ == .unit then cσ
      else .prod cρ cσ
  | .sum ρ σ => .sum (cleanTy ρ) (cleanTy σ)
  | .list ρ => .list (cleanTy ρ)

/-- Cleaned computational content `τ^c(A) := c(τ(A))` (p. 12). -/
def tauClean (A : Formula) : Ty :=
  cleanTy (tau A)

/-- Definition 3.5 (Harrop / computationally irrelevant formulas, p. 12):
A formula `A` has no computational content (is Harrop / c.i.) iff `τ^c(A) = U`. -/
def IsHarrop (A : Formula) : Prop :=
  tauClean A = .unit

/-- Formula containing neither existence predicates `E_ρ` nor disjunctions `∨`
(Proposition 4.2(1), p. 20 & Corollary 4.11, p. 26). -/
def IsExistAndDisjFree : Formula → Prop
  | .pred _ _ => True
  | .existPred _ _ => False
  | .imp A B => IsExistAndDisjFree A ∧ IsExistAndDisjFree B
  | .tensor A B => IsExistAndDisjFree A ∧ IsExistAndDisjFree B
  | .conj A B => IsExistAndDisjFree A ∧ IsExistAndDisjFree B
  | .disj _ _ => False
  | .all _ A => IsExistAndDisjFree A
  | .ex _ A => IsExistAndDisjFree A

/-- Assumption variable `u^A` (Section 3.2, p. 12). -/
structure AssumpVar where
  id : Nat
  formula : Formula
  deriving DecidableEq, Repr

/-- Proof contexts `Π, Γ` are finite sets of assumption variables (represented as lists). -/
abbrev ProofContext := List AssumpVar

/-- Conversion equations `r =_ρ r'` corresponding to Definition 2.9, where in the equation
`cons_ρ d^⋄ r l {s} t = s d^⋄ r (l {s} t)` the term `l` can be arbitrary (Axiom 13, p. 15). -/
inductive AxiomConvEq : Ty → Term → Term → Prop where
  | beta (x : Var) (r s : Term) (σ : Ty) :
      WeaklyTyped (.lam x r) (.lolli x.ty σ) →
      WeaklyTyped s x.ty →
      AxiomConvEq σ (.app (.lam x r) s) (substTerm r x s)
  | tensorBeta (ρ σ τ : Ty) (r s t : Term) :
      WeaklyTyped r ρ →
      WeaklyTyped s σ →
      WeaklyTyped t (.lolli ρ (.lolli σ τ)) →
      AxiomConvEq τ
        (.app (.app (.const (.tensorElim ρ σ τ))
          (.app (.app (.const (.tensorIntro ρ σ)) r) s)) t)
        (.app (.app t r) s)
  | fstBeta (ρ σ τ : Ty) (r s t : Term) :
      WeaklyTyped r (.lolli τ ρ) →
      WeaklyTyped s (.lolli τ σ) →
      WeaklyTyped t τ →
      AxiomConvEq ρ
        (.app (.const (.fst ρ σ))
          (.app (.app (.app (.const (.prodIntro ρ σ τ)) r) s) t))
        (.app r t)
  | sndBeta (ρ σ τ : Ty) (r s t : Term) :
      WeaklyTyped r (.lolli τ ρ) →
      WeaklyTyped s (.lolli τ σ) →
      WeaklyTyped t τ →
      AxiomConvEq σ
        (.app (.const (.snd ρ σ))
          (.app (.app (.app (.const (.prodIntro ρ σ τ)) r) s) t))
        (.app s t)
  | inlBeta (ρ σ τ : Ty) (r s : Term) :
      WeaklyTyped r ρ →
      WeaklyTyped s (.prod (.lolli ρ τ) (.lolli σ τ)) →
      AxiomConvEq τ
        (.app (.app (.const (.sumElim ρ σ τ))
          (.app (.const (.inl ρ σ)) r)) s)
        (.app (.app (.const (.fst (.lolli ρ τ) (.lolli σ τ))) s) r)
  | inrBeta (ρ σ τ : Ty) (r s : Term) :
      WeaklyTyped r σ →
      WeaklyTyped s (.prod (.lolli ρ τ) (.lolli σ τ)) →
      AxiomConvEq τ
        (.app (.app (.const (.sumElim ρ σ τ))
          (.app (.const (.inr ρ σ)) r)) s)
        (.app (.app (.const (.snd (.lolli ρ τ) (.lolli σ τ))) s) r)
  | iterNil (ρ τ : Ty) (s t : Term) :
      WeaklyTyped s (.lolli .diamond (.lolli ρ (.lolli τ τ))) →
      WeaklyTyped t τ →
      AxiomConvEq τ (.app (.iter (.const (.nil ρ)) s) t) t
  | iterConsArb (ρ τ : Ty) (d r l s t : Term) :
      WeaklyTyped d .diamond →
      WeaklyTyped r ρ →
      WeaklyTyped l (.list ρ) →
      WeaklyTyped s (.lolli .diamond (.lolli ρ (.lolli τ τ))) →
      WeaklyTyped t τ →
      AxiomConvEq τ
        (.app (.iter (.app (.app (.app (.const (.cons ρ)) d) r) l) s) t)
        (.app (.app (.app s d) r) (.app (.iter l s) t))

/-- Helper building the compatibility chain `x₁ = y₁ → ⋯ → xₙ = yₙ → B`. -/
def eqChainImp : List Ty → List Term → List Term → Formula → Formula
  | ρ :: ρs, x :: xs, y :: ys, B =>
      .imp (Formula.eqForm ρ x y) (eqChainImp ρs xs ys B)
  | _, _, _, B => B

/-- Definition 3.8 (Axioms for the core system, pp. 14–15, equations (3)–(25)).
Each constructor of `CoreAxiom` represents a core axiom instance together with its
canonical formula `CoreAxiom.formula`. -/
inductive CoreAxiom where
  /-- (3) `(C → A) → (C → B) → C → A ∧ B` -/
  | ax3 (A B C : Formula)
  /-- (4) `A₀ ∧ A₁ → A₀` -/
  | ax4_left (A₀ A₁ : Formula)
  /-- (4) `A₀ ∧ A₁ → A₁` -/
  | ax4_right (A₀ A₁ : Formula)
  /-- (5) `A → B → A ⊗ B` -/
  | ax5 (A B : Formula)
  /-- (6) `A ⊗ B → (A → B → C) → C` -/
  | ax6 (A B C : Formula)
  /-- (7) `A₀ → A₀ ∨ A₁` -/
  | ax7_left (A₀ A₁ : Formula)
  /-- (7) `A₁ → A₀ ∨ A₁` -/
  | ax7_right (A₀ A₁ : Formula)
  /-- (8) `(A → C) ∧ (B → C) → A ∨ B → C` -/
  | ax8 (A B C : Formula)
  /-- (9) `∀x.A → ∃x.A` -/
  | ax9 (x : Var) (A : Formula)
  /-- (10) `∃x.A → (∀x.A → B) → B` with `x ∉ FV(B)` -/
  | ax10 (x : Var) (A B : Formula)
  /-- (11) `⊥ → P(r⃗)` -/
  | ax11 (P : PredSym) (rs : List Term)
  /-- (12) Reflexivity `r =_ρ r` -/
  | ax12_refl (ρ : Ty) (r : Term)
  /-- (12) Symmetry `r =_ρ s → s =_ρ r` -/
  | ax12_symm (ρ : Ty) (r s : Term)
  /-- (12) Transitivity `r =_ρ s → s =_ρ t → r =_ρ t` -/
  | ax12_trans (ρ : Ty) (r s t : Term)
  /-- (13) Conversion equation `r =_ρ r'` -/
  | ax13 (ρ : Ty) (r r' : Term)
  /-- (14) `f =_{ρ⊸σ} g → x =_ρ y → f x =_σ g y` -/
  | ax14 (ρ σ : Ty) (f g x y : Term)
  /-- (15) `x₁ = y₁ → ⋯ → xₙ = yₙ → P(x₁,...,xₙ) → P(y₁,...,yₙ)` -/
  | ax15 (P : PredSym) (xs ys : List Term)
  /-- (16) `x =_ρ y → E_ρ(x) → E_ρ(y)` -/
  | ax16 (ρ : Ty) (x y : Term)
  /-- (17) `x =_U ε` -/
  | ax17 (x : Term)
  /-- (18) `(∀x^ρ. f x =_σ g x) → f =_{ρ⊸σ} g` -/
  | ax18 (ρ σ : Ty) (x : Var) (f g : Term)
  /-- (19) `fst z =_ρ fst z' ∧ snd z =_σ snd z' → z =_{ρ×σ} z'` -/
  | ax19 (ρ σ : Ty) (z z' : Term)
  /-- (20→) `E_{ρ⊸σ}(f) → ∀x^ρ. E_ρ(x) → E_σ(f x)` -/
  | ax20_imp (ρ σ : Ty) (x : Var) (f : Term)
  /-- (20←) `(∀x^ρ. E_ρ(x) → E_σ(f x)) → E_{ρ⊸σ}(f)` -/
  | ax20_mpr (ρ σ : Ty) (x : Var) (f : Term)
  /-- (21→) `E_{ρ×σ}(z) → E_ρ(fst z) ∧ E_σ(snd z)` -/
  | ax21_imp (ρ σ : Ty) (z : Term)
  /-- (21←) `E_ρ(fst z) ∧ E_σ(snd z) → E_{ρ×σ}(z)` -/
  | ax21_mpr (ρ σ : Ty) (z : Term)
  /-- (22) `E(c)` for constructor `c ∈ {ε, ⊗⁺, inl, inr, nil, cons}` -/
  | ax22 (c : Const)
  /-- (23) `(∀x^ρ, y^σ. E(x, y) → A[⊗⁺ x y / z]) → ∀z^{ρ⊗σ}. E(z) → A` -/
  | ax23 (ρ σ : Ty) (x y z : Var) (A : Formula)
  /-- (24) `(∀x^ρ. E(x) → A[inl x / z]) ∧ (∀y^σ. E(y) → A[inr y / z]) → ∀z^{ρ+σ}. E(z) → A` -/
  | ax24 (ρ σ : Ty) (x y z : Var) (A : Formula)
  /-- (25) `(E_ρ(x) → A) → A` for c.i. formula `A` -/
  | ax25 (ρ : Ty) (x : Term) (A : Formula)
  deriving DecidableEq, Repr

/-- Side conditions and formula assigned to each `CoreAxiom` (Definition 3.8, pp. 14–15). -/
def CoreAxiom.formula : CoreAxiom → Formula
  | .ax3 A B C => .imp (.imp C A) (.imp (.imp C B) (.imp C (.conj A B)))
  | .ax4_left A₀ A₁ => .imp (.conj A₀ A₁) A₀
  | .ax4_right A₀ A₁ => .imp (.conj A₀ A₁) A₁
  | .ax5 A B => .imp A (.imp B (.tensor A B))
  | .ax6 A B C => .imp (.tensor A B) (.imp (.imp A (.imp B C)) C)
  | .ax7_left A₀ A₁ => .imp A₀ (.disj A₀ A₁)
  | .ax7_right A₀ A₁ => .imp A₁ (.disj A₀ A₁)
  | .ax8 A B C => .imp (.conj (.imp A C) (.imp B C)) (.imp (.disj A B) C)
  | .ax9 x A => .imp (.all x A) (.ex x A)
  | .ax10 x A B => .imp (.ex x A) (.imp (.all x (.imp A B)) B)
  | .ax11 P rs => .imp Formula.bot (.pred P rs)
  | .ax12_refl ρ r => Formula.eqForm ρ r r
  | .ax12_symm ρ r s => .imp (Formula.eqForm ρ r s) (Formula.eqForm ρ s r)
  | .ax12_trans ρ r s t =>
      .imp (Formula.eqForm ρ r s) (.imp (Formula.eqForm ρ s t) (Formula.eqForm ρ r t))
  | .ax13 ρ r r' => Formula.eqForm ρ r r'
  | .ax14 ρ σ f g x y =>
      .imp (Formula.eqForm (.lolli ρ σ) f g)
        (.imp (Formula.eqForm ρ x y) (Formula.eqForm σ (.app f x) (.app g y)))
  | .ax15 P xs ys =>
      eqChainImp P.arity xs ys (.imp (.pred P xs) (.pred P ys))
  | .ax16 ρ x y =>
      .imp (Formula.eqForm ρ x y) (.imp (.existPred ρ x) (.existPred ρ y))
  | .ax17 x => Formula.eqForm .unit x (.const .eps)
  | .ax18 ρ σ x f g =>
      .imp (.all x (Formula.eqForm σ (.app f (.var x)) (.app g (.var x))))
        (Formula.eqForm (.lolli ρ σ) f g)
  | .ax19 ρ σ z z' =>
      .imp
        (.conj
          (Formula.eqForm ρ (.app (.const (.fst ρ σ)) z) (.app (.const (.fst ρ σ)) z'))
          (Formula.eqForm σ (.app (.const (.snd ρ σ)) z) (.app (.const (.snd ρ σ)) z')))
        (Formula.eqForm (.prod ρ σ) z z')
  | .ax20_imp ρ σ x f =>
      .imp (.existPred (.lolli ρ σ) f)
        (.all x (.imp (.existPred ρ (.var x)) (.existPred σ (.app f (.var x)))))
  | .ax20_mpr ρ σ x f =>
      .imp (.all x (.imp (.existPred ρ (.var x)) (.existPred σ (.app f (.var x)))))
        (.existPred (.lolli ρ σ) f)
  | .ax21_imp ρ σ z =>
      .imp (.existPred (.prod ρ σ) z)
        (.conj
          (.existPred ρ (.app (.const (.fst ρ σ)) z))
          (.existPred σ (.app (.const (.snd ρ σ)) z)))
  | .ax21_mpr ρ σ z =>
      .imp
        (.conj
          (.existPred ρ (.app (.const (.fst ρ σ)) z))
          (.existPred σ (.app (.const (.snd ρ σ)) z)))
        (.existPred (.prod ρ σ) z)
  | .ax22 c => .existPred c.ty (.const c)
  | .ax23 ρ σ x y z A =>
      let pairxy := Term.app (.app (.const (.tensorIntro ρ σ)) (.var x)) (.var y)
      .imp
        (.all x (.all y
          (.imp (.existPred ρ (.var x))
            (.imp (.existPred σ (.var y)) (substFormula A z pairxy)))))
        (.all z (.imp (.existPred (.tensor ρ σ) (.var z)) A))
  | .ax24 ρ σ x y z A =>
      let inlx := Term.app (.const (.inl ρ σ)) (.var x)
      let inry := Term.app (.const (.inr ρ σ)) (.var y)
      .imp
        (.conj
          (.all x (.imp (.existPred ρ (.var x)) (substFormula A z inlx)))
          (.all y (.imp (.existPred σ (.var y)) (substFormula A z inry))))
        (.all z (.imp (.existPred (.sum ρ σ) (.var z)) A))
  | .ax25 ρ x A => .imp (.imp (.existPred ρ x) A) A

/-- Side conditions ensuring that a `CoreAxiom` is a valid instance of Definition 3.8. -/
def CoreAxiom.IsValid : CoreAxiom → Prop
  | .ax10 x _ B => x ∉ freeVarsFormula B
  | .ax11 P rs => WeaklyTypedList rs P.arity
  | .ax12_refl ρ r => WeaklyTyped r ρ
  | .ax12_symm ρ r s => WeaklyTyped r ρ ∧ WeaklyTyped s ρ
  | .ax12_trans ρ r s t => WeaklyTyped r ρ ∧ WeaklyTyped s ρ ∧ WeaklyTyped t ρ
  | .ax13 ρ r r' => AxiomConvEq ρ r r'
  | .ax14 ρ σ f g x y =>
      WeaklyTyped f (.lolli ρ σ) ∧ WeaklyTyped g (.lolli ρ σ) ∧
      WeaklyTyped x ρ ∧ WeaklyTyped y ρ
  | .ax15 P xs ys => WeaklyTypedList xs P.arity ∧ WeaklyTypedList ys P.arity
  | .ax16 ρ x y => WeaklyTyped x ρ ∧ WeaklyTyped y ρ
  | .ax17 x => WeaklyTyped x .unit
  | .ax18 ρ σ x f g =>
      x.ty = ρ ∧ x ∉ freeVars f ∧ x ∉ freeVars g ∧
      WeaklyTyped f (.lolli ρ σ) ∧ WeaklyTyped g (.lolli ρ σ)
  | .ax19 ρ σ z z' => WeaklyTyped z (.prod ρ σ) ∧ WeaklyTyped z' (.prod ρ σ)
  | .ax20_imp ρ σ x f => x.ty = ρ ∧ x ∉ freeVars f ∧ WeaklyTyped f (.lolli ρ σ)
  | .ax20_mpr ρ σ x f => x.ty = ρ ∧ x ∉ freeVars f ∧ WeaklyTyped f (.lolli ρ σ)
  | .ax21_imp ρ σ z => WeaklyTyped z (.prod ρ σ)
  | .ax21_mpr ρ σ z => WeaklyTyped z (.prod ρ σ)
  | .ax22 c => c.isConstructor = true
  | .ax23 ρ σ x y z A =>
      x.ty = ρ ∧ y.ty = σ ∧ z.ty = .tensor ρ σ ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      x ∉ freeVarsFormula A ∧ y ∉ freeVarsFormula A
  | .ax24 ρ σ x y z A =>
      x.ty = ρ ∧ y.ty = σ ∧ z.ty = .sum ρ σ ∧ x ≠ z ∧ y ≠ z ∧
      x ∉ freeVarsFormula A ∧ y ∉ freeVarsFormula A
  | .ax25 ρ x A => WeaklyTyped x ρ ∧ IsHarrop A
  | _ => True

/-- Definition 3.6 (Raw proof terms, p. 12):
`M, N, L ::= u^A | c | λu^A M | λx^ρ M | M N | M r | M {N}`. -/
inductive ProofTerm where
  | assump : AssumpVar → ProofTerm
  | ax : CoreAxiom → ProofTerm
  | lamAssump : AssumpVar → ProofTerm → ProofTerm
  | lamTerm : Var → ProofTerm → ProofTerm
  | appProof : ProofTerm → ProofTerm → ProofTerm
  | appTerm : ProofTerm → Term → ProofTerm
  | ind : ProofTerm → ProofTerm → ProofTerm
  deriving DecidableEq, Repr

/-- Substitute assumption variable `v` for `u` in proof term `M` (`M[v^A / u^A]`,
used in the `(Contraction)` rule of Definition 3.7, p. 14). -/
def substAssumpProof (M : ProofTerm) (u v : AssumpVar) : ProofTerm :=
  match M with
  | .assump w => if w == u then .assump v else .assump w
  | .ax c => .ax c
  | .lamAssump w body =>
      if w == u then .lamAssump w body else .lamAssump w (substAssumpProof body u v)
  | .lamTerm x body => .lamTerm x (substAssumpProof body u v)
  | .appProof M₁ M₂ => .appProof (substAssumpProof M₁ u v) (substAssumpProof M₂ u v)
  | .appTerm M₁ r => .appTerm (substAssumpProof M₁ u v) r
  | .ind N M₁ => .ind (substAssumpProof N u v) (substAssumpProof M₁ u v)

/-- Bound assumption variables occurring in a proof term `M`. -/
def boundAssumpVars : ProofTerm → List AssumpVar
  | .assump _ => []
  | .ax _ => []
  | .lamAssump w body => w :: boundAssumpVars body
  | .lamTerm _ body => boundAssumpVars body
  | .appProof M₁ M₂ => boundAssumpVars M₁ ++ boundAssumpVars M₂
  | .appTerm M₁ _ => boundAssumpVars M₁
  | .ind N M₁ => boundAssumpVars N ++ boundAssumpVars M₁

/-- All assumption variables (free or bound) occurring in a proof term `M`. -/
def allAssumpVars : ProofTerm → List AssumpVar
  | .assump w => [w]
  | .ax _ => []
  | .lamAssump w body => w :: allAssumpVars body
  | .lamTerm _ body => allAssumpVars body
  | .appProof M₁ M₂ => allAssumpVars M₁ ++ allAssumpVars M₂
  | .appTerm M₁ _ => allAssumpVars M₁
  | .ind N M₁ => allAssumpVars N ++ allAssumpVars M₁

/-- Disjointness of two proof contexts `Π ∩ Γ = ∅` (by assumption variable id, ensuring
distinct assumption variables in a context have distinct ids). -/
def DisjointProofCtx (Δ Γ : ProofContext) : Prop :=
  ∀ u ∈ Δ, ∀ v ∈ Γ, u.id ≠ v.id

/-- Well-formedness of a proof context: no two distinct assumption variables share an id. -/
def CtxIdsUnique (Δ : ProofContext) : Prop :=
  ∀ u ∈ Δ, ∀ v ∈ Δ, u.id = v.id → u = v

/-- Set-extensional union `Θ = Π ∪ Γ` with `Π ∩ Γ = ∅` (Section 3.2, p. 12:
"We denote proof contexts by `Π, Γ, ...`, and write `Π, Γ` for the union `Π ∪ Γ`,
expressing that `Π` and `Γ` are disjoint."). -/
def IsDisjointCtxUnion (Δ Γ Θ : ProofContext) : Prop :=
  DisjointProofCtx Δ Γ ∧ CtxIdsUnique Θ ∧ ∀ u, u ∈ Θ ↔ (u ∈ Δ ∨ u ∈ Γ)

/-- Variable condition `VarCond` for `(∀⁺)` in Definition 3.7 (pp. 13–14):
"`x` must not be free in the type of any element of `Π ∪ Γ`." -/
def VarCond (x : Var) (Δ Γ : ProofContext) : Prop :=
  (∀ u ∈ Δ, x ∉ freeVarsFormula u.formula) ∧
  (∀ u ∈ Γ, x ∉ freeVarsFormula u.formula)

/-- Step formula in the `(L(τ)-Ind)` rule of Definition 3.7 (p. 14):
`∀ p^⋄, x^τ, l^{L(τ)}. E(p) → E(x) → A → A[cons(p, x, l)/l]`. -/
def indStepFormula (τ : Ty) (p x l : Var) (A : Formula) : Formula :=
  let consTerm := Term.app (.app (.app (.const (.cons τ)) (.var p)) (.var x)) (.var l)
  .all p (.all x (.all l
    (.imp (.existPred .diamond (.var p))
      (.imp (.existPred τ (.var x))
        (.imp A (substFormula A l consTerm))))))

/-- Definition 3.7 (Derivations `Π | Γ ⊢ M : A`, pp. 13–14). -/
inductive Derives : ProofContext → ProofContext → ProofTerm → Formula → Prop where
  /-- `(Assumption)`: `Π | Γ, u^A ⊢ u^A : A` -/
  | assumption (Δ Γ Γ' : ProofContext) (u : AssumpVar) :
      DisjointProofCtx Δ Γ' →
      IsDisjointCtxUnion Γ [u] Γ' →
      Derives Δ Γ' (.assump u) u.formula
  /-- `(Axiom)`: `Π | Γ ⊢ c^A : A` -/
  | axiomRule (Δ Γ : ProofContext) (c : CoreAxiom) :
      DisjointProofCtx Δ Γ →
      c.IsValid →
      Derives Δ Γ (.ax c) c.formula
  /-- `(→⁺)`: from `Π | Γ, u^A ⊢ M : B` infer `Π | Γ ⊢ λu^A M : A → B` -/
  | impIntro {Δ Γ Γ' : ProofContext} {u : AssumpVar} {M : ProofTerm} {B : Formula} :
      IsDisjointCtxUnion Γ [u] Γ' →
      Derives Δ Γ' M B →
      Derives Δ Γ (.lamAssump u M) (.imp u.formula B)
  /-- `(→⁻)`: from `Π | Γ₁ ⊢ M : A → B` and `Π | Γ₂ ⊢ N : A` infer `Π | Γ₁, Γ₂ ⊢ M N : B` -/
  | impElim {Δ Γ₁ Γ₂ Γ : ProofContext} {M N : ProofTerm} {A B : Formula} :
      IsDisjointCtxUnion Γ₁ Γ₂ Γ →
      Derives Δ Γ₁ M (.imp A B) →
      Derives Δ Γ₂ N A →
      Derives Δ Γ (.appProof M N) B
  /-- `(∀⁺)`: from `Π | Γ ⊢ M : A` and `VarCond` infer `Π | Γ ⊢ λx^ρ M : ∀x^ρ A` -/
  | allIntro {Δ Γ : ProofContext} (x : Var) {M : ProofTerm} {A : Formula} :
      Derives Δ Γ M A →
      VarCond x Δ Γ →
      Derives Δ Γ (.lamTerm x M) (.all x A)
  /-- `(∀⁻)`: from `Π | Γ ⊢ M : ∀x^ρ A` and `r` weakly typed by `ρ` infer `Π | Γ ⊢ M r : A[r/x]` -/
  | allElim {Δ Γ : ProofContext} {x : Var} {M : ProofTerm} {A : Formula} (r : Term) :
      Derives Δ Γ M (.all x A) →
      WeaklyTyped r x.ty →
      Derives Δ Γ (.appTerm M r) (substFormula A x r)
  /-- `(Passification)`: from `Π | u^B, Γ ⊢ M : A` and `A` c.i. infer `Π, u^B | Γ ⊢ M : A` -/
  | passification {Δ Δ' Γ Γ' : ProofContext} {u : AssumpVar} {M : ProofTerm} {A : Formula} :
      IsDisjointCtxUnion [u] Γ Γ' →
      IsDisjointCtxUnion Δ [u] Δ' →
      IsHarrop A →
      Derives Δ Γ' M A →
      Derives Δ' Γ M A
  /-- `(Contraction)`: from `u^A, Π | v^A, Γ ⊢ M : B` infer `Π | v^A, Γ ⊢ M[v^A/u^A] : B` -/
  | contraction {Δ Δ' Γ Γ' : ProofContext} {u v : AssumpVar} {M : ProofTerm} {B : Formula} :
      u.formula = v.formula →
      v ∉ boundAssumpVars M →
      IsDisjointCtxUnion [u] Δ Δ' →
      IsDisjointCtxUnion [v] Γ Γ' →
      Derives Δ' Γ' M B →
      Derives Δ Γ' (substAssumpProof M u v) B
  /-- `(L(τ)-Ind)`: list iteration induction rule (p. 14). -/
  | listInd {Δ Γ : ProofContext} {N M : ProofTerm} (τ : Ty) (t : Term)
      (p x l : Var) (A : Formula) :
      p.ty = .diamond →
      x.ty = τ →
      l.ty = .list τ →
      p ≠ x → p ≠ l → x ≠ l →
      p ∉ freeVarsFormula A →
      x ∉ freeVarsFormula A →
      WeaklyTyped t (.list τ) →
      Derives Δ Γ N (.existPred (.list τ) t) →
      Derives Δ [] M (indStepFormula τ p x l A) →
      Derives Δ Γ (.ind N M)
        (.imp (substFormula A l (.const (.nil τ))) (substFormula A l t))

/-- Provability judgment `Π | Γ ⊢ A` (p. 15: "there exists a proof term `M` such that
`Π | Γ ⊢ M : A` is derivable"). -/
def Provable (Δ Γ : ProofContext) (A : Formula) : Prop :=
  ∃ M : ProofTerm, Derives Δ Γ M A

/-- Closed provability `⊢ A` (in empty passive and active contexts). -/
def ClosedProvable (A : Formula) : Prop :=
  Provable [] [] A

end ABHS2004


/-!
# Modified Realizability and Program Extraction (ABHS 2004, Section 4)

Source: Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg,
"An arithmetic for non-size-increasing polynomial-time computation",
*Theoretical Computer Science* 318(1–2), 2004, pp. 3–27, Section 4 (pp. 20–26).

This module formalizes:
- Section 4.1: Modified realizability `mr r A` (`r mr A`, Definition 4.1, p. 20).
- Section 4.2: Extracted terms `extractProof M` (`⟦M⟧`, Definition 4.3, pp. 20–21) and
  term cleaning `cleanTerm` / `extractCleaned M` (`⟦M⟧^c := c(⟦M⟧)`, Definition 4.4, p. 22).
- Section 4.3: Context extraction `extractCtx`, `extractCleanCtx`, and realizability
  assumptions `mrAssumptions` for Theorem 4.7 (Soundness of typing, p. 23), Corollary 4.8
  (Underivability, p. 23), Theorem 4.9 (Soundness of modified realizability, p. 24),
  and Corollary 4.11 (Main polytime extraction theorem, p. 26).
-/

namespace ABHS2004

/-- Fresh variable id above a term and two formulas, used when introducing a bound variable
in `mr r (A → B)` and `mr r (A ∨ B)` (Definition 4.1, p. 20). -/
def freshMrVarId (r : Term) (A B : Formula) : Nat :=
  Nat.max (maxVarId r) (Nat.max (maxVarIdFormula A) (maxVarIdFormula B)) + 1

/-- Definition 4.1 (Modified realizability `r mr A`, p. 20):
By induction on `A` we define a formula `mr r A` for arbitrary `r^{τ(A)}`.
- `r mr E_ρ(s) := (r =_ρ s)`
- `r mr P(s⃗) := P(s⃗)`
- `r mr ∀x A := ∀x. r mr A` (renaming `x` if `x ∈ FV(r)`)
- `r mr ∃x A := ∃x. r mr A` (renaming `x` if `x ∈ FV(r)`)
- `r mr (A → B) := ∀x. x mr A → r x mr B`
- `r mr (A ⊗ B) := π₀(r) mr A ∧ π₁(r) mr B`
- `r mr (A ∧ B) := fst r mr A ∧ snd r mr B`
- `r mr (A ∨ B) := (∀x. r = inl x → x mr A) ∧ (∀y. r = inr y → y mr B)`. -/
def mr (r : Term) (A : Formula) : Formula :=
  match A with
  | .existPred ρ s => Formula.eqForm ρ r s
  | .pred P ss => .pred P ss
  | .all x B =>
      if x ∈ freeVarOccurrences r then
        let freshId := Nat.max (maxVarId r) (Nat.max (maxVarIdFormula B) x.id) + 1
        let x' : Var := ⟨freshId, x.ty⟩
        .all x' (mr r (renameFreeVarFormula B x x'))
      else
        .all x (mr r B)
  | .ex x B =>
      if x ∈ freeVarOccurrences r then
        let freshId := Nat.max (maxVarId r) (Nat.max (maxVarIdFormula B) x.id) + 1
        let x' : Var := ⟨freshId, x.ty⟩
        .ex x' (mr r (renameFreeVarFormula B x x'))
      else
        .ex x (mr r B)
  | .imp B C =>
      let x : Var := ⟨freshMrVarId r B C, tau B⟩
      .all x (.imp (mr (.var x) B) (mr (.app r (.var x)) C))
  | .tensor B C =>
      let ρ := tau B
      let σ := tau C
      .conj (mr (Term.pi0 ρ σ r) B) (mr (Term.pi1 ρ σ r) C)
  | .conj B C =>
      let ρ := tau B
      let σ := tau C
      .conj
        (mr (.app (.const (.fst ρ σ)) r) B)
        (mr (.app (.const (.snd ρ σ)) r) C)
  | .disj B C =>
      let ρ := tau B
      let σ := tau C
      let baseId := freshMrVarId r B C
      let x : Var := ⟨baseId, ρ⟩
      let y : Var := ⟨baseId + 1, σ⟩
      let inlx := Term.app (.const (.inl ρ σ)) (.var x)
      let inry := Term.app (.const (.inr ρ σ)) (.var y)
      .conj
        (.all x (.imp (Formula.eqForm (.sum ρ σ) r inlx) (mr (.var x) B)))
        (.all y (.imp (Formula.eqForm (.sum ρ σ) r inry) (mr (.var y) C)))
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

/-- Canonical closed term `ε^ρ` for types whose cleaned type is `U` (or built from dummy terms
for Harrop axiom realizers in Section 4.2, p. 21). -/
def dummyTerm : Ty → Term
  | .unit => .const .eps
  | .diamond => .var ⟨0, .diamond⟩
  | .list ρ => .const (.nil ρ)
  | .lolli ρ σ =>
      let x : Var := ⟨0, ρ⟩
      .lam x (dummyTerm σ)
  | .tensor ρ σ =>
      .app (.app (.const (.tensorIntro ρ σ)) (dummyTerm ρ)) (dummyTerm σ)
  | .prod ρ σ =>
      let u : Var := ⟨0, .unit⟩
      .app (.app (.app (.const (.prodIntro ρ σ .unit))
        (.lam u (dummyTerm ρ)))
        (.lam u (dummyTerm σ)))
        (.const .eps)
  | .sum ρ σ =>
      .app (.const (.inl ρ σ)) (dummyTerm ρ)

/-- Section 4.2 (p. 20): For each assumption variable `u^A` we choose a unique term variable
`x_{u^A}` of type `τ(A)` (using odd variable ids `2 * u.id + 1` to keep them distinct). -/
def assumpRealizerVar (u : AssumpVar) : Var :=
  ⟨2 * u.id + 1, tau u.formula⟩

/-- Definition 4.3 (Extracted terms for core axioms `⟦A⟧`, p. 21). -/
def extractAxiom (ax : CoreAxiom) : Term :=
  match ax with
  | .ax3 A B C => .const (.prodIntro (tau A) (tau B) (tau C))
  | .ax4_left A₀ A₁ => .const (.fst (tau A₀) (tau A₁))
  | .ax4_right A₀ A₁ => .const (.snd (tau A₀) (tau A₁))
  | .ax5 A B => .const (.tensorIntro (tau A) (tau B))
  | .ax6 A B C => .const (.tensorElim (tau A) (tau B) (tau C))
  | .ax7_left A₀ A₁ => .const (.inl (tau A₀) (tau A₁))
  | .ax7_right A₀ A₁ => .const (.inr (tau A₀) (tau A₁))
  | .ax8 A B C =>
      let ρ := tau A
      let σ := tau B
      let τ := tau C
      let z₁ : Var := ⟨0, .prod (.lolli ρ τ) (.lolli σ τ)⟩
      let z₂ : Var := ⟨1, .sum ρ σ⟩
      .lam z₁ (.lam z₂ (.app (.app (.const (.sumElim ρ σ τ)) (.var z₂)) (.var z₁)))
  | .ax9 _ A => Term.idTerm (tau A)
  | .ax10 _ A B =>
      let x : Var := ⟨0, tau A⟩
      let f : Var := ⟨1, .lolli (tau A) (tau B)⟩
      .lam x (.lam f (.app (.var f) (.var x)))
  | .ax16 ρ _ _ => Term.idTerm ρ
  | .ax20_imp ρ σ _ _ => Term.idTerm (.lolli ρ σ)
  | .ax20_mpr ρ σ _ _ => Term.idTerm (.lolli ρ σ)
  | .ax21_imp ρ σ _ => Term.idTerm (.prod ρ σ)
  | .ax21_mpr ρ σ _ => Term.idTerm (.prod ρ σ)
  | .ax22 c => .const c
  | .ax23 ρ σ _ _ _ A =>
      let τ := tau A
      let f : Var := ⟨0, .lolli ρ (.lolli σ τ)⟩
      let z : Var := ⟨1, .tensor ρ σ⟩
      .lam f (.lam z (.app (.app (.const (.tensorElim ρ σ τ)) (.var z)) (.var f)))
  | .ax24 ρ σ _ _ _ A =>
      let τ := tau A
      let z₁ : Var := ⟨0, .prod (.lolli ρ τ) (.lolli σ τ)⟩
      let z₂ : Var := ⟨1, .sum ρ σ⟩
      .lam z₁ (.lam z₂ (.app (.app (.const (.sumElim ρ σ τ)) (.var z₂)) (.var z₁)))
  | other => dummyTerm (tau other.formula)

/-- Definition 4.3 (Extracted terms `⟦M⟧`, pp. 20–21):
- `⟦u^A⟧ := x_u^{τ(A)}`
- `⟦λu^A M^B⟧ := λx_u^{τ(A)} ⟦M⟧`
- `⟦M^{A→B} N⟧ := ⟦M⟧ ⟦N⟧`
- `⟦λx^ρ M^A⟧ := ⟦M⟧`
- `⟦M^{∀x^ρ A} r⟧ := ⟦M⟧`
- `⟦N^{E_{L(ρ)}(t)} {M}⟧ := ⟦N⟧ {⟦M⟧}`. -/
def extractProof : ProofTerm → Term
  | .assump u => .var (assumpRealizerVar u)
  | .ax c => extractAxiom c
  | .lamAssump u M => .lam (assumpRealizerVar u) (extractProof M)
  | .lamTerm _ M => extractProof M
  | .appProof M N => .app (extractProof M) (extractProof N)
  | .appTerm M _ => extractProof M
  | .ind N M => .iter (extractProof N) (extractProof M)

/-- Intrinsic type inference `inferType r` for raw terms (since variables and constants carry
their explicit types in `ABHS2004`). -/
def inferType : Term → Option Ty
  | .var x => some x.ty
  | .const c => some c.ty
  | .lam x r =>
      match inferType r with
      | some σ => some (.lolli x.ty σ)
      | none => none
  | .app r _ =>
      match inferType r with
      | some (.lolli _ σ) => some σ
      | _ => none
  | .iter _ s =>
      match inferType s with
      | some (.lolli .diamond (.lolli _ (.lolli τ _))) => some (.lolli τ τ)
      | _ => none

/-- Definition 4.4 (p. 22): Cleaned variable `x̃^{c(ρ)}` associated with `x^ρ`. -/
def cleanVar (x : Var) : Var :=
  ⟨x.id, cleanTy x.ty⟩

/-- Definition 4.4 (p. 22): Cleaning `c(c)` for constants `c^ρ`. -/
def cleanConst (c : Const) : Term :=
  if cleanTy c.ty == .unit then
    .const .eps
  else
    match c with
    | .eps => .const .eps
    | .nil ρ => .const (.nil (cleanTy ρ))
    | .cons ρ =>
        let cρ := cleanTy ρ
        if cρ == .unit then
          let d : Var := ⟨0, .diamond⟩
          let l : Var := ⟨1, Ty.nat⟩
          .lam d (.lam l (Term.succNat (.var d) (.var l)))
        else
          .const (.cons cρ)
    | .tensorIntro ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cρ == .unit then Term.idTerm cσ
        else if cσ == .unit then Term.idTerm cρ
        else .const (.tensorIntro cρ cσ)
    | .tensorElim ρ σ τ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        let cτ := cleanTy τ
        if cρ == .unit && cσ == .unit then
          Term.idTerm cτ
        else if cρ == .unit then
          let x : Var := ⟨0, cσ⟩
          let f : Var := ⟨1, .lolli cσ cτ⟩
          .lam x (.lam f (.app (.var f) (.var x)))
        else if cσ == .unit then
          let x : Var := ⟨0, cρ⟩
          let f : Var := ⟨1, .lolli cρ cτ⟩
          .lam x (.lam f (.app (.var f) (.var x)))
        else
          .const (.tensorElim cρ cσ cτ)
    | .prodIntro ρ σ τ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        let cτ := cleanTy τ
        if cρ == .unit then
          if cτ == .unit then Term.idTerm cσ
          else
            let g : Var := ⟨0, .lolli cτ cσ⟩
            let z : Var := ⟨1, cτ⟩
            .lam g (.lam z (.app (.var g) (.var z)))
        else if cσ == .unit then
          if cτ == .unit then Term.idTerm cρ
          else
            let f : Var := ⟨0, .lolli cτ cρ⟩
            let z : Var := ⟨1, cτ⟩
            .lam f (.lam z (.app (.var f) (.var z)))
        else if cτ == .unit then
          let x : Var := ⟨0, cρ⟩
          let y : Var := ⟨1, cσ⟩
          let u₁ : Var := ⟨2, .unit⟩
          let u₂ : Var := ⟨3, .unit⟩
          .lam x (.lam y
            (.app (.app (.app (.const (.prodIntro cρ cσ .unit))
              (.lam u₁ (.var x)))
              (.lam u₂ (.var y)))
              (.const .eps)))
        else
          .const (.prodIntro cρ cσ cτ)
    | .fst ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cσ == .unit then Term.idTerm cρ
        else .const (.fst cρ cσ)
    | .snd ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cρ == .unit then Term.idTerm cσ
        else .const (.snd cρ cσ)
    | .inl ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cρ == .unit then .app (.const (.inl .unit cσ)) (.const .eps)
        else .const (.inl cρ cσ)
    | .inr ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cσ == .unit then .app (.const (.inr cρ .unit)) (.const .eps)
        else .const (.inr cρ cσ)
    | .sumElim ρ σ τ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        let cτ := cleanTy τ
        let branchL := if cρ == .unit then cτ else .lolli cρ cτ
        let branchR := if cσ == .unit then cτ else .lolli cσ cτ
        if cρ == .unit && cσ == .unit then
          let s : Var := ⟨0, .sum .unit .unit⟩
          let p : Var := ⟨1, .prod cτ cτ⟩
          let u₁ : Var := ⟨2, .unit⟩
          let u₂ : Var := ⟨3, .unit⟩
          let q : Var := ⟨4, .prod cτ cτ⟩
          let adaptedPair :=
            Term.app
              (.app (.app (.const (.prodIntro (.lolli .unit cτ) (.lolli .unit cτ) (.prod cτ cτ)))
                (.lam q (.lam u₁ (.app (.const (.fst cτ cτ)) (.var q)))))
                (.lam q (.lam u₂ (.app (.const (.snd cτ cτ)) (.var q)))))
              (.var p)
          .lam s (.lam p (.app (.app (.const (.sumElim .unit .unit cτ)) (.var s)) adaptedPair))
        else if cρ == .unit then
          let s : Var := ⟨0, .sum .unit cσ⟩
          let p : Var := ⟨1, .prod branchL branchR⟩
          let u₁ : Var := ⟨2, .unit⟩
          let q : Var := ⟨3, .prod branchL branchR⟩
          let adaptedPair :=
            Term.app
              (.app (.app (.const (.prodIntro (.lolli .unit cτ) branchR (.prod branchL branchR)))
                (.lam q (.lam u₁ (.app (.const (.fst branchL branchR)) (.var q)))))
                (.lam q (.app (.const (.snd branchL branchR)) (.var q))))
              (.var p)
          .lam s (.lam p (.app (.app (.const (.sumElim .unit cσ cτ)) (.var s)) adaptedPair))
        else if cσ == .unit then
          let s : Var := ⟨0, .sum cρ .unit⟩
          let p : Var := ⟨1, .prod branchL branchR⟩
          let u₂ : Var := ⟨2, .unit⟩
          let q : Var := ⟨3, .prod branchL branchR⟩
          let adaptedPair :=
            Term.app
              (.app (.app (.const (.prodIntro branchL (.lolli .unit cτ) (.prod branchL branchR)))
                (.lam q (.app (.const (.fst branchL branchR)) (.var q))))
                (.lam q (.lam u₂ (.app (.const (.snd branchL branchR)) (.var q)))))
              (.var p)
          .lam s (.lam p (.app (.app (.const (.sumElim cρ .unit cτ)) (.var s)) adaptedPair))
        else
          .const (.sumElim cρ cσ cτ)

/-- Definition 4.4 (Cleaning of terms `c(r)`, p. 22). -/
def cleanTerm (r : Term) : Term :=
  match inferType r with
  | some ρ =>
      if cleanTy ρ == .unit then
        .const .eps
      else
        match r with
        | .var x => .var (cleanVar x)
        | .const c => cleanConst c
        | .lam x body =>
            if cleanTy x.ty == .unit then
              cleanTerm body
            else
              .lam (cleanVar x) (cleanTerm body)
        | .app t s =>
            match inferType s with
            | some σ =>
                if cleanTy σ == .unit then
                  cleanTerm t
                else
                  .app (cleanTerm t) (cleanTerm s)
            | none => .app (cleanTerm t) (cleanTerm s)
        | .iter t s => .iter (cleanTerm t) (cleanTerm s)
  | none => r

/-- Section 4.3 (p. 23): Cleaned extracted term `⟦M⟧^c := c(⟦M⟧)`. -/
def extractCleaned (M : ProofTerm) : Term :=
  cleanTerm (extractProof M)

/-- Section 4.3 (p. 23): Uncleaned context extraction `⟦Π⟧ := {x_u^{τ(A)} | u^A ∈ Π}`. -/
def extractCtx (Δ : ProofContext) : List Var :=
  Δ.map assumpRealizerVar

/-- Section 4.3 (p. 23): Cleaned context extraction
`⟦Π⟧^c := {x̃_u^{τ^c(A)} | u^A ∈ Π, τ^c(A) ≠ U}`. -/
def extractCleanCtx (Δ : ProofContext) : List Var :=
  (Δ.filter (fun u => tauClean u.formula != .unit)).map (fun u => cleanVar (assumpRealizerVar u))

/-- Section 4.3 (Theorem 4.9, p. 24): Realizability context mapping each assumption `u^B ∈ Π`
to an assumption variable `ũ^{x_u mr B}`. -/
def mrContext (Δ : ProofContext) : ProofContext :=
  Δ.map (fun u => ⟨u.id, mr (.var (assumpRealizerVar u)) u.formula⟩)

/-- A derivation `M` (with passive context `Π` and active context `Γ`) is almost closed
if every assumption in `Π ∪ Γ` has cleaned realizer type `⋄` or `U` (in particular, when
`Π = []` and `Γ = []`, or when `⟦Γ⟧^c` contains only variables of type `⋄`, Corollary 4.11, p. 26). -/
def IsAlmostClosedDerivation (Δ Γ : ProofContext) : Prop :=
  (∀ v ∈ extractCleanCtx Δ, v.ty = .diamond) ∧
  (∀ v ∈ extractCleanCtx Γ, v.ty = .diamond)

/-- Freshness condition from Section 4.2 (p. 20: "For each variable `u^A` we choose a unique
variable `x_{u^A}` of type `τ(A)` that is sufficiently different to all variables used so far"):
all assumption variables in `Δ`, `Γ`, and `M` have pairwise distinct ids when their formulas
differ, and their chosen realizer variables `x_{u^A}` do not occur free in `A` or in the
formulas of `Δ ∪ Γ`. -/
def FreshRealizerVars (Δ Γ : ProofContext) (M : ProofTerm) (A : Formula) : Prop :=
  let allU := Δ ++ Γ ++ allAssumpVars M
  (∀ u ∈ allU, ∀ v ∈ allU, u.id = v.id → u = v) ∧
  (∀ u ∈ allU, assumpRealizerVar u ∉ freeVarsFormula A) ∧
  (∀ u ∈ allU, ∀ w ∈ Δ ++ Γ, assumpRealizerVar u ∉ freeVarsFormula w.formula)

end ABHS2004

namespace ABHS2004.Audit

def badAx : CoreAxiom := .ax16 .diamond (.var ⟨0, .diamond⟩) (.var ⟨0, .diamond⟩)

theorem badAx_valid : badAx.IsValid := by
  exact ⟨WeaklyTyped.var _, WeaklyTyped.var _⟩

theorem badAx_derivable : Derives [] [] (.ax badAx) badAx.formula := by
  apply Derives.axiomRule
  · simp [DisjointProofCtx]
  · exact badAx_valid

theorem badAx_fresh : FreshRealizerVars [] [] (.ax badAx) badAx.formula := by
  simp [FreshRealizerVars, allAssumpVars]

theorem badAx_extraction_not_typed :
    ¬ WeaklyTyped (extractProof (.ax badAx)) (tau badAx.formula) := by
  intro h
  change WeaklyTyped (.lam ⟨0, .diamond⟩ (.var ⟨0, .diamond⟩))
    (.lolli .unit (.lolli .diamond .diamond)) at h
  cases h

#print axioms badAx_extraction_not_typed
#print axioms badAx_derivable
#print axioms badAx_fresh
end ABHS2004.Audit
