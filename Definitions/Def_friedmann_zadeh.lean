import Definitions.Def_friedmann_simplex
import Definitions.Def_friedmann_parity
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

/-! The explicit two-centre counter of Disser--Friedmann--Hopp.
Indices here start at zero; the source's level i is represented by i-1.
These definitions contain no lower-bound, progress, or counter-simulation fields.
-/
namespace FriedmannZadeh

open scoped BigOperators Matrix

abbrev Centre (n : ℕ) := {c : Fin n × Fin 2 // c.1.val + c.2.val < n}

inductive Node (n : ℕ) where
  | entry : Fin n → Node n
  | selector : Fin n → Node n
  | cycle : Centre n → Fin 2 → Node n
  | escape : Centre n → Fin 2 → Node n
  | upper : Centre n → Node n
  | centre : Centre n → Node n
  | reward : Centre n → Node n
  | sink : Node n
  deriving DecidableEq, Fintype

abbrev Strategy (n : ℕ) := Node n → Node n
abbrev Edge (n : ℕ) := Node n × Node n

def entryAt (n i : ℕ) : Node n :=
  if h : i < n then .entry ⟨i,h⟩ else .sink

def selectorAt (n i : ℕ) : Node n :=
  if h : i < n then .selector ⟨i,h⟩ else .sink

def centreAt (n i j : ℕ) : Node n :=
  if h : i < n ∧ j < 2 ∧ i + j < n then
    .centre ⟨(⟨i,h.1⟩,⟨j,h.2.1⟩),h.2.2⟩
  else .sink

def cycleAt (n i j k : ℕ) : Node n :=
  if h : i < n ∧ j < 2 ∧ i + j < n ∧ k < 2 then
    .cycle ⟨(⟨i,h.1⟩,⟨j,h.2.1⟩),h.2.2.1⟩ ⟨k,h.2.2.2⟩
  else .sink

def upperAt (n i j : ℕ) : Node n :=
  if h : i < n ∧ j < 2 ∧ i + j < n then
    .upper ⟨(⟨i,h.1⟩,⟨j,h.2.1⟩),h.2.2⟩
  else .sink

def rewardAt (n i j : ℕ) : Node n :=
  if h : i < n ∧ j < 2 ∧ i + j < n then
    .reward ⟨(⟨i,h.1⟩,⟨j,h.2.1⟩),h.2.2⟩
  else .sink

def owned {n : ℕ} : Node n → Bool
  | .centre _ | .reward _ | .sink => false
  | _ => true

def priority {n : ℕ} : Node n → ℕ
  | .entry _ | .cycle _ _ | .escape _ _ => 3
  | .selector i => 11 + 2 * i.val
  | .upper c => 10 - 2 * c.val.2.val
  | .centre c => 6 - 2 * c.val.2.val
  | .reward c => 12 + 2 * c.val.1.val
  | .sink => 1

def successors {n : ℕ} : Node n → Finset (Node n)
  | .entry i => {.selector i, entryAt n (i.val + 1)}
  | .selector i => if h : i.val + 1 < n then
      {.centre ⟨(i,0),by simp⟩, .centre ⟨(i,1),by simpa using h⟩}
    else {.centre ⟨(i,0),by simp⟩}
  | .cycle c k => {.centre c, .escape c k}
  | .escape _ _ => {entryAt n 1, selectorAt n 0}
  | .upper c => {.reward c, entryAt n 0}
  | .centre c => {.cycle c 0, .cycle c 1, .upper c}
  | .reward c => {if c.val.2.val = 0 then entryAt n (c.val.1.val + 2)
      else selectorAt n (c.val.1.val + 1)}
  | .sink => {.sink}

def legal {n : ℕ} (σ : Strategy n) : Prop :=
  ∀ v, owned v = true → σ v ∈ successors v

def initial {n : ℕ} : Strategy n
  | .entry i => entryAt n (i.val + 1)
  | .selector i => .centre ⟨(i,0),by simp⟩
  | .cycle c k => .escape c k
  | .escape _ _ => entryAt n 1
  | .upper c => if c.val.2.val = 0 then .reward c else entryAt n 0
  | v => v

def closed {n : ℕ} (σ : Strategy n) (i j : ℕ) : Prop :=
  i < n ∧ j < 2 ∧ i + j < n ∧
  σ (cycleAt n i j 0) = centreAt n i j ∧
  σ (cycleAt n i j 1) = centreAt n i j

noncomputable def bitState {n : ℕ} (σ : Strategy n) : ℕ → Bool := by
  classical
  exact fun i => Nat.rec (motive := fun _ => Bool) false
    (fun k prev => decide (closed σ (n - 1 - k) prev.toNat)) (n - i)

/-- The source's seven successive edge classes, in order of precedence. -/
noncomputable def edgeGroup {n : ℕ} (σ : Strategy n) (e : Edge n) : ℕ :=
  match e.1 with
  | .selector _ => 0
  | .cycle c _ => if e.2 = .centre c then 6 else 1
  | .escape c k => if σ (.cycle c k) = .centre c then 2 else 5
  | .entry _ => 3
  | .upper _ => 4
  | _ => 7

def level {n : ℕ} : Node n → ℕ
  | .entry i | .selector i => i.val
  | .cycle c _ | .escape c _ | .upper c | .centre c | .reward c => c.val.1.val
  | .sink => n

def centreIndex {n : ℕ} : Node n → ℕ
  | .cycle c _ | .escape c _ | .upper c | .centre c | .reward c => c.val.2.val
  | _ => 0

def lastIndex {n : ℕ} : Node n → ℕ
  | .cycle _ k | .escape _ k => k.val
  | _ => 0

/-- Closed, half-open towards a specified vertex, and other centre states.
This is a classification of the current strategy, not an assumed phase. -/
noncomputable def halfopenTo {n : ℕ} (σ : Strategy n) (i j : ℕ)
    (target : Node n) : Prop :=
  ∃ k : Fin 2, σ (cycleAt n i j k.val) = centreAt n i j ∧
    σ (cycleAt n i j (1 - k.val)) ≠ centreAt n i j ∧
    σ (match cycleAt n i j (1 - k.val) with
       | .cycle c l => .escape c l | _ => .sink) = target

inductive Context where | parity | mdp
  deriving DecidableEq

noncomputable def activeIndex {n : ℕ} (σ : Strategy n) (i : ℕ) : ℕ :=
  (bitState σ (i + 1)).toNat

/-- Strict part of the source's within-class ordering. The target parameter is
the direction of the current transition; concrete runs determine it from the
better of b₂ and g₁. Its equivalence to the source phase convention is a target.
-/
noncomputable def internalBefore {n : ℕ} (ctx : Context) (σ : Strategy n)
    (target : Node n) (e f : Edge n) : Prop :=
  let i := level e.1; let k := level f.1
  let j := centreIndex e.1; let l := centreIndex f.1
  let x := lastIndex e.1; let y := lastIndex f.1
  let active := fun a b => b = activeIndex σ a
  let preferred := fun a b => if ctx = .parity then b = 0 else active a b
  match edgeGroup σ e with
  | 4 => k < i
  | 5 => k < i ∨ (i = k ∧ preferred i j ∧ ¬ preferred k l)
  | 2 => k < i ∨ (i = k ∧
      ((closed σ i j ∧ ¬ closed σ k l) ∨
       (¬ closed σ i j ∧ ¬ closed σ k l ∧
         halfopenTo σ i j target ∧ ¬ halfopenTo σ k l target) ∨
       ((closed σ i j ↔ closed σ k l) ∧
        (halfopenTo σ i j target ↔ halfopenTo σ k l target) ∧
        preferred i j ∧ ¬ preferred k l)))
  | 6 =>
      let otherClosed := fun a b c => σ (cycleAt n a b (1 - c)) = centreAt n a b
      (¬ otherClosed i j x ∧ otherClosed k l y) ∨
      ((otherClosed i j x ↔ otherClosed k l y) ∧
        ((bitState σ i = false ∧ bitState σ k = true) ∨
         (bitState σ i = bitState σ k ∧
           (i < k ∨ (i = k ∧
             ((active i j ∧ ¬ active k l) ∨
              ((active i j ↔ active k l) ∧ x < y)))))))
  | _ => False

noncomputable def before {n : ℕ} (ctx : Context) (σ : Strategy n)
    (target : Node n) (e f : Edge n) : Prop :=
  edgeGroup σ e < edgeGroup σ f ∨
    (edgeGroup σ e = edgeGroup σ f ∧ internalBefore ctx σ target e f)

/-- A fixed total ordering of labels completes any ties left unspecified by
the source. Only a linear extension of the source preorder is admitted. -/
noncomputable def linearExtension {n : ℕ} (ctx : Context) (σ : Strategy n)
    (target : Node n) (rank : Edge n → ℕ) : Prop :=
  Function.Injective rank ∧ ∀ e f, before ctx σ target e f → rank e < rank f

/-- A concrete completion of the source preorder. For a strict partial order,
predecessor cardinality increases on every ordered pair; the final label breaks
ties. Hence evaluation requires only polynomially many pair comparisons. -/
noncomputable def sourceRank {n : ℕ} (ctx : Context) (σ : Strategy n)
    (target : Node n) (e : Edge n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f => before ctx σ target f e)).card *
    Fintype.card (Edge n) + (Fintype.equivFin (Edge n) e).val

def parityGame (n : ℕ) : FriedmannParity.Game (Node n) where
  owner v := !owned v
  priority := priority
  edge v w := w ∈ successors v

/-- An integer radix realizes lexicographic comparison of priority
multiplicities. This totalizes the source's set comparison for its actual
repeated-priority presentation; equal multiplicities are identified. -/
noncomputable def pgPlayScore {n : ℕ} (σ τ : Strategy n) (v : Node n) : ℤ := by
  classical
  let a := FriedmannParity.playValue (parityGame n) σ τ v
  let M : ℤ := Fintype.card (Node n) + 1
  let W : ℤ := ∑ w ∈ a.path, (-M) ^ priority w
  let H : ℤ := 2 * (Fintype.card (Node n) : ℤ) * M ^ (2 * n + 12) + 1
  let L : ℤ := if a.cyclePriority % 2 = 0 then -(a.length : ℤ) else a.length
  exact (FriedmannParity.reward a.cyclePriority * H + W) * M + L

noncomputable def pgValue {n : ℕ} (σ : Strategy n) (v : Node n) : ℤ := by
  classical
  let scores := (Finset.univ.filter
    (fun τ : Strategy n => FriedmannParity.Legal (parityGame n) true τ)).image
      (fun τ => pgPlayScore σ τ v)
  exact if h : scores.Nonempty then scores.min' h else 0

noncomputable def pgBetter {n : ℕ} (σ : Strategy n) (v w : Node n) : Prop :=
  pgValue σ v < pgValue σ w

noncomputable def pgImproving {n : ℕ} (σ : Strategy n) (e : Edge n) : Prop :=
  owned e.1 = true ∧ e.2 ∈ successors e.1 ∧ pgBetter σ (σ e.1) e.2

noncomputable def pgTarget {n : ℕ} (σ : Strategy n) : Node n :=
  by
    classical
    exact if pgBetter σ (entryAt n 1) (selectorAt n 0)
      then selectorAt n 0 else entryAt n 1

structure CounterState (n : ℕ) where
  strategy : Strategy n
  count : Edge n → ℕ

noncomputable def exceptional {n : ℕ} (improving : Edge n → Prop)
    (count : Edge n → ℕ) : Prop :=
  let e := (entryAt n 0,entryAt n 1)
  let f := (upperAt n 0 1,rewardAt n 0 1)
  count e = 0 ∧ count f = 0 ∧ improving e ∧ improving f

noncomputable def counterRank {n : ℕ} (ctx : Context) (s : CounterState n)
    (target : Node n) (improving : Edge n → Prop) (e : Edge n) : ℕ := by
  classical
  exact if exceptional improving s.count ∧ e = (upperAt n 0 1,rewardAt n 0 1)
    then 0 else sourceRank ctx s.strategy target e + 1

noncomputable def counterChoice {n : ℕ} (ctx : Context) (s : CounterState n)
    (target : Node n) (improving : Edge n → Prop) (e : Edge n) : Prop :=
  improving e ∧ (∀ f, improving f → s.count e ≤ s.count f) ∧
    ∀ f, improving f → s.count f = s.count e →
      counterRank ctx s target improving e ≤ counterRank ctx s target improving f

def updateCounter {n : ℕ} (s : CounterState n) (e : Edge n) : CounterState n where
  strategy := Function.update s.strategy e.1 e.2
  count := Function.update s.count e (s.count e + 1)

noncomputable def pgStep {n : ℕ} (s s' : CounterState n) : Prop :=
  ∃ e, counterChoice .parity s (pgTarget s.strategy) (pgImproving s.strategy) e ∧
    s' = updateCounter s e

noncomputable def pgRun {n : ℕ} (s : ℕ → CounterState n) (T : ℕ) : Prop :=
  (s 0).strategy = initial ∧ (∀ e, (s 0).count e = 0) ∧
  (∀ t, t ≤ T → legal (s t).strategy) ∧
  (∀ t, t < T → pgStep (s t) (s (t + 1))) ∧
  ∀ e, ¬ pgImproving (s T).strategy e

/-- Deterministic reward vertices are retained as single-action vertices.
Figure 5 assigns nonzero rewards to g, s, h and zero to the unlabelled vertices.
This avoids discarding the high reward at h when eliminating deterministic
random vertices. -/
def control {n : ℕ} : Node n → Bool
  | .centre _ | .sink => false
  | _ => true

def mdpReward {n : ℕ} (N : ℕ) : Node n → ℚ
  | .selector i => (-(N : ℚ)) ^ (11 + 2 * i.val)
  | .upper c => (-(N : ℚ)) ^ (10 - 2 * c.val.2.val)
  | .reward c => (-(N : ℚ)) ^ (12 + 2 * c.val.1.val)
  | _ => 0

noncomputable def transition {n : ℕ} (ε : ℚ) (σ : Strategy n)
    (v w : Node n) : ℚ :=
  match v with
  | .centre c => if w = .upper c then ε
      else if w = .cycle c 0 ∨ w = .cycle c 1 then (1 - ε) / 2 else 0
  | .reward c => if w ∈ successors (.reward c) then 1 else 0
  | .sink => if w = .sink then 1 else 0
  | _ => if σ v = w then 1 else 0

noncomputable def policyMatrix {n : ℕ} (ε : ℚ) (σ : Strategy n) :
    Matrix (Node n) (Node n) ℚ :=
  fun v w => if v = .sink then (if w = .sink then 1 else 0)
    else (if v = w then 1 else 0) - transition ε σ v w

noncomputable def proper {n : ℕ} (ε : ℚ) (σ : Strategy n) : Prop :=
  (policyMatrix ε σ).det ≠ 0

noncomputable def mdpValue {n : ℕ} (N : ℕ) (ε : ℚ) (σ : Strategy n) : Node n → ℚ :=
  (policyMatrix ε σ)⁻¹ *ᵥ mdpReward N

noncomputable def mdpImproving {n : ℕ} (N : ℕ) (ε : ℚ)
    (σ : Strategy n) (e : Edge n) : Prop :=
  owned e.1 = true ∧ e.2 ∈ successors e.1 ∧
    mdpValue N ε σ (σ e.1) < mdpValue N ε σ e.2

noncomputable def mdpTarget {n : ℕ} (N : ℕ) (ε : ℚ) (σ : Strategy n) : Node n :=
  if mdpValue N ε σ (entryAt n 1) < mdpValue N ε σ (selectorAt n 0)
    then selectorAt n 0 else entryAt n 1

noncomputable def mdpStep {n : ℕ} (N : ℕ) (ε : ℚ)
    (s s' : CounterState n) : Prop :=
  ∃ e, counterChoice .mdp s (mdpTarget N ε s.strategy)
      (mdpImproving N ε s.strategy) e ∧ s' = updateCounter s e

noncomputable def mdpRun {n : ℕ} (N : ℕ) (ε : ℚ)
    (s : ℕ → CounterState n) (T : ℕ) : Prop :=
  (s 0).strategy = initial ∧ (∀ e, (s 0).count e = 0) ∧
  (∀ t, t ≤ T → legal (s t).strategy ∧ proper ε (s t).strategy) ∧
  (∀ t, t < T → mdpStep N ε (s t) (s (t + 1))) ∧
  ∀ e, ¬ mdpImproving N ε (s T).strategy e

structure LPState (m n : ℕ) where
  basis : FriedmannSimplex.Basis m n
  count : Fin n → ℕ

noncomputable def leastEntered {m n : ℕ} (P : FriedmannSimplex.LP m n)
    (s : LPState m n) (j : Fin n) : Prop :=
  FriedmannSimplex.improving P s.basis j ∧
    ∀ k, FriedmannSimplex.improving P s.basis k → s.count j ≤ s.count k

noncomputable def lpStep {m n : ℕ} (P : FriedmannSimplex.LP m n)
    (tie : LPState m n → Fin n → ℕ) (s s' : LPState m n) : Prop :=
  ∃ j, leastEntered P s j ∧
    (∀ k, leastEntered P s k → tie s j ≤ tie s k) ∧
    FriedmannSimplex.pivot P s.basis j s'.basis ∧
    s'.count = Function.update s.count j (s.count j + 1)

noncomputable def lpRun {m n : ℕ} (P : FriedmannSimplex.LP m n)
    (tie : LPState m n → Fin n → ℕ) (s : ℕ → LPState m n) (T : ℕ) : Prop :=
  FriedmannSimplex.basicFeasible P (s 0).basis ∧
    (∀ j, (s 0).count j = 0) ∧
    (∀ t, t < T → lpStep P tie (s t) (s (t + 1))) ∧
    FriedmannSimplex.optimalBasis P (s T).basis

abbrev Decision (n : ℕ) := {v : Node n // control v = true}

abbrev Action (n : ℕ) :=
  {e : Edge n // control e.1 = true ∧ e.2 ∈ successors e.1}

noncomputable def rowCount (n : ℕ) : ℕ := Fintype.card (Decision n)
noncomputable def columnCount (n : ℕ) : ℕ := Fintype.card (Action n)

noncomputable def rowAt (n : ℕ) : Fin (rowCount n) ≃ Decision n :=
  (Fintype.equivFin (Decision n)).symm

noncomputable def columnAt (n : ℕ) : Fin (columnCount n) ≃ Action n :=
  (Fintype.equivFin (Action n)).symm

/-- Eliminate a random centre immediately after an action, while retaining all
deterministic reward vertices as single-action decision vertices. Terminal sink
visits have zero continuing occupancy. -/
def afterAction {n : ℕ} (ε : ℚ) (w u : Node n) : ℚ :=
  match w with
  | .centre c => if u = .upper c then ε
      else if u = .cycle c 0 ∨ u = .cycle c 1 then (1 - ε) / 2 else 0
  | .sink => 0
  | _ => if w = u then 1 else 0

/-- Occupancy LP, with one unit of input flow at each nonterminal decision
vertex. Coefficients are generated from the explicit graph and probabilities.
-/
noncomputable def inducedLP (n N : ℕ) (ε : ℚ) :
    FriedmannSimplex.LP (rowCount n) (columnCount n) where
  A i j := (if (columnAt n j).val.1 = (rowAt n i).val then 1 else 0) -
    afterAction ε (columnAt n j).val.2 (rowAt n i).val
  b _ := 1
  c j := mdpReward N (columnAt n j).val.1

noncomputable def basisPolicy {n : ℕ}
    (B : FriedmannSimplex.Basis (rowCount n) (columnCount n)) : Strategy n :=
  fun v => if h : ∃ i, (columnAt n (B i)).val.1 = v then
    (columnAt n (B (Classical.choose h))).val.2 else initial v

noncomputable def represents {n : ℕ} (σ : Strategy n)
    (B : FriedmannSimplex.Basis (rowCount n) (columnCount n)) : Prop :=
  ∀ i, (columnAt n (B i)).val.1 = (rowAt n i).val ∧
    (columnAt n (B i)).val.2 =
      (match (rowAt n i).val with
        | .reward c => if c.val.2.val = 0 then entryAt n (c.val.1.val + 2)
            else selectorAt n (c.val.1.val + 1)
        | v => σ v)

noncomputable def actionCounts {n : ℕ}
    (s : LPState (rowCount n) (columnCount n)) (e : Edge n) : ℕ :=
  if h : ∃ j, (columnAt n j).val = e then s.count (Classical.choose h) else 0

noncomputable def inducedTie (n N : ℕ) (ε : ℚ)
    (s : LPState (rowCount n) (columnCount n)) (j : Fin (columnCount n)) : ℕ :=
  let σ := basisPolicy s.basis
  let cs : CounterState n := ⟨σ, actionCounts s⟩
  let improving := fun e => ∃ k, (columnAt n k).val = e ∧
    FriedmannSimplex.improving (inducedLP n N ε) s.basis k
  counterRank .mdp cs (mdpTarget N ε σ) improving (columnAt n j).val

noncomputable def InducedSimplexRun (n N : ℕ) (ε : ℚ)
    (s : ℕ → LPState (rowCount n) (columnCount n)) (T : ℕ) : Prop :=
  lpRun (inducedLP n N ε) (inducedTie n N ε) s T ∧ represents initial (s 0).basis

noncomputable def Parameters (n N : ℕ) (ε : ℚ) : Prop :=
  0 < n ∧ 7 * n ≤ N ∧ 0 < ε ∧ ε < ((N : ℚ) ^ (2 * n + 11))⁻¹

noncomputable def ParityLowerBound (n : ℕ) : Prop :=
  (∃ T s, pgRun (n := n) s T) ∧ ∀ T s, pgRun (n := n) s T → 2 ^ n ≤ T

noncomputable def MDPLowerBound (n N : ℕ) (ε : ℚ) : Prop :=
  (∃ T s, mdpRun (n := n) N ε s T) ∧
    ∀ T s, mdpRun (n := n) N ε s T → 2 ^ n ≤ T

noncomputable def SimplexLowerBound (n N : ℕ) (ε : ℚ) : Prop :=
  (∃ T s, InducedSimplexRun n N ε s T) ∧
    ∀ T s, InducedSimplexRun n N ε s T → 2 ^ n ≤ T

noncomputable def Main : Prop :=
  ∀ n N ε, Parameters n N ε →
    ParityLowerBound n ∧ MDPLowerBound n N ε ∧ SimplexLowerBound n N ε

noncomputable def priorityCount {n : ℕ} (S : Finset (Node n)) (p : ℕ) : ℕ :=
  (S.filter (fun v => priority v = p)).card

noncomputable def countLT {n : ℕ} (S T : Finset (Node n)) : Prop :=
  ∃ p, (∀ q, p < q → priorityCount S q = priorityCount T q) ∧
    ((p % 2 = 0 ∧ priorityCount S p < priorityCount T p) ∨
      (p % 2 = 1 ∧ priorityCount T p < priorityCount S p))

noncomputable def countEquivalent {n : ℕ} (S T : Finset (Node n)) : Prop :=
  ∀ p, priorityCount S p = priorityCount T p

noncomputable def countValueLT {n : ℕ}
    (a b : FriedmannParity.Valuation (Node n)) : Prop :=
  FriedmannParity.reward a.cyclePriority < FriedmannParity.reward b.cyclePriority ∨
    (a.cyclePriority = b.cyclePriority ∧ countLT a.path b.path) ∨
    (a.cyclePriority = b.cyclePriority ∧ countEquivalent a.path b.path ∧
      ((a.cyclePriority % 2 = 1 ∧ a.length < b.length) ∨
        (a.cyclePriority % 2 = 0 ∧ b.length < a.length)))

def PgSingleSwitch {n : ℕ} (σ ρ : Strategy n) : Prop :=
  ∃ e, pgImproving σ e ∧ ρ = Function.update σ e.1 e.2

def PgReachable {n : ℕ} (σ : Strategy n) : Prop :=
  Relation.ReflTransGen PgSingleSwitch initial σ

noncomputable def PgCounterstrategy {n : ℕ} (σ τ : Strategy n) : Prop :=
  FriedmannParity.Legal (parityGame n) true τ ∧
    ∀ v, pgPlayScore σ τ v = pgValue σ v

noncomputable def nextLevel (n b : ℕ) : ℕ := by
  classical
  let S := (Finset.range n).filter (fun i => (b+1).testBit i)
  exact if h : S.Nonempty then S.min' h else 0

noncomputable def Canonical {n : ℕ} (ctx : Context) (b : ℕ)
    (σ : Strategy n) : Prop :=
  b < 2 ^ n ∧ legal σ ∧
  (∀ c k, σ (.escape c k) =
    (if b.testBit 0 then selectorAt n 0 else entryAt n 1)) ∧
  (∀ i : Fin n,
    let j := (b.testBit (i.val+1)).toNat
    if b.testBit i.val then
      σ (.entry i) = .selector i ∧ closed σ i.val j ∧
      ¬ closed σ i.val (1-j) ∧ σ (.selector i) = centreAt n i.val j
    else
      σ (.entry i) = entryAt n (i.val+1) ∧ ¬ closed σ i.val j ∧
      (closed σ i.val (1-j) → σ (.selector i) = centreAt n i.val (1-j)) ∧
      (¬ closed σ i.val 0 → ¬ closed σ i.val 1 →
        σ (.selector i) = centreAt n i.val (if ctx = .parity then 0 else j))) ∧
  (∀ c, σ (.upper c) =
    if c.val.2.val = (b.testBit (c.val.1.val+1)).toNat
      then .reward c else entryAt n 0) ∧
  (b < 2 ^ n - 1 → ∀ c, c.val.1.val = nextLevel n b → ∀ k,
    σ (.cycle c k) ≠ .centre c)

def sourceTarget (n b : ℕ) : Node n :=
  if (b+1).testBit 0 then selectorAt n 0 else entryAt n 1

noncomputable def sourceStep {n : ℕ} (ctx : Context) (b N : ℕ) (ε : ℚ)
    (s s' : CounterState n) : Prop :=
  ∃ e, counterChoice ctx s (sourceTarget n b)
      (if ctx = .parity then pgImproving s.strategy else mdpImproving N ε s.strategy) e ∧
    s' = updateCounter s e

end FriedmannZadeh
