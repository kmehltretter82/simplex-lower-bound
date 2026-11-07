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


namespace FriedmannZadeh

/-- Theorem 4, together with its simplex transfer in §5. The rule, construction,
zero initial occurrence record and complete-run semantics are fixed in Main. -/
theorem goal : Main := by sorry

end FriedmannZadeh


namespace FriedmannZadeh

/-- Section 5, with every count and every pivot preserved by the occupancy LP. -/
theorem lp_transfer (n N : ℕ) (ε : ℚ) (hp : Parameters n N ε)
    (s : ℕ → CounterState n) (T : ℕ) (hs : mdpRun N ε s T) :
    ∃ z : ℕ → LPState (rowCount n) (columnCount n),
      InducedSimplexRun n N ε z T ∧
      ∀ t, t ≤ T → represents (s t).strategy (z t).basis ∧
        ∀ j, (z t).count j = (s t).count (columnAt n j).val := by sorry

end FriedmannZadeh


namespace FriedmannZadeh

/-- Transition-probability and initial-policy obligations for §4 / Lemma 1. -/
theorem mdp_valid (n N : ℕ) (ε : ℚ) (hp : Parameters n N ε) :
    legal (initial (n := n)) ∧ proper ε (initial (n := n)) ∧
    ∀ σ : Strategy n, legal σ → ∀ v,
      (∀ w, 0 ≤ transition ε σ v w) ∧ ∑ w, transition ε σ v w = 1 := by sorry

end FriedmannZadeh


namespace FriedmannZadeh

/-- Lemma 1, parity part, with a common minimizing counterstrategy. -/
theorem sink (n : ℕ) (hn : 0 < n) (σ : Strategy n) (hσ : PgReachable σ) :
    ∃ τ, PgCounterstrategy σ τ ∧ ∀ v, ∃ t : ℕ,
      ∀ k, t ≤ k → FriedmannParity.play (parityGame n) σ τ v k = .sink := by sorry

end FriedmannZadeh


namespace FriedmannZadeh

/-- Table 1 and the explicit deterministic-vertex occupancy representation. -/
theorem size (n : ℕ) (hn : 0 < n) :
    Fintype.card (Node n) = 16 * n - 6 ∧
    rowCount n = 14 * n - 6 ∧ columnCount n = 26 * n - 12 := by sorry

end FriedmannZadeh


namespace FriedmannZadeh

/-- Agreement of the implemented valuation-defined transition direction with
the source's phase-defined direction, on an entire canonical enumeration.
Both the execution and the partition into source transitions are conclusions.
-/
theorem source_realization (n N : ℕ) (ε : ℚ) (hp : Parameters n N ε) :
    ∀ ctx : Context, ∃ T, ∃ s : ℕ → CounterState n, ∃ cut : ℕ → ℕ,
      (if ctx = .parity then pgRun s T else mdpRun N ε s T) ∧
      cut 0 = 0 ∧
      (∀ b, b < 2 ^ n → cut b ≤ T ∧ Canonical ctx b (s (cut b)).strategy) ∧
      (∀ b, b + 1 < 2 ^ n → cut b < cut (b+1) ∧ ∀ t,
        cut b ≤ t → t < cut (b+1) →
          sourceStep ctx b N ε (s t) (s (t+1))) := by sorry

end FriedmannZadeh


namespace FriedmannZadeh

/-- Concrete completion of the partial ordering in §6.2 / Definition 7. -/
theorem tie_order (n : ℕ) (hn : 0 < n) (ctx : Context)
    (σ : Strategy n) (hσ : legal σ) (target : Node n)
    (ht : target = entryAt n 1 ∨ target = selectorAt n 0) :
    linearExtension ctx σ target (sourceRank ctx σ target) := by sorry

end FriedmannZadeh


namespace FriedmannZadeh

/-- Radix realization of the standard priority-multiplicity valuation order.
Source: Avis--Friedmann, §2.2, used for the repeated-priority counter here. -/
theorem valuation (n : ℕ) (hn : 0 < n) (σ τ ρ υ : Strategy n)
    (v w : Node n) :
    (pgPlayScore σ τ v < pgPlayScore ρ υ w) ↔
      countValueLT (FriedmannParity.playValue (parityGame n) σ τ v)
        (FriedmannParity.playValue (parityGame n) ρ υ w) := by sorry

end FriedmannZadeh
