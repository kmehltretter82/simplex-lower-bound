import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 8: a realizable AUSO of dimension 5(n−1), with both signed
directions ordered as in (1), and a complete walk of length at least 2^n. -/
theorem auso_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    realizesCube n hn ∧
    ∃ (c : Fin (cols n) → ℚ) (T : ℕ) (s : ℕ → MDPState n),
      isAUSO n hn c ∧
      (∀ σ τ, cubeOrientation n hn (program n).c σ τ → cubeOrientation n hn c σ τ) ∧
      cubeRun n hn c s T ∧ 2 ^ n ≤ T := by
  sorry

end FriedmannCunningham


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


namespace FriedmannCunningham

/-- Lemma 12: an actual polytope realization, with an objective that orients
every cube edge and retains the original strict improvements. -/
theorem cube_realization (n : ℕ) (hn : 3 ≤ n) :
    realizesCube n hn ∧
    ∃ c : Fin (cols n) → ℚ, isAUSO n hn c ∧
      ∀ σ τ, cubeOrientation n hn (program n).c σ τ → cubeOrientation n hn c σ τ := by
  sorry

end FriedmannCunningham


namespace FriedmannCunningham

/-- Construction validity needed by the §4.2 policy/BFS correspondence.
The graph-derived reward retains the aliases discussed in the source notes. -/
theorem lp_valid (n : ℕ) (hn : 3 ≤ n) :
    FriedmannSimplex.bounded (program n) ∧
    ∀ σ : Policy n,
      FriedmannSimplex.basicFeasible (program n) (policyBasis n hn σ) ∧
        ∀ i, 0 < FriedmannSimplex.basicValues (program n) (policyBasis n hn σ) i := by
  sorry

end FriedmannCunningham


namespace FriedmannCunningham

/-- Theorem 6, expressed on the equivalent decision-state MDP. -/
theorem mdp_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → MDPState n), mdpRun n hn s T ∧ 2 ^ n ≤ T := by
  sorry

end FriedmannCunningham


namespace FriedmannCunningham

open scoped BigOperators

/-- Figure 7 and Lemma 8, after eliminating the random vertices: each action's
transition row is substochastic and every policy's transient matrix is invertible. -/
theorem mdp_valid (n : ℕ) (hn : 3 ≤ n) :
    (∀ r b q, 0 ≤ transition n hn r b q) ∧
    (∀ r b, (∑ q : Fin (rows n), transition n hn r b q) ≤ 1) ∧
    (∀ σ : Policy n,
      (FriedmannSimplex.basisMatrix (program n) (policyBasis n hn σ)).det ≠ 0) := by
  sorry

end FriedmannCunningham


namespace FriedmannCunningham

/-- Theorem 4, with the explicit Figure 2 graph and multiplicity valuations. -/
theorem parity_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → ParityState n), parityRun n hn s T ∧ 2 ^ n ≤ T := by
  sorry

end FriedmannCunningham


namespace FriedmannCunningham

open scoped BigOperators

/-- The §4.2–4.3 correspondence, including Lemma 11's objective identity. -/
theorem policy_pivot (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    FriedmannSimplex.basicObjective (program n) (policyBasis n hn σ) =
      (∑ r : Fin (rows n), policyValue n hn σ r) ∧
    ∀ r,
      (mdpImproving n hn σ r ↔
        FriedmannSimplex.improving (program n) (policyBasis n hn σ)
          (actionColumn n hn r (!σ r))) ∧
      (mdpImproving n hn σ r →
        FriedmannSimplex.pivot (program n) (policyBasis n hn σ)
          (actionColumn n hn r (!σ r))
          (policyBasis n hn (Function.update σ r (!σ r)))) := by
  sorry

end FriedmannCunningham


namespace FriedmannCunningham

/-- Theorem 7: the graph-derived LP, the prescribed order and initial basis,
at least 2^n pivots, and strict objective increase on every pivot. -/
theorem simplex_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → FriedmannSimplex.State (rows n) (cols n)),
      s 0 = initialState n hn ∧
      FriedmannSimplex.cunninghamRun (program n) (order n) s T ∧
      2 ^ n ≤ T ∧
      ∀ t, t < T →
        FriedmannSimplex.basicObjective (program n) (s t).basis <
          FriedmannSimplex.basicObjective (program n) (s (t + 1)).basis := by
  sorry

end FriedmannCunningham
