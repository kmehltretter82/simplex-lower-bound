# Research & Formalization Execution Plan: Precision, Memory, and Robustness in Pivot-Rule Lower Bounds

## 1. Executive Summary & Program Vision

This plan converts the completed Avis–Friedmann Lean 4 formalization (`Solutions/Sol_friedmann_cunningham_*.lean`) into a 12-month research and formal-verification program investigating **what makes local improvement algorithms slow**: their memory, the information they observe, and the numerical structure of their instances.

### Baseline Assets in This Repository
- **Verified Cunningham Lower Bound Suite (`Solutions/`)**: Proved Lean 4 theorems establishing the $2^n$ lower bound across parity games (`Sol_friedmann_cunningham_parity_lower_bound.lean`), transient rational MDPs (`Sol_friedmann_cunningham_mdp_lower_bound.lean`), abstract unique-sink orientations (`Sol_friedmann_cunningham_auso_lower_bound.lean`), rational cube realization (`Sol_friedmann_cunningham_cube_realization.lean`), and standard-form rational primal simplex (`Sol_friedmann_cunningham_simplex_lower_bound.lean`) for the $5(n-1) \times 10(n-1)$ family defined in `Definitions/Def_friedmann_cunningham.lean` and `Definitions/Def_friedmann_simplex.lean`.
- **Companion Models & Audit Tooling**: Formal definitions for Zadeh's history-counter rule (`Definitions/Def_friedmann_zadeh.lean`), parity/payoff games (`Definitions/Def_friedmann_parity.lean`, `Definitions/Def_friedmann_payoff.lean`), kernel-checked local algebra certificates (`checks/CunninghamRewardTranslation.lean`, `checks/CunninghamNonconstantObjective.lean`), and exact Python exploration scripts (`notes/cunningham_numeric.py`, `notes/cunningham_semantic_probe.py`, `notes/zadeh_explore.py`).

### Core Strategic Goals
1. **Make the Existing Development Reusable**: Complete the rational-to-real LP geometric transport, connect the relational specification (`cunninghamRun`) to an executable algorithm, and extract a general execution-preserving simulation theorem.
2. **Primary New-Mathematics Bet (Coefficient Compression)**: Obtain compact (polynomial-bit) numerical encodings for a broader class of pivot-rule lower bounds, overcoming the doubly exponential LP coefficient bottleneck identified in 2026 research (Disser–Loho–Maat–Mosis 2026; Maat 2026).
3. **Parallel Investigation (Effective Horizon & Robustness)**: Prove an early positive upper-bound theorem ($O(m^2 H \log(2H))$ pivots under a bounded effective-horizon certificate) to expose the exact obstruction driving exponential runs, and determine whether Cunningham's exponential behavior survives inverse-polynomial perturbations.

**Target 12-Month Destination**: A flagship paper tentatively titled *"Precision, Memory, and Robustness in Pivot-Rule Lower Bounds"* establishing at least one new asymptotic complexity theorem (on encoding bit-length, perturbation tolerance, or finite-memory controllers), backed by a reusable, kernel-checked Lean 4 library.

---

## 2. Immediate Launch Missions (Week 1 Kickoff)

Before expanding into long-horizon branches, open three tightly scoped missions immediately:

- [ ] **Mission 1: Real Interpretation & Executable Run Correspondence for Cunningham's Rule**
  - Close the scalar-extension step from $\mathbb{Q}$ (`Definitions/Def_friedmann_simplex.lean`) to $\mathbb{R}$, and connect the relational theorem `simplex_lower_bound` (`Solutions/Sol_friedmann_cunningham_simplex_lower_bound.lean`) to a deterministic executable function.
- [ ] **Mission 2: Cyclic Policy Iteration Under a Bounded Effective-Horizon Certificate**
  - Formalize and attempt the candidate $O(m^2 H \log(2H))$ pivot upper bound for transient MDPs, targeting the **Fair-Sweep Lemma** ($v_{\mathrm{end}} \ge T v_{\mathrm{start}}$) as the first formal milestone.
- [ ] **Mission 3: Parameterized Counter Gadgets with Certified Numerical Bounds**
  - Refactor the concrete rational parameters (`scale n`, `epsilon n`, `rewardG n i`, `rewardH n i` in `Definitions/Def_friedmann_cunningham.lean`) into an abstract hypothesis structure capturing the exact phase inequalities needed for the counter recurrence, enabling automated search for smaller bit-lengths and wider perturbation margins.

---

## 3. Technical Workstreams & Actionable Tasks

### Workstream 1: Reusable Formal Infrastructure & Real/Executable Bridges

#### WS1.A — Complete the Passage from Rational to Real LPs *(Time-boxed: Weeks 3–6)*
Separate the $\mathbb{Q} \to \mathbb{R}$ extension into two theorems so that algebraic execution transfer and polytope geometry do not entangle:
1. **Algebraic Transport Theorem**:
   - Define scalar extension of `FriedmannSimplex.LP m n` from $\mathbb{Q}$ to $\mathbb{R}$ via `Rat.cast : ℚ →+* ℝ`.
   - Prove that casting preserves `basisMatrix` nonsingularity, `basicValues`, `basicPoint`, `direction`, `reducedCost` signs, `improving` predicates, `leaving` ratio-test comparisons, `cyclicDistance` choices, and strict `basicObjective` increases across the entire run.
2. **Geometric Transport Theorem**:
   - Lift `bounded`, `isVertex`, `polytopeAdjacent`, and `realizesCube` (`Definitions/Def_friedmann_cunningham.lean`) from rational feasible points ($x : \operatorname{Fin} k \to \mathbb{Q}$) to all real feasible points ($x : \operatorname{Fin} k \to \mathbb{R}$).
   - Bridge universal quantifiers over real feasible points using rational dual certificates (Farkas/witness vectors from `Sol_friedmann_cunningham_cube_realization.lean`), rank preservation over field extensions, and explicit face characterizations.
3. **Deliverable**: `Theorems/Thm_FriedmannCunningham_real_simplex.lean` and its proof module, certifying the $2^n$ lower bound on an ordinary real LP together with its real combinatorial cube realization.

#### WS1.B — Connect the Relational Theorem to an Executable Algorithm *(Weeks 1–5)*
1. **Executable Simplex & MDP Runners**:
   - Define a computable step function `cunninghamExecStep` over $\mathbb{Q}$ that explicitly separates **scanning an action** (advancing the cursor past non-improving actions) from **performing a pivot** (updating the basis and cursor).
   - Make explicit: initial basis and cursor (`initialState`), leaving-variable tie-breaking convention (e.g., lexicographically first row index minimizing the ratio test), action-selection tie-breaking (uniquely determined by `cyclicDistance` when `order` is an equivalence), and the stopping condition (`optimalBasis`).
2. **Uniqueness & Soundness Proof**:
   - Use `nondegenerate (program n)` (already proved in `Sol_friedmann_cunningham_lp_valid.lean`) to prove that `leaving` is unique at every reachable basis of `program n`.
   - Prove that the relational `cunninghamRun` in `simplex_lower_bound` corresponds to the unique execution trace of the executable runner.
3. **Instrumentation**:
   - Extend `notes/cunningham_numeric.py` and the Lean runner to log a standardized profile for every generated instance: structural size $(m, n, \text{nnz})$, maximum coefficient bit-length, total binary encoding length, exact pivot count, and total scan count.

#### WS1.C — Extract a General Execution-Preserving Transformation Theorem *(Weeks 7–10)*
1. **Abstract Stateful Local-Improvement Interface**:
   - Define a generic deterministic local-improvement system with state
     $$\text{State} = (\text{Config},\ \text{Memory})$$
     where $\text{Config}$ represents a policy, strategy, or basis, and $\text{Memory}$ represents a cyclic cursor, permutation state, or Zadeh history counter.
2. **Reusable Simulation Theorem**:
   - Generalize the transfer pattern at the end of `Solutions/Sol_friedmann_cunningham_simplex_lower_bound.lean` (lines 294–332) into a standalone theorem: a map $F : S \to T$ that preserves the initial state, the visible improving-action information/rankings, the selected action, the configuration update, the memory update, and the termination predicate satisfies
     $$F(\operatorname{next}_S(s)) = \operatorname{next}_T(F(s))$$
     and preserves complete execution traces and strict objective progress.
3. **Validation on Two Constructions**:
   - Re-derive the MDP-to-Simplex transfer (`Sol_friedmann_cunningham_simplex_lower_bound.lean`) and Parity-to-MDP transfer as instances of this interface, then test it on a second rule/construction (Maat's direct game-to-simplex correspondence or Zadeh's rule in `Def_friedmann_zadeh.lean`).

#### WS1.D — Formalize Maat's Direct Game-to-Simplex Connection *(Months 4–5)*
1. **Trajectory Correspondence**:
   - Formalize the direct strategy-improvement-to-simplex trajectory correspondence under nondegeneracy from Maat (*"Connecting Strategy Improvement, the Simplex Algorithm and Lopsidedness"*, rev. Oct 2026), bypassing the intermediate transient-MDP construction.
2. **Side-by-Side Route Comparison**:
   - Express both Maat's direct route and the existing Avis–Friedmann transient-MDP route through the WS1.C simulation interface.
   - Quantitatively compare coefficient bit-lengths, matrix sparsity, and nondegeneracy hypotheses across both certified translations.

---

### Workstream 2: Effective-Horizon Upper Bound (Fast-Track Positive Theorem)

This workstream targets an early positive complexity result that explains *why* the Avis–Friedmann family requires exponentially small transition probabilities ($\varepsilon_n = (2n+1)^{-(2n+2)}$).

#### Candidate Theorem
Let $\mathcal{M}$ be a finite transient MDP with $m$ state–action pairs, total-reward maximization, and exact single-switch policy evaluation. Suppose there exist a weight vector $w$ and horizon bound $H \ge 1$ such that for every state $s$ and available action $a$:
$$1 \le w_s \le H \qquad\text{and}\qquad \sum_t P(s,a,t)\,w_t \le w_s - 1.$$
Then Cunningham's cyclic policy-improvement rule performs at most
$$O\!\left(m^2 H \log(2H)\right)$$
pivots, completely independent of reward magnitudes.

#### Actionable Proof Steps *(Weeks 3–8)*
1. **Literature & Novelty Check**:
   - Cross-check the exact cyclic-scan statement against Scherrer's contraction/action-elimination bounds for Howard's rule and Akian–Gaubert's weighted-norm transformations.
2. **Milestone 2.1 — The Fair-Sweep Lemma**:
   - Define a complete cyclic sweep of Cunningham's cursor across all $m$ actions.
   - Prove that if $v_{\mathrm{start}}$ and $v_{\mathrm{end}}$ are the policy value vectors at the start and end of a full sweep and $T$ is the Bellman optimality operator, then $v_{\mathrm{end}} \ge T v_{\mathrm{start}}$ componentwise (since every skipped action was already dominated and every taken switch strictly raised values monotonically).
3. **Milestone 2.2 — Weighted Contraction & Action Elimination**:
   - Equip $\mathbb{R}^S$ with the $w$-weighted supremum norm $\|u\|_w = \max_s |u_s| / w_s$ and prove that $T$ is a $(1 - 1/H)$-contraction.
   - Prove that a block of $O(H \log(2H))$ sweeps permanently eliminates at least one suboptimal action used at the start of the block, yielding at most $m$ elimination phases and $O(m^2 H \log(2H))$ total pivots.
4. **Milestone 2.3 — Obstruction Corollary on the Avis–Friedmann Family**:
   - Apply the theorem to `FriedmannCunningham.transition n hn` together with the proved $2^n$ lower bound (`Sol_friedmann_cunningham_mdp_lower_bound.lean`) to formally deduce that `program n` cannot admit any certificate $(w, H)$ with $H \le \operatorname{poly}(n)$.

---

### Workstream 3: Compact Numerical Encodings for Broader Lower Bounds (Main Research Bet)

**Context**: Disser, Loho, Maat, and Mosis (Aug 2026) prove superpolynomial lower bounds for index-based rules with $o(m/\log m)$ memory states, and Maat (Oct 2026) connects games directly to simplex, but both translations produce **doubly exponential LP coefficients**—ruling out strongly polynomial complexity without ruling out polynomial-time complexity in the binary input length.

#### Target Theorem
For a specified class $\mathcal{C}$ of limited-memory / ranking-based pivot rules, construct for each $R \in \mathcal{C}$ a family of linear programs $L_s$ of structural size $s$ such that:
$$\operatorname{bits}(L_s) \le s^{O(1)} \qquad\text{and}\qquad T_R(L_s) = s^{\omega(1)}.$$

#### Actionable Execution Steps *(Weeks 7–36)*
1. **Step 3.1 — Parameterize the Existing Counter Proof (Weeks 7–12)**:
   - Inspect `Solutions/Sol_friedmann_cunningham_mdp_lower_bound.lean` and extract the exact set of algebraic inequalities over `scale`, `epsilon`, `rewardG`, and `rewardH` used across the counter phases:
     - Positive advantage of the intended switch at each phase.
     - Non-improving sign of every action encountered earlier by the cyclic cursor during the scan.
     - Policy evaluation well-definedness (nonsingularity and nonnegativity).
   - Package these obligations as a Lean `structure CounterParameterSpec (n : ℕ)` and prove that *any* parameter assignment satisfying `CounterParameterSpec n` yields the $2^n$ run.
2. **Step 3.2 — Select One Broader Gadget Family & Extract Obligations (Months 4–5)**:
   - Choose a restricted family of hard counter gadgets from the 2026 index/ranking-based lower-bound constructions.
   - Write down the exact visibility obligations required by the selector (not only intended-move legality, but also all alternative-move signs and relative reduced-cost/objective-improvement rankings visible to the rule).
3. **Step 3.3 — Automated Constraint Search for Small Rational Realizations (Months 4–6)**:
   - Build a Python + LP/SMT solver script (`notes/compact_coeff_search.py`) for $n = 3, 4, 5, 6$:
     - First fix the transition topology and vary only rewards; then co-optimize transitions and rewards.
     - Minimize maximum denominator/numerator bit-length subject to strict phase-obligation margins.
   - Inspect the small-$n$ rational solutions to conjecture an closed-form inductive parameter assignment with $\operatorname{poly}(n)$ bit-length.
4. **Step 3.4 — Prove All-$n$ Polynomial-Bit Sufficiency or Architectural Obstruction (Months 6–9)**:
   - **Success Tier A (Full Target)**: Prove the compact-encoding theorem $\operatorname{bits}(L_s) \le s^{O(1)}$ for the target rule class and transfer the execution to simplex via WS1.C.
   - **Success Tier B (Intermediate / Tradeoff)**: Prove a compact encoding for a key subclass, or establish a quantitative tradeoff between structural size $s$, memory states, and coefficient bit-length.
   - **Success Tier C (Certified Obstruction)**: If polynomial bits are impossible within the fixed gadget topology, prove a formal lower bound showing that *any* parameter assignment satisfying `CounterParameterSpec` on that gadget architecture requires $\Omega(\cdot)$ bits of precision.

---

### Workstream 4: Robust Cunningham Lower Bounds (Parallel Research Bet)

**Central Question**: Does Cunningham's exponential behavior require finely tuned rational numbers, or does it survive every allowed perturbation within an inverse-polynomial radius (analogous to Christ–Yannakakis for Howard's rule)?

#### Target Theorems
- **Modest Target**: Establish an explicit positive perturbation neighborhood $\delta_n > 0$ around `program n` within which every perturbed instance still requires $\ge 2^n$ Cunningham pivots.
- **Strong Target**: Construct normalized transient MDP instances $\widehat{M}_N$ of size $N$ such that for explicit constants $c, \alpha, k > 0$ and every permitted perturbation $\Delta$ satisfying $\|\Delta\|_\infty \le N^{-k}$,
  $$T_{\mathrm{Cunningham}}(\widehat{M}_N + \Delta) \ge 2^{c N^\alpha}.$$

#### Staged Execution Plan *(Weeks 9–36)*
1. **Stage 4.1 — Objective-Only Perturbations ($A, b$ Fixed)**:
   - Keep the conservation matrix $A$ and right-hand side $b$ fixed so basis matrices and directions remain invariant, making reduced costs linear in $c$.
   - Compute exact admissible polytopes of objective perturbations $\Delta c$ for $n = 3, 4, 5$ using LP margin maximization, paying special attention to **every action scanned before the intended pivot** and any zero-margin identities.
2. **Stage 4.2 — MDP Reward Perturbations**:
   - Prove interval versions of the phase value bounds in `Sol_friedmann_cunningham_mdp_lower_bound.lean` when action rewards $r(s,a)$ vary independently within $\pm \delta$.
3. **Stage 4.3 — Transition Probability Perturbations**:
   - Define the exact perturbation model: perturbations to nonzero transition probabilities preserving sub-stochasticity/normalization while keeping structural zeros fixed (distinguishing structured MDP perturbations from arbitrary entrywise LP matrix perturbations).
   - Bound the rational-function perturbation of $(I - P_\sigma)^{-1}$ using Neumann-series / effective-horizon bounds.
4. **Stage 4.4 — Gadget Replacement for Fragile Scales**:
   - Replace exponentially small single-edge probabilities ($\varepsilon_n = (2n+1)^{-(2n+2)}$) with cascades of $O(n \log n)$ or $O(n^2)$ binary/constant-probability relay states so primitive transition probabilities stay bounded away from $0$ by $1/\operatorname{poly}(N)$.
   - Track the state blowup $N = O(n^q)$ carefully to certify the resulting $2^{\Omega(N^{1/q})}$ robust lower bound.

---

### Workstream 5: Information, Memory, and Longer-Term Targets

#### WS5.A — Lower Bounds for Finite-Memory Controllers *(Activate after WS1.C & WS3 prototype)*
- **Target**: Extend the 2026 three-ranking $\Omega(2^{\sqrt{N}})$ memoryless lower bound (global index, reduced cost, objective improvement) to deterministic rules controlled by a **two-state machine** (and subsequently $q$-state controllers).
- **Formal Model**: Explicitly separate
  $$(\text{Observation},\ \text{Memory State},\ \text{Selected Action},\ \text{Memory Update})$$
  and distinguish the number of memory states $q$ from memory bits $\lceil \log_2 q \rceil$.
- **Approach**: Search for pairs of counter phases that produce identical observations (relative rankings of improving moves) to the selector while requiring incompatible actions to avoid a counter increment, then compose into a repeatable gadget showing $\forall R \in \mathcal{C}_q,\ \exists I_R$ with $T_R(I_R)$ superpolynomial.

#### WS5.B — Randomizing the Cyclic Order *(Exploratory — 5% allocation)*
- Clearly separate four distinct algorithmic variants:
  1. Fixed cyclic order with a uniformly random initial cursor (`last`).
  2. Single random permutation $\pi$ chosen once at initialization.
  3. Fresh random permutation resampled after every complete sweep.
  4. Occasional random improving pivots mixed with cyclic scanning.
- **First Step**: Analyze Variant 1 on `program n` (only $10(n-1)$ possible initial cursor positions) to test whether all initial cursor positions synchronize into the standard counter trajectory within one sweep, or build a short synchronization gadget.
- **Quantifier Discipline for Variant 2**: Ensure any lower bound targets a *single fixed instance* $I_N$ independent of $\pi$ such that $\mathbb{E}_\pi[T(I_N, \pi)] \ge 2^{\Omega(N^\alpha)}$ (rather than $\forall \pi\,\exists I_\pi$).

#### WS5.C — Network LP Lower Bounds *(Exploratory — 5% allocation)*
- Investigate Avis–Friedmann's open question of realizing an exponential Cunningham run on minimum-cost network flow instances.
- **Built-in Structural Constraint**: Because integral vertices of a network flow problem with $m$ arcs, capacity bound $U$, and cost bound $C$ span at most $O(mUC)$ integer objective values, any exponential strict-improvement family must use large capacities or costs (with polynomial binary bit-length $\log(UC) = \operatorname{poly}(n)$). Hold larger investment until WS3/WS4 reveal compatible scale-amplification gadgets.

---

### Workstream 6: Verification-Driven Discovery & Benchmarking Pipeline

#### Neuro-Symbolic / Solver-Guided Discovery Loop
1. **Constrained Search Space**: Restrict external search (`notes/` Python + Z3/CVC5/LP solvers) to layered transient MDPs with two actions per controlled state, symbolic reward/probability scales, and finite phase-machine templates close to `Def_friedmann_cunningham.lean`.
2. **Certificate-to-Lean Pipeline**: Require the external search to emit:
   - Candidate gadget parameters,
   - Phase invariant templates $\mathcal{I}(k)$ for counter value $k \in \{0, \dots, 2^n - 1\}$, and
   - Local linear/algebraic certificates for the recurrence $\mathcal{I}(k) \implies \mathcal{I}(k+1)$ (plus separate initialization and termination proofs so $2^n - 1$ increments plus boundary steps yield an exact $\ge 2^n$ pivot theorem).
3. **Lean Verification**: Discharge local linear-arithmetic obligations in Lean (using `linarith`, `positivity`, `nlinarith`, and evaluating `leanprover/lp` for exact rational LP certificate checking) while proving the all-$n$ inductive counter theorem in the kernel.

#### Mandatory Benchmark Record for Every Construction
Maintain a structured catalog (`notes/construction-benchmarks.json` and a markdown table) recording six standardized metrics for every baseline and new family:

| Metric Category | Recorded Fields |
| :--- | :--- |
| **1. Structural Size** | States $S$, actions $m$, LP rows/cols $(5(n-1), 10(n-1))$, nonzeros $\text{nnz}(A)$ |
| **2. Numerical Encoding** | Max coefficient bit-length, common denominator bit-length, total binary encoding bits |
| **3. Complexity Lower Bound** | Certified pivot lower bound $T(n)$ and scan count lower bound |
| **4. Robustness Radius** | Certified perturbation norm $\|\Delta\|_\infty$ (objective-only, reward, transition, full LP) |
| **5. Effective Horizon** | Best finite certificate $H(n)$ or proved lower-bound obstruction on $H(n)$ |
| **6. Rule & Tie Assumptions** | Observed information (signs vs. rankings), memory state count $q$, leaving/entering tie-breaking |

---

## 4. Twelve-Month Milestones, Deliverables & Schedule

*Resource assumption: 1 algorithms researcher + 2 Lean-capable contributors supported by AI agents (for solo execution, preserve the strict dependency order and stretch calendar dates proportionally).*

| Milestone | Period | Core Workstreams | Concrete Deliverables | Acceptance / Success Criteria |
| :--- | :--- | :--- | :--- | :--- |
| **M1: Executable Baseline & Spec Audit** | **Weeks 1–2** | WS1.B, WS6 | • Documented theorem interfaces for `Solutions/Sol_friedmann_cunningham_*.lean`<br>• Computable Lean/Python runner with scan vs. pivot separation<br>• Initial `notes/construction-benchmarks.json` record for Avis–Friedmann | Reproducible `python3 scripts/check_all.py` build; explicit initialization, cursor, tie-breaking, bit-size, and scan-count instrumentation verified on $n=3,4,5$. |
| **M2: Real LP Bridge & Horizon Prototype** | **Weeks 3–6** | WS1.A, WS1.B, WS2 | • `Thm_FriedmannCunningham_real_simplex.lean` (algebraic + geometric $\mathbb{Q}\to\mathbb{R}$ transport)<br>• Executable-run equivalence theorem<br>• Proof of Fair-Sweep Lemma ($v_{\mathrm{end}} \ge T v_{\mathrm{start}}$) and draft of $O(m^2 H \log(2H))$ theorem | Checked real-LP lower bound theorem and executable correspondence in Lean (or sharply isolated remaining geometric face lemmas); Fair-Sweep Lemma kernel-checked. |
| **M3: Simulation Framework & Parameterized Counter** | **Weeks 7–12** | WS1.C, WS2, WS3 (Step 3.1), WS4 (Stage 4.1) | • Generic stateful simulation theorem $F(\operatorname{next}_S(s)) = \operatorname{next}_T(F(s))$<br>• `CounterParameterSpec` abstraction of `Sol_friedmann_cunningham_mdp_lower_bound.lean`<br>• Completed $O(m^2 H \log(2H))$ horizon theorem + Avis–Friedmann obstruction corollary<br>• First all-$n$ parameter extension (reduced bit-scale or objective-perturbation margin) | Existing Cunningham lower bound re-derived cleanly through the abstract simulation and parameter interfaces; at least one certified all-$n$ parameter improvement proved. |
| **M4: Direct Game Transfer & Compact-Coefficient Candidate** | **Months 4–6** | WS1.D, WS3 (Steps 3.2–3.3), WS4 (Stages 4.2–4.3) | • Formalized trajectory correspondence for Maat (Oct 2026)<br>• `notes/compact_coeff_search.py` SMT/LP solver suite<br>• Concrete polynomial-bit candidate family (or proved architectural precision obstruction) for one broader gadget class | Certified game-to-simplex translation component in Lean; explicit polynomial-bit parameter formula validated for small $n$ with an inductive proof outline (or formal obstruction theorem). |
| **M5: Asymptotic Complexity Theorem & Lean Coverage** | **Months 7–9** | WS3 (Step 3.4) *or* WS4 (Stage 4.4) / WS5.A | • Complete mathematical proof of the strongest research branch (compact encodings, inverse-polynomial robust Cunningham gadgets, or 2-state memory lower bound)<br>• Core inductive phase-step proofs formalized in Lean | One new asymptotic complexity theorem with a complete mathematical proof and substantial Lean 4 kernel coverage of the counter recurrence and transfer lemmas. |
| **M6: Final Verification, Paper & Library Release** | **Months 10–12** | All active branches | • Manuscript *"Precision, Memory, and Robustness in Pivot-Rule Lower Bounds"*<br>• Self-contained, documented Lean 4 library & benchmark suite | Zero `sorry` declarations in all main theorems (`python3 scripts/check_all.py` passes cleanly); complete benchmark comparison table against 2017–2026 literature. |

---

## 5. Portfolio Effort Allocation & Go/No-Go Decision Gates

### Effort Allocation (Post-Quarter 1)
During **Quarter 1 (Weeks 1–12)**, dedicate ~70% of effort to exposing, abstracting, and parameterizing the existing Avis–Friedmann proof structure (WS1.A–C, WS3.1) and ~30% to the fast-track effective-horizon upper bound (WS2).

For **Quarters 2–4 (Months 4–12)**, allocate effort across branches as follows:
- **40% — Compact Coefficients for Broader Lower Bounds (WS3)**: Primary new-mathematics bet.
- **30% — Shared Formalization & Execution-Preserving Transformations (WS1.C–D, WS6)**: Reusable simulation interfaces, Maat's direct transfer, and Lean proof engineering.
- **20% — Robustness & Effective-Horizon Analysis (WS2, WS4)**: Perturbation margins, interval phase lemmas, and probability-amplification gadgets.
- **10% — Randomized Cursor/Order & Network LP Experiments (WS5)**: Contained exploratory probes; promote WS5.A (finite-memory controllers) to a main branch only if WS3's generalized gadget mechanics reveal a clean state-aliasing construction.

### Hard Decision Gates
1. **Day 30 Gate (End of Week 4)**:
   - *Requirement*: Working executable model (with separate pivot and scan counters), baseline benchmark table for $n=3,4,5$, and a concrete algebraic specification of the first parameter extension + Fair-Sweep Lemma status.
   - *Pivot Trigger*: If the geometric $\mathbb{Q}\to\mathbb{R}$ face-transport proof in WS1.A threatens to overrun Week 6, freeze the algebraic $\mathbb{Q}\to\mathbb{R}$ execution theorem and scope the remaining real-polytope face lemma as an isolated background task.
2. **Day 90 Gate (End of Week 12 / Milestone M3)**:
   - *Requirement*: Either a proved **all-$n$ parameter extension** (smaller coefficient scales or positive objective/reward perturbation radius) *or* a **precise mathematical obstruction theorem** explaining why the Avis–Friedmann topology forbids it.
   - *Rule*: A large table of finite numerical experiments for $n \le 6$ without an all-$n$ inductive statement does **not** pass this gate.
3. **Month 6 Gate (End of Milestone M4)**:
   - *Requirement*: Evaluate the candidate theorems from WS3 (compact encodings for broader rules) and WS4 (robust Cunningham gadgets).
   - *Action*: Concentrate 70%+ of Months 7–9 capacity on the single branch with the clearest path to a flagship asymptotic theorem; convert the remaining branches into documented conjectures, finite benchmark records, or scoped sections in the final library.
