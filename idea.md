I would turn this into a research program on what makes local improvement algorithms slow: their memory, the information they use, and the numerical structure of their instances. Your Avis–Friedmann formalization gives you a starting point for studying those questions with constructions and proofs that can be checked together.

My strongest recommendation is to pursue three connected goals:
1. Make the existing development reusable: complete the real-geometry interpretation and extract precise machinery for transferring algorithm executions.
2. Make one serious new-mathematics bet: obtain compact numerical encodings for a broader class of lower bounds, exploiting a limitation explicitly identified in 2026 research.
3. Run a parallel investigation into robustness: determine whether Cunningham’s exponential behavior survives meaningful perturbations, and which parameters control the transition between fast and slow behavior.
I would aim for one new complexity theorem within twelve months, supported by several useful formalization results. Below is the plan I would actually follow, including a concrete candidate theorem worth investigating immediately.
1. What you now have—and why it is useful
I inspected your mission. It marks the main simplex theorem as proved, with the prescribed initial state, a complete execution, at least \(2^n\) pivots, and strict objective improvement at every pivot. The family has \(5(n-1)\) equality constraints and \(10(n-1)\) nonnegative variables. I checked the public statement and status; I have not independently rebuilt the submitted proof.

The mission’s scope notes identify several valuable foundations: explicit basis and ratio-test semantics, the cyclic cursor, transient rational MDPs, and geometric realization conditions. They also identify a specific extension: the rational-to-real geometric interpretation remains a mathematical argument rather than a checked Lean transport theorem.

That suggests the right next move: expose the structure inside the proof that forces a long run.

The scientific object is a collection of obligations:
- Which moves are improving at each phase?
- Which improving move does the cursor encounter first?
- Which inequalities force a bit to reset or advance?
- Which properties survive a change of coefficients or representation?
- How much numerical precision is actually necessary?
Once those obligations are explicit and reusable, changing a gadget, a parameter, or a selection rule becomes a controlled mathematical experiment.
2. The next formalizations, in priority order
A. Complete the passage from rational to real LPs
This is the clearest immediate extension.

Separate it into two theorems.

Algebraic transport: interpreting the rational coefficients in \(\mathbb R\) preserves the same basis sequence, reduced-cost signs, ratio-test comparisons, cursor updates, and objective increases.

Geometric transport: the real feasible polytope has the required boundedness, vertices, edges, and cube structure.

The second part needs more than coefficient casting: a statement quantified over rational feasible points must be connected to the corresponding statement over all real feasible points. Rational dual certificates, rank preservation, and a description of faces provide possible routes.

Deliverable: a theorem about an ordinary real LP that carries the accepted lower bound all the way through its geometric interpretation.

This is a formalization advance with immediate reuse value. I would give it a bounded initial time allocation so it does not absorb the entire research program.
B. Connect the relational theorem to an executable algorithm
Your displayed main theorem asserts the existence of a complete run satisfying the formal Cunningham relation. The next useful interface is an executable implementation whose run is proved to satisfy that relation.

Make explicit:
- The initial basis and cursor.
- The distinction between scanning an action and performing a pivot.
- The leaving-variable convention.
- The treatment of ties.
- The stopping condition.
Then determine whether the constructed family has unique relevant choices. If so, derive a theorem about the unique execution. If some choices remain, state exactly whether the lower bound concerns a specified tie-breaking implementation or every permitted execution.

This is useful for experimentation: an exact executable model lets you modify instances and immediately see where the phase argument fails.

For every generated instance, record structural size, coefficient bit length, pivot count, and scan count separately. A bound exponential in dimension is not automatically exponential in the full binary encoding length.
C. Extract a theorem about preserving complete executions
A reduction that preserves optimal solutions need not preserve an algorithm’s behavior.

For these lower bounds, the state should include both the mathematical solution and the rule’s memory:
\[
\text{algorithm state}
=
(\text{policy or basis},\ \text{cursor or other memory}).
\]
The central reusable theorem should say:
An encoding that preserves the initial state, relevant improving-action information, selected action, state update, and memory update preserves the execution.

For deterministic systems, the essential condition has the form
\[
F(\operatorname{next}_S(s))
=
\operatorname{next}_T(F(s)),
\]
with termination handled explicitly.

The important work lies in proving this condition for substantive transformations. For Cunningham, preserving the improving set and cyclic ordering can suffice. For a rule using reduced-cost rankings, preserving signs alone is insufficient. For a history rule, duplicating an action may change its behavior even when optimal values remain unchanged.

I would first extract the smallest interface that fits your proof, then test it on a second construction before generalizing further.
D. Formalize the new direct game-to-simplex connection
The highest-value next paper, in my judgment, is Matthew Maat’s “Connecting Strategy Improvement, the Simplex Algorithm and Lopsidedness,” revised 21 October 2026. It gives a direct correspondence between strategy improvement and simplex under nondegeneracy assumptions, bypassing the handcrafted intermediate MDP construction. It also explicitly notes potentially doubly exponential LP coefficients. arxiv.org

I would formalize the trajectory correspondence first, then express it through the interface above. Keep your existing MDP route: comparing the two translations could reveal where one has better numerical complexity.

This creates a useful research setup: two certified routes from games to LPs, with their hypotheses and numerical costs exposed.

For a later stress test, Zadeh’s rule is attractive because its history consists of counters rather than one cursor. Its exponential LP lower bound is already known, as are exponential bounds for Zadeh, Johnson, and Cunningham on abstract AUSOs. Those are worthwhile formalizations, but the novelty would lie in the reusable theory or a strengthening of their assumptions. Abstract AUSO bounds also require a separate realizability argument before becoming bounds for actual LPs. Springer Nature Link
3. Main research bet: compact coefficients for broader lower bounds
This is the direction I would give the largest share of research attention.

The 2026 paper by Disser, Loho, Maat, and Mosis proves a superpolynomial lower bound for index-based rules with \(o(m/\log m)\) memory states. Its August full version explicitly explains a limitation: the LP translation has doubly exponential coefficients, so the conclusion excludes strongly polynomial behavior without automatically excluding polynomial behavior in binary input length. arxiv.org

That provides a concrete target.
Proposed theorem
For an appropriate class \(\mathcal C\) of pivot rules, construct, for each \(R\in\mathcal C\), a family \(L_s\) satisfying
\[
\operatorname{bits}(L_s)\le s^{O(1)}
\qquad\text{and}\qquad
T_R(L_s)=s^{\omega(1)}.
\]
Here \(s\) measures structural size and the family may depend on the rule.

The intended advance is to retain a broad lower bound while giving the hard instances polynomial-length binary descriptions.
Why your development helps
You already have a detailed example where a game counter becomes a rational MDP and then an LP. That is an alternative to applying a very general transformation with enormous coefficients.

The research strategy would be:
1. Select one restricted family of hard gadgets from the broader construction.
2. Extract the inequalities actually needed for its counter phases.
3. Seek a direct transient-MDP implementation of those inequalities.
4. Prove that polynomially many bits suffice.
5. Transfer the complete execution to simplex.
This could succeed because a general translation may distinguish many configurations that never matter for a particular hard family. A specialized construction only needs the distinctions required by its invariant.

The hard part is preserving all information visible to the rule. Showing that the intended move remains legal is insufficient: another move might become improving, or a ranking might change, causing the algorithm to leave the intended trajectory.
A practical first experiment
Take a small gadget family and formulate coefficient selection as a constraint problem:
- Intended improvements have positive advantage.
- Relevant alternative moves have the required signs.
- Rankings observed by the selector are preserved.
- Policies remain well-defined.
- Coefficients satisfy explicit bit-size or denominator bounds.
Search for small rational solutions, inspect the pattern, and attempt an inductive parameter assignment.

Where possible, fix the transition structure and vary rewards first. This often makes the initial search substantially simpler than changing everything at once.
What would count as success?
There are several meaningful levels:
- A better encoding for one important subclass.
- A general sufficient condition for polynomial-bit realizations of counter gadgets.
- A quantitative tradeoff between instance size, memory allowance, and numerical precision.
- The full compact-encoding theorem for the chosen rule class.
Even an obstruction can be useful: for example, a theorem that a specified gadget architecture requires a certain amount of precision. Its scope must remain “within this architecture” unless it actually rules out all constructions.

Keep the first target family-specific. A general efficiently constructible, polynomial-bit reduction from the relevant games to rational LPs would have much larger algorithmic consequences. Maat’s paper explicitly identifies the numerical limitation of its general correspondence. arxiv.org
4. Parallel research bet: robust Cunningham lower bounds
The central question is:
Does the exponential counter require finely tuned numbers, or can its behavior survive a substantial range of numerical changes?

There is a modest version and a strong version.

The modest version establishes a positive perturbation neighborhood for each finite instance, under suitable strictness assumptions. The strong version provides a useful, uniform quantitative radius as instance size grows.
Proposed strong target
Construct normalized MDP instances \(\widehat M_N\) such that, for explicit positive constants \(c,\alpha,k\),
\[
T_{\mathrm{Cunningham}}(\widehat M_N+\Delta)
\ge 2^{cN^\alpha}
\]
for every permitted perturbation satisfying
\[
\|\Delta\|_\infty\le N^{-k}.
\]
The perturbation model must specify what changes: rewards, nonzero transition probabilities, normalization constraints, and any fixed structural zeros.

This direction has a substantial precedent. Christ and Yannakakis already prove robust lower bounds for Howard’s policy iteration and other variants, including bounds surviving every allowed perturbation within an inverse-polynomial range. Thus the potential contribution here is a precise Cunningham result or a stronger quantitative tradeoff. arxiv.org
The key Cunningham-specific difficulty
For each intended pivot, you need to control:
1. Its positive advantage.
2. Every action encountered earlier in the cyclic scan.
3. The policy evaluation and feasibility conditions.
4. The corresponding leaving-variable behavior after translation to simplex.
The second condition is easy to overlook. A perturbation may preserve the intended improvement while enabling an earlier action, which changes the entire run.

Zero margins deserve special attention. Some may follow from identities preserved by the perturbation model. Others may require a redesigned gadget.
How I would stage this
First, vary only the objective. With \(A,b\) fixed, reduced-cost conditions are linear in the objective coefficients. This makes exact searches for admissible regions and normalized margins a manageable first problem.

Next, vary MDP rewards. Try to prove interval versions of the existing phase lemmas.

Then vary transition probabilities. This introduces rational-function and invertibility issues, but also addresses the most interesting numerical fragility.

Finally, replace fragile parameters with gadgets. Search for implementations with controlled primitive probabilities and rewards that reproduce the needed effective scales.

Track the size increase carefully. If \(n\) counter bits become \(N=O(n^q)\) states, a \(2^n\) execution becomes a lower bound of
\[
2^{\Omega(N^{1/q})}.
\]
That can still be a substantial result.

Also preserve the distinction between structured MDP perturbations and independent perturbations of every LP entry. A certified translation of the former does not automatically establish the latter.
5. A concrete first theorem worth attempting: an effective-horizon upper bound
I would also investigate a positive theorem early. It could explain exactly which feature permits your exponential family.

Here is a specific candidate.

This is a proposed theorem and proof route, not a result I have checked in Lean or established as new.

Consider a finite transient MDP with \(m\) available state–action pairs, total-reward maximization, and exact single-switch policy evaluation. Suppose there is a vector \(w\) and \(H\ge1\) such that, for every action \(a\) available at state \(s\),
\[
1\le w_s\le H,
\qquad
\sum_t P(s,a,t)w_t\le w_s-1.
\]
This is a directly checkable certificate of bounded effective horizon.
Candidate conclusion
Cunningham’s cyclic policy-improvement rule performs at most
\[
O\!\left(m^2H\log(2H)\right)
\]
pivots.

The useful feature would be independence from reward magnitudes.
Why this looks plausible
Cunningham’s scan has a fairness property: over one complete sweep, every action is inspected.

Let \(v_{\mathrm{start}}\) and \(v_{\mathrm{end}}\) be the policy values at the beginning and end of a sweep, and let \(T\) be the Bellman optimality operator.

For any inspected action:
- If it is skipped, the current value already dominates its one-step value.
- If it is selected, policy improvement raises the value enough.
- Later improvements preserve that inequality.
This suggests the sweep lemma
\[
v_{\mathrm{end}}\ge T v_{\mathrm{start}}.
\]
The certificate \(w\) supplies a contraction factor \(1-1/H\) in a weighted norm. A block of \(O(H\log(2H))\) sweeps should therefore reduce the error enough to eliminate permanently at least one previously used suboptimal action. There are at most \(m\) such eliminations, and at most \(m\) pivots per sweep.

Contraction and action-elimination techniques have precedents in policy-iteration analyses, including Scherrer’s work; weighted transformations also appear in Akian–Gaubert. The particular cyclic-scan theorem needs a careful novelty check and a full proof. arxiv.org
Why pursue this alongside lower bounds?
If it works, apply it to your hard family.

It would show that the family cannot admit a uniformly polynomial \(H\) satisfying the certificate. You would have identified a quantitative obstruction behind the exponential run.

Even if the mathematical statement turns out to be an overlooked consequence of existing work, it would give you a useful formal upper-bound counterpart. It could also generalize from Cunningham to schedules with a bounded delay before every action is reconsidered.

This is the first small research question I would try to settle. It has a concrete proof route, directly uses your MDP semantics, and can inform the harder robustness project.
6. Higher-risk target: lower bounds for rules with richer information and memory
The most ambitious conceptual question is:
How much information and memory must a pivot rule use to escape these constructions?

The 2026 ranking paper already gives an \(\Omega(2^{\sqrt N})\) bound for deterministic memoryless rules using three rankings: global index, reduced cost, and objective improvement. It also explicitly asks about larger memory in the index-based setting. arxiv.org

A focused next target would be:
Extend the three-ranking lower bound to rules controlled by a two-state machine.

That is a precise step beyond the memoryless setting. It is much easier to investigate than an unrestricted claim about every history-based rule.

The formal model should separate:
\[
\text{observation},\qquad
\text{memory state},\qquad
\text{selected action},\qquad
\text{memory update}.
\]
Specify whether the observation contains action identities, relative ranks, actual numerical values, or information about the current basis. These choices materially change the theorem.

Also distinguish memory states from memory bits. A cursor taking \(m\) possible positions has \(m\) states, even though it can be stored in \(O(\log m)\) bits.
Suggested progression
Start with two states and a tightly defined observation model. Search for pairs of phases that appear equivalent to the selector but require incompatible behavior to avoid a long run. Then try to turn that mechanism into a repeatable counter.

If successful, increase the controller size and derive a quantitative lower bound depending on memory.

The desired conclusion has the form
\[
\forall R\in\mathcal C_q,\quad
\exists I_R:\quad
T_R(I_R)\text{ is large}.
\]
The instance may depend on the rule. Requiring one fixed instance to defeat every conceivable rule would be a substantially different claim.

I would activate this branch after the simulation interface and one generalized family are working.
7. Two longer-term targets
A. Randomizing the cyclic order
This is a natural experiment because it changes the mechanism your proof tracks most closely.

Distinguish four algorithms:
- A fixed order with a random initial cursor.
- A random order chosen once.
- A new random order after every sweep.
- Occasional random pivots mixed with cyclic scanning.
Begin with the initial cursor. There are only linearly many possible cursor positions, and the existing phase invariants may show synchronization—or suggest a short synchronization gadget.

For a random order, the meaningful lower-bound target is
\[
\exists I_N\text{ fixed independently of }\pi:
\qquad
\mathbb E_\pi[T(I_N,\pi)]
\ge 2^{\Omega(N^\alpha)}.
\]
There is a critical quantifier distinction:
\[
\forall\pi\;\exists I_\pi
\]
does not establish hardness of a randomized order on one fixed instance.

I did not locate a resolution of this precise randomized-Cunningham question in the targeted searches. I would treat it as a candidate research direction requiring a dedicated literature check.
B. Extend the construction to network LPs
Avis–Friedmann explicitly propose extending their lower bound to network LPs in the paper’s conclusion. I did not locate a later resolution. That makes it a credible long-term target, with that qualification about its current status. oliverfriedmann.com

The goal would be a family of min-cost-flow instances with polynomial binary description length and superpolynomial Cunningham network-simplex executions.

There is an elementary constraint worth incorporating immediately. With integral capacities bounded by \(U\), integer costs bounded by \(C\), and \(m\) arcs, objective values at integral vertices lie in a range of size \(O(mUC)\). Each strict improvement changes the integer objective by at least one.

Consequently, an exponential strict-improvement construction cannot simultaneously keep all those numerical magnitudes polynomially bounded. Large magnitudes with polynomial bit length remain possible.

I would reserve a small exploratory allocation for this project until the earlier work reveals a suitable gadget.
8. Make formal verification part of discovery
The program needs an experimental component, but its purpose should be to discover inductive constructions.
Search over a controlled family
Start close to the existing proof:
- Transient MDPs with two actions per controlled state.
- A finite collection of gadget types.
- Layered composition indexed by counter position.
- Symbolic reward and probability parameters.
- A fixed collection of counter phases.
Let external search use simulation, SAT/SMT, LP optimization, and agent-generated conjectures. Ask it to produce a candidate construction together with proposed invariants and local certificates.

Then prove in Lean that the certificate implies the all-\(n\) result.
Certify the recurrence
Checking a trajectory with millions of pivots can validate an example. The reusable mathematical result is an inductive statement connecting counter phases.

For example:
Every state satisfying the invariant for counter value \(k\) reaches a state satisfying the invariant for \(k+1\), after at least one actual pivot, while preserving all intermediate obligations.

Be precise about counting: \(2^n\) counter configurations give \(2^n-1\) increments. Initialization and termination steps must be handled separately to recover an exact \(2^n\) theorem.
Keep the certificate claim realistic
A reasonable goal is:
A restricted certificate language admits efficient checking, and compact accepted certificates establish exponentially long families of executions.

Do not assume every exponential run has a compact proof. Restrict the language to finite phase machines, controlled invariant templates, explicit algebraic obligations, and specified induction rules.

There is already useful infrastructure: leanprover/lp provides exact LP certificates checked in Lean and linear-arithmetic tactics. It could discharge some local obligations; it does not itself prove pivot-trajectory correspondence or an inductive counter theorem. GitHub
Measure mathematical progress
The research record for each construction should contain:
\[
\begin{aligned}
&\text{states, actions, nonzero coefficients},\\
&\text{coefficient bits and total encoding length},\\
&\text{pivot lower bound},\\
&\text{robustness radius},\\
&\text{effective-horizon certificate or obstruction},\\
&\text{assumptions on observations, memory, and ties}.
\end{aligned}
\]
That makes different constructions genuinely comparable.
9. A twelve-month execution plan
These are planning estimates for a small team—roughly an algorithms researcher and two Lean-capable contributors, supported by agents. For a solo effort, I would preserve the order and stretch the calendar.
Period	Main work	Concrete success criterion
Weeks 1–2	Export the accepted development, document its exact theorem interfaces, build an exact small-instance runner	Reproducible build; explicit initialization, cursor, ties, and size conventions
Weeks 3–6	Rational-to-real transport; executable-run correspondence; investigate the horizon theorem	A real-LP theorem and a checked execution interface, or sharply isolated remaining lemmas
Weeks 7–12	Extract counter-phase and simulation interfaces; parameterize the current construction	Existing lower bound rederived through the interfaces; first all-\(n\) parameter extension
Months 4–6	Begin Maat’s direct transfer; attack compact encodings for one broader gadget family	A certified translation component and a concrete polynomial-bit candidate or a proved obstruction
Months 7–9	Concentrate on the strongest research branch; develop robustness gadgets if promising	A new asymptotic statement with a complete mathematical proof and substantial Lean coverage
Months 10–12	Finish verification, compare against current literature, prepare a paper and reusable release	One publishable new result plus the supporting formal library


How I would allocate attention
During the first quarter, most effort should go into exposing and testing the existing proof’s structure. After that, I would allocate approximately:
- 40%: compact encodings for broader lower bounds.
- 30%: shared formalization and execution-preserving transformations.
- 20%: robustness and effective-horizon analysis.
- 10%: randomized cursor/order and network experiments.
The memory extension becomes a main branch only if the first generalized constructions suggest a workable mechanism.
Decision points
At day 30, require an executable model and a concrete proposed extension.

At day 90, require either an all-\(n\) extension or a precise obstruction that changes the research target. A large table of finite experiments is insufficient.

At month six, concentrate effort on the branch with the clearest theorem. Keep the remaining branches as documented conjectures and small experiments.
What I would start this week
I would open three tightly scoped missions:
1. Real interpretation and execution correspondence for Cunningham’s lower bound.
   Close the scalar-extension step and connect the accepted relation to an exact algorithm.
2. Cyclic policy iteration under a bounded effective-horizon certificate.
   Attempt the candidate \(O(m^2H\log(2H))\) theorem, with the fair-sweep lemma as the first milestone.
3. Parameterized counter gadgets with certified numerical bounds.
   Replace fixed coefficients by explicit hypotheses, then search for smaller encodings and larger margins.
The strategic destination would be a paper along the lines of “Precision, Memory, and Robustness in Pivot-Rule Lower Bounds.” Its central contribution should be a new quantitative theorem—about encoding length, perturbation tolerance, or the power of memory—with the formal development serving as the machinery that made the result discoverable and checkable.

My first major bet would be coefficient compression; my first short theorem attempt would be the effective-horizon bound. Together they give the program both a credible path to an early result and a route to a substantial advance beyond the original paper.
