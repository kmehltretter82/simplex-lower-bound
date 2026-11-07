import Definitions.Def_friedmann_parity
import Solutions.Sol_friedmann_parity_counterstrategy

set_option autoImplicit false

namespace FriedmannParity

open FriedmannMultiplicity

section StepComparison

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Part 1: Right-Step Comparison (`playValue_le_of_step_le`) -/

lemma reward_playValue_step_le_of_step_le {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (x : V) :
    reward (playValue G σ₂ τ₂ (step G σ₁ τ₁ x)).cyclePriority ≤
      reward (playValue G σ₂ τ₂ x).cyclePriority := by
  have hle := reward_cyclePriority_le_of_multiplicity_valueLE (hstep x)
  rwa [playValue_cyclePriority_step] at hle

lemma playValue_cyclePriority_eq_on_recurring_of_step_le {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    {v x w : V}
    (hx : x ∈ recurring (play G σ₁ τ₁ v))
    (hw : w ∈ recurring (play G σ₁ τ₁ v)) :
    (playValue G σ₂ τ₂ x).cyclePriority = (playValue G σ₂ τ₂ w).cyclePriority := by
  apply reward_injective
  exact eq_on_recurring_of_le_step_int
    (fun y => reward (playValue G σ₂ τ₂ y).cyclePriority)
    (reward_playValue_step_le_of_step_le hstep) hx hw

lemma count_playValue_eq_above_max_of_step_le {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (v : V) :
    let m := playValue G σ₂ τ₂
    let R₁ := recurring (play G σ₁ τ₁ v)
    let w₁ := cycleLeader G σ₁ τ₁ v
    let p₁ := (playValue G σ₁ τ₁ v).cyclePriority
    let p_star := (m w₁).cyclePriority
    let M := Finset.univ.sup G.priority + max p₁ p_star + 1
    ∀ d : ℕ, ∀ q : ℕ, M - d ≤ q → max p₁ p_star < q →
      ∀ x ∈ R₁,
        count G (m (step G σ₁ τ₁ x)).path q =
          count G (m (step G σ₂ τ₂ x)).path q ∧
        count G (m (step G σ₁ τ₁ x)).path q =
          count G (m x).path q := by
  intro m R₁ w₁ p₁ p_star M d
  have hw₁ : w₁ ∈ R₁ := cycleLeader_mem_recurring G σ₁ τ₁ v
  induction d with
  | zero =>
    intro q hMq _ x _
    have hsup : Finset.univ.sup G.priority < q := by omega
    rw [count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup]
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    intro q hMq hmaxq
    by_cases hMq' : M - d ≤ q
    · exact ih q hMq' hmaxq
    · have hgt : ∀ x ∈ R₁, ∀ q', q < q' →
          count G (m (step G σ₁ τ₁ x)).path q' =
            count G (m (step G σ₂ τ₂ x)).path q' := by
        intro x hx q' hq'
        exact (ih q' (by omega) (by omega) x hx).1
      have hmx_eq : ∀ x ∈ R₁,
          count G (m x).path q =
            count G (m (step G σ₂ τ₂ x)).path q := by
        intro x hx
        have hpx : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
        have hp_lt_q : (m x).cyclePriority < q := by omega
        have hcnt := count_playValue_step hp_lt_q
        have hle_p1 : G.priority x ≤ p₁ := Finset.le_sup hx
        have hne_q : G.priority x ≠ q := by omega
        rw [if_neg hne_q, Nat.add_zero] at hcnt
        exact hcnt
      have hcp_eq : ∀ x ∈ R₁,
          (m (step G σ₁ τ₁ x)).cyclePriority =
            (m (step G σ₂ τ₂ x)).cyclePriority := by
        intro x hx
        have h1 : (m (step G σ₁ τ₁ x)).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep (step_mem_recurring hx) hw₁
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
        rw [h1, playValue_cyclePriority_step]
        exact h2.symm
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
      · have hstep_le : ∀ x ∈ R₁,
            count G (m (step G σ₁ τ₁ x)).path q ≤ count G (m x).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (hstep x) (hcp_eq x hx) (hgt x hx)).1 hpar
        intro x hx
        have heq := eq_of_le_step_on_recurring
          (fun y => count G (m y).path q) hstep_le hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩
      · have hstep_ge : ∀ x ∈ R₁,
            count G (m x).path q ≤ count G (m (step G σ₁ τ₁ x)).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (hstep x) (hcp_eq x hx) (hgt x hx)).2 hpar
        intro x hx
        have heq := eq_of_step_le_on_recurring
          (fun y => count G (m y).path q) hstep_ge hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩

lemma reward_playValue_le_of_step_le {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (v : V) :
    reward (playValue G σ₁ τ₁ v).cyclePriority ≤
      reward (playValue G σ₂ τ₂ (cycleLeader G σ₁ τ₁ v)).cyclePriority := by
  let m := playValue G σ₂ τ₂
  let R₁ := recurring (play G σ₁ τ₁ v)
  let w₁ := cycleLeader G σ₁ τ₁ v
  let p₁ := (playValue G σ₁ τ₁ v).cyclePriority
  let p_star := (m w₁).cyclePriority
  change reward p₁ ≤ reward p_star
  have hw₁ : w₁ ∈ R₁ := cycleLeader_mem_recurring G σ₁ τ₁ v
  have hpw₁ : G.priority w₁ = p₁ :=
    (playValue_cyclePriority_eq_priority_cycleLeader G σ₁ τ₁ v).symm
  have habove : ∀ q : ℕ, max p₁ p_star < q → ∀ x ∈ R₁,
      count G (m (step G σ₁ τ₁ x)).path q =
        count G (m (step G σ₂ τ₂ x)).path q := by
    intro q hq x hx
    let M := Finset.univ.sup G.priority + max p₁ p_star + 1
    have hMM : M - M ≤ q := by simp
    exact (count_playValue_eq_above_max_of_step_le hstep v M q hMM hq x hx).1
  have hcp_eq : ∀ x ∈ R₁,
      (m (step G σ₁ τ₁ x)).cyclePriority =
        (m (step G σ₂ τ₂ x)).cyclePriority := by
    intro x hx
    have h1 : (m (step G σ₁ τ₁ x)).cyclePriority = p_star :=
      playValue_cyclePriority_eq_on_recurring_of_step_le hstep (step_mem_recurring hx) hw₁
    have h2 : (m x).cyclePriority = p_star :=
      playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
    rw [h1, playValue_cyclePriority_step]
    exact h2.symm
  rcases lt_trichotomy p₁ p_star with hlt | heq | hgt
  · rcases Nat.mod_two_eq_zero_or_one p_star with hpar | hpar
    · unfold reward
      split_ifs <;> omega
    · exfalso
      have hseq : ∀ x ∈ R₁, SetEquivalent G
          (m (step G σ₁ τ₁ x)).path
          (m (step G σ₂ τ₂ x)).path := by
        intro x hx q
        by_cases hq : p_star < q
        · exact habove q (by omega) x hx
        · have h1 : (playValue G σ₂ τ₂ (step G σ₁ τ₁ x)).cyclePriority = p_star :=
            playValue_cyclePriority_eq_on_recurring_of_step_le hstep (step_mem_recurring hx) hw₁
          have h2 : (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)).cyclePriority = p_star :=
            (hcp_eq x hx).symm.trans h1
          change count G (playValue G σ₂ τ₂ (step G σ₁ τ₁ x)).path q =
            count G (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)).path q
          rw [count_playValue_eq_zero_of_le_cyclePriority (by omega),
              count_playValue_eq_zero_of_le_cyclePriority (by omega)]
      have hlen_step : ∀ x ∈ R₁,
          (m (step G σ₁ τ₁ x)).length ≤
            (m (step G σ₂ τ₂ x)).length ∧
          (m (step G σ₂ τ₂ x)).length + 1 = (m x).length := by
        intro x hx
        have h1 : (m (step G σ₁ τ₁ x)).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep (step_mem_recurring hx) hw₁
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
        have hlen_le := length_le_of_multiplicity_valueLE_odd
          (hstep x) (hcp_eq x hx) (hseq x hx) (by rw [h1]; exact hpar)
        have hx_ne : x ≠ cycleLeader G σ₂ τ₂ x := by
          intro hcl
          have hpx : G.priority x = p_star := by
            have hpcl := playValue_cyclePriority_eq_priority_cycleLeader G σ₂ τ₂ x
            change (m x).cyclePriority = _ at hpcl
            rw [h2, ← hcl] at hpcl
            exact hpcl.symm
          have hpx_le : G.priority x ≤ p₁ := Finset.le_sup hx
          omega
        have hlen_eq := playValue_length_eq_succ_of_ne_cycleLeader hx_ne
        exact ⟨hlen_le, hlen_eq.symm⟩
      have hstep_le : ∀ x ∈ R₁, (m (step G σ₁ τ₁ x)).length ≤ (m x).length := by
        intro x hx
        have ⟨h1, h2⟩ := hlen_step x hx
        omega
      have heq_w1 := eq_of_le_step_on_recurring (fun y => (m y).length) hstep_le hw₁
      have ⟨h1, h2⟩ := hlen_step w₁ hw₁
      omega
  · rw [heq]
  · rcases Nat.mod_two_eq_zero_or_one p₁ with hpar | hpar
    · exfalso
      have hstep_rel : ∀ x ∈ R₁,
          count G (m (step G σ₁ τ₁ x)).path p₁ ≤
            count G (m (step G σ₂ τ₂ x)).path p₁ ∧
          count G (m x).path p₁ =
            count G (m (step G σ₂ τ₂ x)).path p₁ +
              (if G.priority x = p₁ then 1 else 0) := by
        intro x hx
        have hle_cnt := (count_le_or_ge_of_multiplicity_valueLE
          (hstep x) (hcp_eq x hx)
          (fun q' hq' => habove q' (by omega) x hx)).1 hpar
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
        have hp_lt : (m x).cyclePriority < p₁ := by
          rw [h2]
          exact hgt
        have hcnt := count_playValue_step hp_lt
        exact ⟨hle_cnt, hcnt⟩
      have hstep_le : ∀ x ∈ R₁,
          count G (m (step G σ₁ τ₁ x)).path p₁ ≤ count G (m x).path p₁ := by
        intro x hx
        have ⟨h1, h2⟩ := hstep_rel x hx
        omega
      have heq_w1 := eq_of_le_step_on_recurring
        (fun y => count G (m y).path p₁) hstep_le hw₁
      have ⟨h1, h2⟩ := hstep_rel w₁ hw₁
      rw [if_pos hpw₁] at h2
      omega
    · unfold reward
      split_ifs <;> omega

lemma multiplicity_playValue_le_of_step_le {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (v : V) :
    FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ v)
      (playValue G σ₂ τ₂ v) := by
  let π₁ := play G σ₁ τ₁ v
  let w₁ := cycleLeader G σ₁ τ₁ v
  let p₁ := (playValue G σ₁ τ₁ v).cyclePriority
  let k := (playValue G σ₁ τ₁ v).length
  have hcl_play : ∀ t : ℕ, cycleLeader G σ₁ τ₁ (π₁ t) = w₁ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [π₁] at ih ⊢
      rw [play_succ', cycleLeader_step, ih]
  have hcp_play : ∀ t : ℕ, (playValue G σ₁ τ₁ (π₁ t)).cyclePriority = p₁ := by
    intro t
    rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl_play t,
        ← playValue_cyclePriority_eq_priority_cycleLeader]
  have hbase_w1 : FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ w₁) (playValue G σ₂ τ₂ w₁) := by
    have hrew : reward p₁ ≤ reward (playValue G σ₂ τ₂ w₁).cyclePriority :=
      reward_playValue_le_of_step_le hstep v
    have hcl_w1 : w₁ = cycleLeader G σ₁ τ₁ w₁ := by
      have h := hcl_play k
      dsimp only [π₁, k] at h
      rw [play_playValue_length] at h
      exact h.symm
    have hcp_w1 : (playValue G σ₁ τ₁ w₁).cyclePriority = p₁ := by
      have h := hcp_play k
      dsimp only [π₁, k] at h
      rw [play_playValue_length] at h
      exact h
    rcases lt_or_eq_of_le hrew with hlt | heq
    · rw [multiplicity_valueLE_iff]
      right; left
      rw [hcp_w1]
      exact hlt
    · have hp_eq : p₁ = (playValue G σ₂ τ₂ w₁).cyclePriority := reward_injective heq
      have hcp_0 : (playValue G σ₁ τ₁ w₁).cyclePriority =
          (playValue G σ₂ τ₂ w₁).cyclePriority := by
        rw [hcp_w1, hp_eq]
      have hcl_0 : w₁ = cycleLeader G σ₂ τ₂ w₁ :=
        hcl_w1.trans (cycleLeader_eq_of_cyclePriority_eq hinj hcp_0)
      have hval_1 := playValue_eq_of_eq_cycleLeader hcl_w1
      have hval_2 := playValue_eq_of_eq_cycleLeader hcl_0
      rw [hval_1, hval_2, hcp_0]
      exact multiplicity_valueLE_refl G _
  have hind : ∀ d : ℕ, d ≤ k →
      FriedmannMultiplicity.ValueLE G
        (playValue G σ₁ τ₁ (π₁ (k - d)))
        (playValue G σ₂ τ₂ (π₁ (k - d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hk0 : k - 0 = k := by omega
      rw [hk0]
      dsimp only [π₁, k]
      rw [play_playValue_length]
      exact hbase_w1
    | succ d ih =>
      intro hd
      let t := k - (d + 1)
      have ht_lt : t < k := by omega
      have ht_succ : t + 1 = k - d := by omega
      let x := π₁ t
      let x' := step G σ₁ τ₁ x
      have hx'_eq : x' = π₁ (k - d) := by
        dsimp only [x', x, π₁]
        rw [← play_succ', ht_succ]
      have ih' : FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x') (playValue G σ₂ τ₂ x') := by
        rw [hx'_eq]
        exact ih (by omega)
      have hle_step : FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x')
          (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)) :=
        multiplicity_valueLE_trans ih' (hstep x)
      have hrew_le : reward (playValue G σ₁ τ₁ x).cyclePriority ≤
          reward (playValue G σ₂ τ₂ x).cyclePriority := by
        have h := reward_cyclePriority_le_of_multiplicity_valueLE hle_step
        dsimp only [x'] at h
        rw [playValue_cyclePriority_step, playValue_cyclePriority_step] at h
        exact h
      rcases lt_or_eq_of_le hrew_le with hlt | heq
      · rw [multiplicity_valueLE_iff]
        right; left
        exact hlt
      · have hp_eq : (playValue G σ₁ τ₁ x).cyclePriority =
            (playValue G σ₂ τ₂ x).cyclePriority :=
          reward_injective heq
        have hx_ne_w1 : x ≠ cycleLeader G σ₁ τ₁ x := by
          rw [hcl_play t]
          exact play_ne_cycleLeader_of_lt_length ht_lt
        have hx_ne_2 : x ≠ cycleLeader G σ₂ τ₂ x := by
          intro hcl_2
          exact hx_ne_w1 (hcl_2.trans (cycleLeader_eq_of_cyclePriority_eq hinj hp_eq.symm))
        have hval_1 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_w1
        have hnot_1 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_w1
        have hval_2 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_2
        have hnot_2 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_2
        change FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x) (playValue G σ₂ τ₂ x)
        rw [hval_1, hval_2]
        apply multiplicity_valueLE_prepend
        · rw [playValue_cyclePriority_step, playValue_cyclePriority_step, hp_eq]
        · exact hnot_1
        · exact hnot_2
        · exact hle_step
  have h0 := hind k le_rfl
  have hkk : k - k = 0 := by omega
  rw [hkk] at h0
  exact h0

lemma playValue_le_of_step_le {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (v : V) :
    ValueLE G (playValue G σ₁ τ₁ v) (playValue G σ₂ τ₂ v) := by
  rw [valueLE_iff_multiplicity_valueLE hinj]
  apply multiplicity_playValue_le_of_step_le hinj
  intro x
  exact (valueLE_iff_multiplicity_valueLE hinj _ _).mp (hstep x)

/-! ### Part 2: Left-Step Comparison (`le_playValue_of_le_step`) -/

lemma reward_playValue_le_step_of_le_step {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (x : V) :
    reward (playValue G σ₁ τ₁ x).cyclePriority ≤
      reward (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)).cyclePriority := by
  have hle := reward_cyclePriority_le_of_multiplicity_valueLE (hstep x)
  rwa [playValue_cyclePriority_step] at hle

lemma playValue_cyclePriority_eq_on_recurring_of_le_step {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    {v x w : V}
    (hx : x ∈ recurring (play G σ₂ τ₂ v))
    (hw : w ∈ recurring (play G σ₂ τ₂ v)) :
    (playValue G σ₁ τ₁ x).cyclePriority = (playValue G σ₁ τ₁ w).cyclePriority := by
  apply reward_injective
  have h := eq_on_recurring_of_le_step_int
    (fun y => -reward (playValue G σ₁ τ₁ y).cyclePriority)
    (fun y => by have := reward_playValue_le_step_of_le_step hstep y; omega) hx hw
  omega

lemma count_playValue_eq_above_max_of_le_step {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (v : V) :
    let m := playValue G σ₁ τ₁
    let R₂ := recurring (play G σ₂ τ₂ v)
    let w₂ := cycleLeader G σ₂ τ₂ v
    let p₂ := (playValue G σ₂ τ₂ v).cyclePriority
    let p_star := (m w₂).cyclePriority
    let M := Finset.univ.sup G.priority + max p₂ p_star + 1
    ∀ d : ℕ, ∀ q : ℕ, M - d ≤ q → max p₂ p_star < q →
      ∀ x ∈ R₂,
        count G (m (step G σ₁ τ₁ x)).path q =
          count G (m (step G σ₂ τ₂ x)).path q ∧
        count G (m (step G σ₂ τ₂ x)).path q =
          count G (m x).path q := by
  intro m R₂ w₂ p₂ p_star M d
  have hw₂ : w₂ ∈ R₂ := cycleLeader_mem_recurring G σ₂ τ₂ v
  induction d with
  | zero =>
    intro q hMq _ x _
    have hsup : Finset.univ.sup G.priority < q := by omega
    rw [count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup]
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    intro q hMq hmaxq
    by_cases hMq' : M - d ≤ q
    · exact ih q hMq' hmaxq
    · have hgt : ∀ x ∈ R₂, ∀ q', q < q' →
          count G (m (step G σ₁ τ₁ x)).path q' =
            count G (m (step G σ₂ τ₂ x)).path q' := by
        intro x hx q' hq'
        exact (ih q' (by omega) (by omega) x hx).1
      have hmx_eq : ∀ x ∈ R₂,
          count G (m x).path q =
            count G (m (step G σ₁ τ₁ x)).path q := by
        intro x hx
        have hpx : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
        have hp_lt_q : (m x).cyclePriority < q := by omega
        have hcnt := count_playValue_step hp_lt_q
        have hle_p2 : G.priority x ≤ p₂ := Finset.le_sup hx
        have hne_q : G.priority x ≠ q := by omega
        rw [if_neg hne_q, Nat.add_zero] at hcnt
        exact hcnt
      have hcp_eq : ∀ x ∈ R₂,
          (m (step G σ₁ τ₁ x)).cyclePriority =
            (m (step G σ₂ τ₂ x)).cyclePriority := by
        intro x hx
        have h1 : (m (step G σ₂ τ₂ x)).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep (step_mem_recurring hx) hw₂
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
        rw [playValue_cyclePriority_step, h1, h2]
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
      · have hstep_ge : ∀ x ∈ R₂,
            count G (m x).path q ≤ count G (m (step G σ₂ τ₂ x)).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (hstep x) (hcp_eq x hx) (hgt x hx)).1 hpar
        intro x hx
        have heq := eq_of_step_le_on_recurring
          (fun y => count G (m y).path q) hstep_ge hx
        exact ⟨(hmx_eq x hx).symm.trans heq.symm, heq⟩
      · have hstep_le : ∀ x ∈ R₂,
            count G (m (step G σ₂ τ₂ x)).path q ≤ count G (m x).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (hstep x) (hcp_eq x hx) (hgt x hx)).2 hpar
        intro x hx
        have heq := eq_of_le_step_on_recurring
          (fun y => count G (m y).path q) hstep_le hx
        exact ⟨(hmx_eq x hx).symm.trans heq.symm, heq⟩

lemma reward_le_playValue_of_le_step {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (v : V) :
    reward (playValue G σ₁ τ₁ (cycleLeader G σ₂ τ₂ v)).cyclePriority ≤
      reward (playValue G σ₂ τ₂ v).cyclePriority := by
  let m := playValue G σ₁ τ₁
  let R₂ := recurring (play G σ₂ τ₂ v)
  let w₂ := cycleLeader G σ₂ τ₂ v
  let p₂ := (playValue G σ₂ τ₂ v).cyclePriority
  let p_star := (m w₂).cyclePriority
  change reward p_star ≤ reward p₂
  have hw₂ : w₂ ∈ R₂ := cycleLeader_mem_recurring G σ₂ τ₂ v
  have hpw₂ : G.priority w₂ = p₂ :=
    (playValue_cyclePriority_eq_priority_cycleLeader G σ₂ τ₂ v).symm
  have habove : ∀ q : ℕ, max p₂ p_star < q → ∀ x ∈ R₂,
      count G (m (step G σ₁ τ₁ x)).path q =
        count G (m (step G σ₂ τ₂ x)).path q := by
    intro q hq x hx
    let M := Finset.univ.sup G.priority + max p₂ p_star + 1
    have hMM : M - M ≤ q := by simp
    exact (count_playValue_eq_above_max_of_le_step hstep v M q hMM hq x hx).1
  have hcp_eq : ∀ x ∈ R₂,
      (m (step G σ₁ τ₁ x)).cyclePriority =
        (m (step G σ₂ τ₂ x)).cyclePriority := by
    intro x hx
    have h1 : (m (step G σ₂ τ₂ x)).cyclePriority = p_star :=
      playValue_cyclePriority_eq_on_recurring_of_le_step hstep (step_mem_recurring hx) hw₂
    have h2 : (m x).cyclePriority = p_star :=
      playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
    rw [playValue_cyclePriority_step, h1, h2]
  rcases lt_trichotomy p₂ p_star with hlt | heq | hgt
  · rcases Nat.mod_two_eq_zero_or_one p_star with hpar | hpar
    · exfalso
      have hseq : ∀ x ∈ R₂, SetEquivalent G
          (m (step G σ₁ τ₁ x)).path
          (m (step G σ₂ τ₂ x)).path := by
        intro x hx q
        by_cases hq : p_star < q
        · exact habove q (by omega) x hx
        · have h1 : (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)).cyclePriority = p_star :=
            playValue_cyclePriority_eq_on_recurring_of_le_step hstep (step_mem_recurring hx) hw₂
          have h2 : (playValue G σ₁ τ₁ (step G σ₁ τ₁ x)).cyclePriority = p_star :=
            (hcp_eq x hx).trans h1
          change count G (playValue G σ₁ τ₁ (step G σ₁ τ₁ x)).path q =
            count G (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)).path q
          rw [count_playValue_eq_zero_of_le_cyclePriority (by omega),
              count_playValue_eq_zero_of_le_cyclePriority (by omega)]
      have hlen_step : ∀ x ∈ R₂,
          (m (step G σ₂ τ₂ x)).length ≤
            (m (step G σ₁ τ₁ x)).length ∧
          (m (step G σ₁ τ₁ x)).length + 1 = (m x).length := by
        intro x hx
        have h1 : (m (step G σ₂ τ₂ x)).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep (step_mem_recurring hx) hw₂
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
        have hlen_ge := length_ge_of_multiplicity_valueLE_even
          (hstep x) (hcp_eq x hx) (hseq x hx) (by rw [playValue_cyclePriority_step, h2]; exact hpar)
        have hx_ne : x ≠ cycleLeader G σ₁ τ₁ x := by
          intro hcl
          have hpx : G.priority x = p_star := by
            have hpcl := playValue_cyclePriority_eq_priority_cycleLeader G σ₁ τ₁ x
            change (m x).cyclePriority = _ at hpcl
            rw [h2, ← hcl] at hpcl
            exact hpcl.symm
          have hpx_le : G.priority x ≤ p₂ := Finset.le_sup hx
          omega
        have hlen_eq := playValue_length_eq_succ_of_ne_cycleLeader hx_ne
        exact ⟨hlen_ge, hlen_eq.symm⟩
      have hstep_le : ∀ x ∈ R₂, (m (step G σ₂ τ₂ x)).length ≤ (m x).length := by
        intro x hx
        have ⟨h1, h2⟩ := hlen_step x hx
        omega
      have heq_w2 := eq_of_le_step_on_recurring (fun y => (m y).length) hstep_le hw₂
      have ⟨h1, h2⟩ := hlen_step w₂ hw₂
      omega
    · unfold reward
      split_ifs <;> omega
  · rw [heq]
  · rcases Nat.mod_two_eq_zero_or_one p₂ with hpar | hpar
    · unfold reward
      split_ifs <;> omega
    · exfalso
      have hstep_rel : ∀ x ∈ R₂,
          count G (m (step G σ₂ τ₂ x)).path p₂ ≤
            count G (m (step G σ₁ τ₁ x)).path p₂ ∧
          count G (m x).path p₂ =
            count G (m (step G σ₁ τ₁ x)).path p₂ +
              (if G.priority x = p₂ then 1 else 0) := by
        intro x hx
        have hge_cnt := (count_le_or_ge_of_multiplicity_valueLE
          (hstep x) (hcp_eq x hx)
          (fun q' hq' => habove q' (by omega) x hx)).2 hpar
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
        have hp_lt : (m x).cyclePriority < p₂ := by
          rw [h2]
          exact hgt
        have hcnt := count_playValue_step hp_lt
        exact ⟨hge_cnt, hcnt⟩
      have hstep_le : ∀ x ∈ R₂,
          count G (m (step G σ₂ τ₂ x)).path p₂ ≤ count G (m x).path p₂ := by
        intro x hx
        have ⟨h1, h2⟩ := hstep_rel x hx
        omega
      have heq_w2 := eq_of_le_step_on_recurring
        (fun y => count G (m y).path p₂) hstep_le hw₂
      have ⟨h1, h2⟩ := hstep_rel w₂ hw₂
      rw [if_pos hpw₂] at h2
      omega

lemma multiplicity_le_playValue_of_le_step {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (v : V) :
    FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ v)
      (playValue G σ₂ τ₂ v) := by
  let π₂ := play G σ₂ τ₂ v
  let w₂ := cycleLeader G σ₂ τ₂ v
  let p₂ := (playValue G σ₂ τ₂ v).cyclePriority
  let k := (playValue G σ₂ τ₂ v).length
  have hcl_play : ∀ t : ℕ, cycleLeader G σ₂ τ₂ (π₂ t) = w₂ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [π₂] at ih ⊢
      rw [play_succ', cycleLeader_step, ih]
  have hcp_play : ∀ t : ℕ, (playValue G σ₂ τ₂ (π₂ t)).cyclePriority = p₂ := by
    intro t
    rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl_play t,
        ← playValue_cyclePriority_eq_priority_cycleLeader]
  have hbase_w2 : FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ w₂) (playValue G σ₂ τ₂ w₂) := by
    have hrew : reward (playValue G σ₁ τ₁ w₂).cyclePriority ≤ reward p₂ :=
      reward_le_playValue_of_le_step hstep v
    have hcl_w2 : w₂ = cycleLeader G σ₂ τ₂ w₂ := by
      have h := hcl_play k
      dsimp only [π₂, k] at h
      rw [play_playValue_length] at h
      exact h.symm
    have hcp_w2 : (playValue G σ₂ τ₂ w₂).cyclePriority = p₂ := by
      have h := hcp_play k
      dsimp only [π₂, k] at h
      rw [play_playValue_length] at h
      exact h
    rcases lt_or_eq_of_le hrew with hlt | heq
    · rw [multiplicity_valueLE_iff]
      right; left
      rw [hcp_w2]
      exact hlt
    · have hp_eq : (playValue G σ₁ τ₁ w₂).cyclePriority = p₂ := reward_injective heq
      have hcp_0 : (playValue G σ₁ τ₁ w₂).cyclePriority =
          (playValue G σ₂ τ₂ w₂).cyclePriority := by
        rw [hcp_w2, hp_eq]
      have hcl_1 : w₂ = cycleLeader G σ₁ τ₁ w₂ :=
        hcl_w2.trans (cycleLeader_eq_of_cyclePriority_eq hinj hcp_0.symm)
      have hval_1 := playValue_eq_of_eq_cycleLeader hcl_1
      have hval_2 := playValue_eq_of_eq_cycleLeader hcl_w2
      rw [hval_1, hval_2, hcp_0]
      exact multiplicity_valueLE_refl G _
  have hind : ∀ d : ℕ, d ≤ k →
      FriedmannMultiplicity.ValueLE G
        (playValue G σ₁ τ₁ (π₂ (k - d)))
        (playValue G σ₂ τ₂ (π₂ (k - d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hk0 : k - 0 = k := by omega
      rw [hk0]
      dsimp only [π₂, k]
      rw [play_playValue_length]
      exact hbase_w2
    | succ d ih =>
      intro hd
      let t := k - (d + 1)
      have ht_lt : t < k := by omega
      have ht_succ : t + 1 = k - d := by omega
      let x := π₂ t
      let x' := step G σ₂ τ₂ x
      have hx'_eq : x' = π₂ (k - d) := by
        dsimp only [x', x, π₂]
        rw [← play_succ', ht_succ]
      have ih' : FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x') (playValue G σ₂ τ₂ x') := by
        rw [hx'_eq]
        exact ih (by omega)
      have hle_step : FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
          (playValue G σ₂ τ₂ x') :=
        multiplicity_valueLE_trans (hstep x) ih'
      have hrew_le : reward (playValue G σ₁ τ₁ x).cyclePriority ≤
          reward (playValue G σ₂ τ₂ x).cyclePriority := by
        have h := reward_cyclePriority_le_of_multiplicity_valueLE hle_step
        dsimp only [x'] at h
        rw [playValue_cyclePriority_step, playValue_cyclePriority_step] at h
        exact h
      rcases lt_or_eq_of_le hrew_le with hlt | heq
      · rw [multiplicity_valueLE_iff]
        right; left
        exact hlt
      · have hp_eq : (playValue G σ₁ τ₁ x).cyclePriority =
            (playValue G σ₂ τ₂ x).cyclePriority :=
          reward_injective heq
        have hx_ne_w2 : x ≠ cycleLeader G σ₂ τ₂ x := by
          rw [hcl_play t]
          exact play_ne_cycleLeader_of_lt_length ht_lt
        have hx_ne_1 : x ≠ cycleLeader G σ₁ τ₁ x := by
          intro hcl_1
          exact hx_ne_w2 (hcl_1.trans (cycleLeader_eq_of_cyclePriority_eq hinj hp_eq))
        have hval_1 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_1
        have hnot_1 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_1
        have hval_2 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_w2
        have hnot_2 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_w2
        change FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x) (playValue G σ₂ τ₂ x)
        rw [hval_1, hval_2]
        apply multiplicity_valueLE_prepend
        · rw [playValue_cyclePriority_step, playValue_cyclePriority_step, hp_eq]
        · exact hnot_1
        · exact hnot_2
        · exact hle_step
  have h0 := hind k le_rfl
  have hkk : k - k = 0 := by omega
  rw [hkk] at h0
  exact h0

lemma le_playValue_of_le_step {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (v : V) :
    ValueLE G (playValue G σ₁ τ₁ v) (playValue G σ₂ τ₂ v) := by
  rw [valueLE_iff_multiplicity_valueLE hinj]
  apply multiplicity_le_playValue_of_le_step hinj
  intro x
  exact (valueLE_iff_multiplicity_valueLE hinj _ _).mp (hstep x)

/-! ### Part 3: Locally Minimizing Optimal Counterstrategy and Monotonicity -/

lemma exists_min_neighbor_list {G : Game V} (hG : WellFormed G)
    (σ : V → V) (x : V) (L : List V) :
    ∃ u : V, G.edge x u ∧ ∀ w ∈ L, G.edge x w →
      ValueLE G (value G σ u) (value G σ w) := by
  induction L with
  | nil =>
    rcases hG.1 x with ⟨u, hu⟩
    refine ⟨u, hu, ?_⟩
    intro w hw
    nomatch hw
  | cons w₁ L ih =>
    rcases ih with ⟨u₂, hu₂, hle₂⟩
    by_cases hw₁ : G.edge x w₁
    · rcases valueLE_total hG.2 (value G σ w₁) (value G σ u₂) with h12 | h21
      · refine ⟨w₁, hw₁, ?_⟩
        intro w hmem hwe
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact valueLE_refl G _
        · exact valueLE_trans hG.2 h12 (hle₂ w hmem' hwe)
      · refine ⟨u₂, hu₂, ?_⟩
        intro w hmem hwe
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact h21
        · exact hle₂ w hmem' hwe
    · refine ⟨u₂, hu₂, ?_⟩
      intro w hmem hwe
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact False.elim (hw₁ hwe)
      · exact hle₂ w hmem' hwe

lemma exists_min_neighbor {G : Game V} (hG : WellFormed G) (σ : V → V) (x : V) :
    ∃ u : V, G.edge x u ∧ ∀ w, G.edge x w →
      ValueLE G (value G σ u) (value G σ w) := by
  rcases exists_min_neighbor_list hG σ x (Finset.univ : Finset V).toList with ⟨u, hu, hle⟩
  exact ⟨u, hu, fun w hw => hle w (Finset.mem_toList.mpr (Finset.mem_univ w)) hw⟩

noncomputable def localCounterstrategy (G : Game V) (hG : WellFormed G)
    (σ : V → V) (x : V) : V :=
  Classical.choose (exists_min_neighbor hG σ x)

lemma localCounterstrategy_legal {G : Game V} (hG : WellFormed G) (σ : V → V) :
    Legal G true (localCounterstrategy G hG σ) :=
  fun x _ => (Classical.choose_spec (exists_min_neighbor hG σ x)).1

lemma localCounterstrategy_min {G : Game V} (hG : WellFormed G) (σ : V → V)
    (x w : V) (hw : G.edge x w) :
    ValueLE G (value G σ (localCounterstrategy G hG σ x)) (value G σ w) :=
  (Classical.choose_spec (exists_min_neighbor hG σ x)).2 w hw

lemma playValue_localCounterstrategy_eq_value {G : Game V} (hG : WellFormed G)
    (σ : V → V) (v : V) :
    playValue G σ (localCounterstrategy G hG σ) v = value G σ v := by
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
  have hle1 : ValueLE G
      (playValue G σ (localCounterstrategy G hG σ) v)
      (playValue G σ τ v) := by
    apply playValue_le_of_step_le hG.2
    intro x
    rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ,
        ← value_eq_playValue_of_optimalCounterstrategy hG hτ]
    unfold step
    split_ifs with hx
    · exact valueLE_refl G _
    · exact localCounterstrategy_min hG σ x (τ x)
        (hτ.1 x (Bool.eq_true_of_not_eq_false hx))
  rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ v] at hle1
  have hle2 := value_le_playValue hG σ (localCounterstrategy_legal hG σ) v
  exact valueLE_antisymm hG.2 hle1 hle2

lemma value_le_of_allowed {G : Game V} (hG : WellFormed G)
    {σ σ' : V → V} (hal : Allowed G σ σ') (v : V) :
    ValueLE G (value G σ v) (value G σ' v) := by
  rcases exists_optimalCounterstrategy G hG σ' with ⟨τ', hτ'⟩
  rw [← playValue_localCounterstrategy_eq_value hG σ v,
      value_eq_playValue_of_optimalCounterstrategy hG hτ' v]
  apply le_playValue_of_le_step hG.2
  intro x
  rw [playValue_localCounterstrategy_eq_value hG σ,
      playValue_localCounterstrategy_eq_value hG σ]
  unfold step
  split_ifs with hx
  · exact hal.2 x hx
  · exact localCounterstrategy_min hG σ x (τ' x)
      (hτ'.1 x (Bool.eq_true_of_not_eq_false hx))

omit [Fintype V] in
lemma prepend_injective_of_notMem {G : Game V} (hinj : Function.Injective G.priority)
    {u : V} {a b : Valuation V} (hua : u ∉ a.path) (hub : u ∉ b.path)
    (heq : prepend G u a = prepend G u b) : a = b := by
  rw [← valEq_iff_eq hinj]
  have hcp : a.cyclePriority = b.cyclePriority := by
    have h := congrArg Valuation.cyclePriority heq
    simpa [prepend] using h
  have hlen : a.length = b.length := by
    have h := congrArg Valuation.length heq
    change a.length + 1 = b.length + 1 at h
    omega
  refine ⟨hcp, ?_, hlen⟩
  intro q
  have hq : count G (prepend G u a).path q = count G (prepend G u b).path q := by
    rw [heq]
  rw [count_prepend_of_notMem hua q, count_prepend_of_notMem hub q, hcp] at hq
  omega

lemma value_lt_of_improving_of_priority_ne_cyclePriority
    {G : Game V} (hG : WellFormed G) {σ σ' : V → V} {v : V}
    (hle : ∀ u, ValueLE G (value G σ u) (value G σ' u))
    (hv : G.owner v = false)
    (hlt : ValueLT G (value G σ (σ v)) (value G σ (σ' v)))
    (hpv : G.priority v ≠ (value G σ (σ v)).cyclePriority) :
    ValueLT G (value G σ v) (value G σ' v) := by
  have hlt_step : ValueLT G (value G σ (σ v)) (value G σ' (σ' v)) :=
    valueLT_of_valueLT_of_valueLE hG.2 hlt (hle (σ' v))
  rcases hle v with heq | hlt_v
  · exfalso
    rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
    rcases exists_optimalCounterstrategy G hG σ' with ⟨τ', hτ'⟩
    have hstep1 : step G σ τ v = σ v := by unfold step; rw [if_pos hv]
    have hstep2 : step G σ' τ' v = σ' v := by unfold step; rw [if_pos hv]
    have hval1 := value_eq_playValue_of_optimalCounterstrategy hG hτ v
    have hval2 := value_eq_playValue_of_optimalCounterstrategy hG hτ' v
    have hval1_s := value_eq_playValue_of_optimalCounterstrategy hG hτ (σ v)
    have hval2_s := value_eq_playValue_of_optimalCounterstrategy hG hτ' (σ' v)
    have hne1 : v ≠ cycleLeader G σ τ v := by
      intro hcl
      apply hpv
      rw [hval1_s, ← hstep1, playValue_cyclePriority_step,
          playValue_cyclePriority_eq_priority_cycleLeader, ← hcl]
    have hcp_eq : (playValue G σ τ v).cyclePriority = (playValue G σ' τ' v).cyclePriority := by
      rw [← hval1, ← hval2, heq]
    have hne2 : v ≠ cycleLeader G σ' τ' v := by
      intro hcl2
      exact hne1 (hcl2.trans (cycleLeader_eq_of_cyclePriority_eq hG.2 hcp_eq.symm))
    have hprep1 := playValue_eq_prepend_of_ne_cycleLeader hne1
    have hnot1 := notMem_playValue_step_path_of_ne_cycleLeader hne1
    have hprep2 := playValue_eq_prepend_of_ne_cycleLeader hne2
    have hnot2 := notMem_playValue_step_path_of_ne_cycleLeader hne2
    rw [hstep1, ← hval1_s] at hprep1 hnot1
    rw [hstep2, ← hval2_s] at hprep2 hnot2
    have hprep_eq : prepend G v (value G σ (σ v)) = prepend G v (value G σ' (σ' v)) := by
      rw [← hprep1, ← hval1, heq, hval2, hprep2]
    have hstep_eq := prepend_injective_of_notMem hG.2 hnot1 hnot2 hprep_eq
    rw [hstep_eq] at hlt_step
    exact valueLT_irrefl hG.2 _ hlt_step
  · exact hlt_v

end StepComparison

theorem improvement_strict {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ σ' : V → V)
    (hσ : Legal G false σ) (hi : Improvable G σ) (hs : Improvement G σ σ') :
    (∀ v, ValueLE G (value G σ v) (value G σ' v)) ∧
    ∃ v, G.owner v = false ∧ ValueLT G (value G σ (σ v)) (value G σ' (σ' v)) := by
  let _ := hσ
  have hle : ∀ v, ValueLE G (value G σ v) (value G σ' v) :=
    value_le_of_allowed hG hs.1
  rcases hs.2 hi with ⟨v, hv_owner, hv_lt⟩
  refine ⟨hle, v, hv_owner, ?_⟩
  exact valueLT_of_valueLT_of_valueLE hG.2 hv_lt (hle (σ' v))

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ σ' : V → V)
    (hσ : Legal G false σ) (hi : Improvable G σ) (hs : Improvement G σ σ') :
    (∀ v, ValueLE G (value G σ v) (value G σ' v)) ∧
    ∃ v, G.owner v = false ∧ ValueLT G (value G σ (σ v)) (value G σ' (σ' v)) :=
  improvement_strict G hG σ σ' hσ hi hs

end FriedmannParity
