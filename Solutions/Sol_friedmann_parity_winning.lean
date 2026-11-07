import Definitions.Def_friedmann_parity
import Solutions.Sol_friedmann_parity_counterstrategy

set_option autoImplicit false

namespace FriedmannParity

open FriedmannMultiplicity

section StepComparison

variable {V : Type} [Fintype V] [DecidableEq V]

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

lemma playValue_le_of_optimalCounterstrategy_of_not_improvable
    {G : Game V} (hG : WellFormed G) {σ τ ρ : V → V}
    (hstop : ¬ Improvable G σ)
    (hτ : OptimalCounterstrategy G σ τ)
    (hρ : Legal G false ρ) (v : V) :
    ValueLE G (playValue G ρ τ v) (playValue G σ τ v) := by
  apply playValue_le_of_step_le hG.2
  intro x
  rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ,
      ← value_eq_playValue_of_optimalCounterstrategy hG hτ]
  unfold step
  split_ifs with hx
  · rw [valueLE_iff_not_valueLT hG.2]
    intro hlt
    exact hstop ⟨x, ρ x, hx, hρ x hx, hlt⟩
  · exact valueLE_refl G _

omit [Fintype V] in
lemma cyclePriority_even_of_zero_le_reward {p : ℕ} (h : 0 ≤ reward p) :
    p % 2 = 0 := by
  unfold reward at h
  split_ifs at h with hp
  · exact hp
  · omega

omit [Fintype V] in
lemma zero_le_reward_of_cyclePriority_even {p : ℕ} (h : p % 2 = 0) :
    0 ≤ reward p := by
  unfold reward
  rw [if_pos h]
  omega

omit [Fintype V] in
lemma cyclePriority_odd_of_reward_lt_zero {p : ℕ} (h : reward p < 0) :
    p % 2 = 1 := by
  unfold reward at h
  split_ifs at h with hp
  · omega
  · omega

omit [Fintype V] in
lemma reward_lt_zero_of_cyclePriority_odd {p : ℕ} (h : p % 2 = 1) :
    reward p < 0 := by
  unfold reward
  rw [if_neg (by omega)]
  omega

lemma not_wins_false_and_true {G : Game V} {σ τ : V → V} {v : V}
    (h0 : Wins G false σ v) (h1 : Wins G true τ v) : False := by
  have hp0 := h0.2 τ h1.1
  have hp1 := h1.2 σ h0.1
  simp only [↓reduceIte, Bool.true_eq_false] at hp0 hp1
  omega

end StepComparison

theorem nonimprovable_solves {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V)
    (hσ : Legal G false σ) (hstop : ¬ Improvable G σ) :
    (WinningRegion G false = {v | (value G σ v).cyclePriority % 2 = 0}) ∧
    (WinningRegion G true = {v | (value G σ v).cyclePriority % 2 = 1}) ∧
    (∀ v, (value G σ v).cyclePriority % 2 = 0 → Wins G false σ v) ∧
    (∀ τ, OptimalCounterstrategy G σ τ →
      ∀ v, (value G σ v).cyclePriority % 2 = 1 → Wins G true τ v) ∧
    (∀ ρ, Legal G false ρ → ∀ v, ValueLE G (value G ρ v) (value G σ v)) := by
  have hwin0 : ∀ v, (value G σ v).cyclePriority % 2 = 0 → Wins G false σ v := by
    intro v heven
    refine ⟨hσ, ?_⟩
    intro τ' hτ'
    simp only [↓reduceIte]
    have hle := value_le_playValue hG σ hτ' v
    have hrew := reward_cyclePriority_le_of_valueLE hle
    have h0 := zero_le_reward_of_cyclePriority_even heven
    exact cyclePriority_even_of_zero_le_reward (le_trans h0 hrew)
  have hwin1 : ∀ τ, OptimalCounterstrategy G σ τ →
      ∀ v, (value G σ v).cyclePriority % 2 = 1 → Wins G true τ v := by
    intro τ hτ v hodd
    refine ⟨hτ.1, ?_⟩
    intro ρ hρ
    simp only [Bool.true_eq_false, ↓reduceIte]
    have hle := playValue_le_of_optimalCounterstrategy_of_not_improvable hG hstop hτ hρ v
    rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ v] at hle
    have hrew := reward_cyclePriority_le_of_valueLE hle
    have hlt := reward_lt_zero_of_cyclePriority_odd hodd
    exact cyclePriority_odd_of_reward_lt_zero (lt_of_le_of_lt hrew hlt)
  have hopt_val : ∀ ρ, Legal G false ρ → ∀ v, ValueLE G (value G ρ v) (value G σ v) := by
    intro ρ hρ v
    rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
    have h1 := value_le_playValue hG ρ hτ.1 v
    have h2 := playValue_le_of_optimalCounterstrategy_of_not_improvable hG hstop hτ hρ v
    rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ v] at h2
    exact valueLE_trans hG.2 h1 h2
  have hreg0 : WinningRegion G false = {v | (value G σ v).cyclePriority % 2 = 0} := by
    ext v
    change (∃ ρ, Wins G false ρ v) ↔ (value G σ v).cyclePriority % 2 = 0
    constructor
    · rintro ⟨ρ, hρ⟩
      rcases Nat.mod_two_eq_zero_or_one (value G σ v).cyclePriority with heven | hodd
      · exact heven
      · rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
        exact False.elim (not_wins_false_and_true hρ (hwin1 τ hτ v hodd))
    · intro heven
      exact ⟨σ, hwin0 v heven⟩
  have hreg1 : WinningRegion G true = {v | (value G σ v).cyclePriority % 2 = 1} := by
    ext v
    change (∃ τ, Wins G true τ v) ↔ (value G σ v).cyclePriority % 2 = 1
    constructor
    · rintro ⟨τ, hτ⟩
      rcases Nat.mod_two_eq_zero_or_one (value G σ v).cyclePriority with heven | hodd
      · exact False.elim (not_wins_false_and_true (hwin0 v heven) hτ)
      · exact hodd
    · intro hodd
      rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
      exact ⟨τ, hwin1 τ hτ v hodd⟩
  exact ⟨hreg0, hreg1, hwin0, hwin1, hopt_val⟩

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V)
    (hσ : Legal G false σ) (hstop : ¬ Improvable G σ) :
    (WinningRegion G false = {v | (value G σ v).cyclePriority % 2 = 0}) ∧
    (WinningRegion G true = {v | (value G σ v).cyclePriority % 2 = 1}) ∧
    (∀ v, (value G σ v).cyclePriority % 2 = 0 → Wins G false σ v) ∧
    (∀ τ, OptimalCounterstrategy G σ τ →
      ∀ v, (value G σ v).cyclePriority % 2 = 1 → Wins G true τ v) ∧
    (∀ ρ, Legal G false ρ → ∀ v, ValueLE G (value G ρ v) (value G σ v)) :=
  nonimprovable_solves G hG σ hσ hstop

end FriedmannParity
