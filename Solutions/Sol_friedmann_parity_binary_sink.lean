import Solutions.Sol_friedmann_parity_improvement
import Solutions.Sol_friedmann_parity_transport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace FriedmannParity

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Part 1: General Step, LocalStep, GlobalStep, and Counterstrategy Lemmas -/

lemma value_le_of_step_le {G : Game V} (hWF : WellFormed G) {ρ σ' : V → V}
    (hstep : ∀ v, G.owner v = false → ValueLE G (value G σ' (ρ v)) (value G σ' (σ' v)))
    (v : V) : ValueLE G (value G ρ v) (value G σ' v) := by
  rcases exists_optimalCounterstrategy G hWF σ' with ⟨τ', hτ'⟩
  apply valueLE_trans hWF.2 (value_le_playValue hWF ρ hτ'.1 v)
  rw [value_eq_playValue_of_optimalCounterstrategy hWF hτ' v]
  apply playValue_le_of_step_le hWF.2
  intro x
  rw [← value_eq_playValue_of_optimalCounterstrategy hWF hτ',
      ← value_eq_playValue_of_optimalCounterstrategy hWF hτ']
  unfold step
  split_ifs with hx
  · exact hstep x hx
  · exact valueLE_refl G _

lemma globalStep_of_local_in_next {G : Game V} (hWF : WellFormed G) {σ σ' : V → V}
    (himp : Improvement G σ σ')
    (hnext : ∀ v w, G.owner v = false → G.edge v w →
      ValueLE G (value G σ (σ v)) (value G σ w) →
      ValueLE G (value G σ' w) (value G σ' (σ' v))) :
    GlobalStep G σ σ' := by
  refine ⟨himp, ?_⟩
  intro ρ hρ v
  apply value_le_of_step_le hWF
  intro x hx
  exact hnext x (ρ x) hx (hρ.1 x hx) (hρ.2 x hx)

lemma localStep_of_best_edge {G : Game V} {σ σ' : V → V}
    (hσ : Legal G false σ) (hσ' : Legal G false σ')
    (hstrict : Improvable G σ → ∃ v, G.owner v = false ∧ ValueLT G (value G σ (σ v)) (value G σ (σ' v)))
    (hbest : ∀ v w, G.owner v = false → G.edge v w → ValueLE G (value G σ w) (value G σ (σ' v))) :
    LocalStep G σ σ' :=
  ⟨⟨⟨hσ', fun v hv => hbest v (σ v) hv (hσ v hv)⟩, hstrict⟩, hbest⟩

lemma optimalCounterstrategy_of_min_step {G : Game V} (hWF : WellFormed G) {σ τ : V → V}
    (hτ : Legal G true τ)
    (hmin : ∀ v w, G.owner v = true → G.edge v w → ValueLE G (playValue G σ τ (τ v)) (playValue G σ τ w)) :
    OptimalCounterstrategy G σ τ ∧ ∀ v, value G σ v = playValue G σ τ v := by
  have hopt : OptimalCounterstrategy G σ τ := by
    refine ⟨hτ, ?_⟩
    intro v τ' hτ'
    apply le_playValue_of_le_step hWF.2
    intro x
    unfold step
    split_ifs with hx
    · exact valueLE_refl G _
    · have hx' : G.owner x = true := Bool.eq_true_of_not_eq_false hx
      exact hmin x (τ' x) hx' (hτ' x hx')
  exact ⟨hopt, value_eq_playValue_of_optimalCounterstrategy hWF hopt⟩

/-! ### Part 2: Rank-Based 1-Sink Lemmas -/

lemma iterate_step_eq_sink_of_rank_le {G : Game V} {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v) :
    ∀ k v, rank v ≤ k → (step G σ τ)^[k] v = sink
  | 0, v, hk => by
    by_contra hv
    have hlt := hrank_step v hv
    omega
  | k + 1, v, hk => by
    rw [Function.iterate_succ_apply]
    by_cases hv : v = sink
    · subst hv
      rw [hsink_step]
      exact Function.iterate_fixed hsink_step k
    · have hlt := hrank_step v hv
      exact iterate_step_eq_sink_of_rank_le hsink_step rank hrank_step k (step G σ τ v) (by omega)

lemma reaches_sink_of_rank {G : Game V} {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    (v : V) : ∃ k, (step G σ τ)^[k] v = sink :=
  ⟨rank v, iterate_step_eq_sink_of_rank_le hsink_step rank hrank_step (rank v) v le_rfl⟩

lemma mem_recurring_eq_sink_of_rank {G : Game V} {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    {v u : V} (hu : u ∈ recurring (play G σ τ v)) : u = sink := by
  rw [mem_recurring_iff] at hu
  rcases hu (rank v) with ⟨k, hvk, hk⟩
  rw [play_eq_iterate] at hk
  have hsink := iterate_step_eq_sink_of_rank_le hsink_step rank hrank_step k v hvk
  exact hk.symm.trans hsink

lemma cycleLeader_eq_sink_of_rank {G : Game V} (_hWF : WellFormed G) {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    (v : V) : cycleLeader G σ τ v = sink :=
  mem_recurring_eq_sink_of_rank hsink_step rank hrank_step (cycleLeader_mem_recurring G σ τ v)

lemma cyclePriority_eq_one_of_rank {G : Game V} (hWF : WellFormed G) {σ τ : V → V} {sink : V}
    (hsink_prio : G.priority sink = 1)
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    (v : V) : (playValue G σ τ v).cyclePriority = 1 := by
  rw [playValue_cyclePriority_eq_priority_cycleLeader,
      cycleLeader_eq_sink_of_rank hWF hsink_step rank hrank_step v,
      hsink_prio]

lemma path_sink_of_rank {G : Game V} (hWF : WellFormed G) {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v) :
    (playValue G σ τ sink).path = ∅ := by
  have hcl : sink = cycleLeader G σ τ sink :=
    (cycleLeader_eq_sink_of_rank hWF hsink_step rank hrank_step sink).symm
  have hval := playValue_eq_of_eq_cycleLeader hcl
  exact congrArg Valuation.path hval

lemma path_step_of_rank {G : Game V} (hWF : WellFormed G) {σ τ : V → V} {sink : V}
    (hsink_prio : G.priority sink = 1)
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    (hprio_gt : ∀ v, v ≠ sink → 1 < G.priority v)
    (v : V) (hv : v ≠ sink) :
    (playValue G σ τ v).path = insert v (playValue G σ τ (step G σ τ v)).path := by
  have hcl : v ≠ cycleLeader G σ τ v := by
    rw [cycleLeader_eq_sink_of_rank hWF hsink_step rank hrank_step v]
    exact hv
  have hprep := congrArg Valuation.path (playValue_eq_prepend_of_ne_cycleLeader hcl)
  dsimp [prepend] at hprep
  have hcp := cyclePriority_eq_one_of_rank hWF hsink_prio hsink_step rank hrank_step (step G σ τ v)
  rw [hcp, if_pos (hprio_gt v hv)] at hprep
  exact hprep

lemma rank_step_le_of_rank {G : Game V} {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    (v : V) : rank (step G σ τ v) ≤ rank v := by
  by_cases hv : v = sink
  · subst hv
    rw [hsink_step]
  · exact le_of_lt (hrank_step v hv)

lemma rank_play_le_of_rank {G : Game V} {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    (w : V) : ∀ t : ℕ, rank (play G σ τ w t) ≤ rank w
  | 0 => le_rfl
  | t + 1 => by
    rw [play_succ']
    exact le_trans
      (rank_step_le_of_rank hsink_step rank hrank_step (play G σ τ w t))
      (rank_play_le_of_rank hsink_step rank hrank_step w t)

lemma rank_le_of_mem_path {G : Game V} (_hWF : WellFormed G) {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    (w v : V) (hv : v ∈ (playValue G σ τ w).path) :
    rank v ≤ rank w := by
  rw [mem_playValue_path_iff] at hv
  rcases hv with ⟨⟨t, _, rfl⟩, _⟩
  exact rank_play_le_of_rank hsink_step rank hrank_step w t

lemma not_mem_path_of_rank_lt {G : Game V} (hWF : WellFormed G) {σ τ : V → V} {sink : V}
    (hsink_step : step G σ τ sink = sink)
    (rank : V → ℕ)
    (hrank_step : ∀ v, v ≠ sink → rank (step G σ τ v) < rank v)
    (w v : V) (hlt : rank w < rank v) :
    v ∉ (playValue G σ τ w).path := by
  intro hv
  have hle := rank_le_of_mem_path hWF hsink_step rank hrank_step w v hv
  omega

/-! ### Part 3: Priority-Comparison Helpers for `SetLT` and `ValueLT` -/

lemma setLT_of_top_diff_even {G : Game V} (_hinj : Function.Injective G.priority)
    {A B : Finset V} {d : V}
    (hdA : d ∉ A) (hdB : d ∈ B) (heven : G.priority d % 2 = 0)
    (htop : ∀ x, G.priority d < G.priority x → (x ∈ A ↔ x ∈ B)) :
    SetLT G A B := by
  refine ⟨d, ?_, ?_, Or.inl ⟨heven, hdB⟩⟩
  · rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
    exact Or.inr ⟨hdB, hdA⟩
  · intro u hu
    by_contra hlt
    have hgt : G.priority d < G.priority u := by omega
    have hiff := htop u hgt
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hu
    rcases hu with ⟨huA, huB⟩ | ⟨huB, huA⟩
    · exact huB (hiff.mp huA)
    · exact huA (hiff.mpr huB)

lemma setLT_of_top_diff_odd {G : Game V} (_hinj : Function.Injective G.priority)
    {A B : Finset V} {d : V}
    (hdA : d ∈ A) (hdB : d ∉ B) (hodd : G.priority d % 2 = 1)
    (htop : ∀ x, G.priority d < G.priority x → (x ∈ A ↔ x ∈ B)) :
    SetLT G A B := by
  refine ⟨d, ?_, ?_, Or.inr ⟨hodd, hdA⟩⟩
  · rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
    exact Or.inl ⟨hdA, hdB⟩
  · intro u hu
    by_contra hlt
    have hgt : G.priority d < G.priority u := by omega
    have hiff := htop u hgt
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hu
    rcases hu with ⟨huA, huB⟩ | ⟨huB, huA⟩
    · exact huB (hiff.mp huA)
    · exact huA (hiff.mpr huB)

lemma valueLT_of_setLT_of_cyclePriority_eq_one {G : Game V}
    {a b : Valuation V}
    (ha : a.cyclePriority = 1) (hb : b.cyclePriority = 1)
    (hset : SetLT G a.path b.path) :
    ValueLT G a b :=
  Or.inr (Or.inl ⟨ha.trans hb.symm, hset⟩)

/-! ### Part 4: Uniqueness of `LocalStep` and `GlobalStep` when `cyclePriority = 1` -/

lemma step_congr_on_false {G : Game V} {σ₁ σ₂ : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) (τ : V → V) (v : V) :
    step G σ₁ τ v = step G σ₂ τ v := by
  unfold step
  split_ifs with hv
  · exact hσ v hv
  · rfl

lemma play_congr_on_false {G : Game V} {σ₁ σ₂ : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) (τ : V → V) (v : V) :
    play G σ₁ τ v = play G σ₂ τ v := by
  ext t
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [play_succ, play_succ, step_congr_on_false hσ τ v, ih]

lemma playValue_congr_on_false {G : Game V} {σ₁ σ₂ : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) (τ : V → V) (v : V) :
    playValue G σ₁ τ v = playValue G σ₂ τ v := by
  classical
  unfold playValue
  simp only [play_congr_on_false hσ τ v]

lemma value_congr_on_false {G : Game V} (hWF : WellFormed G) {σ₁ σ₂ : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) (v : V) :
    value G σ₁ v = value G σ₂ v := by
  rcases exists_optimalCounterstrategy G hWF σ₁ with ⟨τ₁, hτ₁⟩
  rcases exists_optimalCounterstrategy G hWF σ₂ with ⟨τ₂, hτ₂⟩
  apply valueLE_antisymm hWF.2
  · have hle := value_le_playValue hWF σ₁ hτ₂.1 v
    rw [playValue_congr_on_false hσ τ₂ v,
        ← value_eq_playValue_of_optimalCounterstrategy hWF hτ₂ v] at hle
    exact hle
  · have hle := value_le_playValue hWF σ₂ hτ₁.1 v
    rw [← playValue_congr_on_false hσ τ₁ v,
        ← value_eq_playValue_of_optimalCounterstrategy hWF hτ₁ v] at hle
    exact hle

lemma cycleLeader_eq_sink_of_priority_one {G : Game V} (hWF : WellFormed G)
    {sink : V} (hsink_prio : G.priority sink = 1)
    {σ τ : V → V} {v : V} (hcp : (playValue G σ τ v).cyclePriority = 1) :
    cycleLeader G σ τ v = sink := by
  apply hWF.2
  rw [← playValue_cyclePriority_eq_priority_cycleLeader, hcp, hsink_prio]

lemma eq_of_playValue_eq_of_cyclePriority_eq_one {G : Game V} (hWF : WellFormed G)
    {sink : V} (hsink_prio : G.priority sink = 1)
    (hprio_gt : ∀ v, v ≠ sink → 1 < G.priority v)
    {σ τ : V → V} {u w : V}
    (hcp_u : (playValue G σ τ u).cyclePriority = 1)
    (hcp_w : (playValue G σ τ w).cyclePriority = 1)
    (heq : playValue G σ τ u = playValue G σ τ w) :
    u = w := by
  have hlen : (playValue G σ τ u).length = (playValue G σ τ w).length :=
    congrArg Valuation.length heq
  have hpath : (playValue G σ τ u).path = (playValue G σ τ w).path :=
    congrArg Valuation.path heq
  rcases Nat.eq_zero_or_pos (playValue G σ τ u).length with h0 | hpos
  · have hu : u = sink := by
      have h1 := play_playValue_length G σ τ u
      rw [h0, play_zero, cycleLeader_eq_sink_of_priority_one hWF hsink_prio hcp_u] at h1
      exact h1
    have hw : w = sink := by
      have h2 := play_playValue_length G σ τ w
      rw [← hlen, h0, play_zero, cycleLeader_eq_sink_of_priority_one hWF hsink_prio hcp_w] at h2
      exact h2
    exact hu.trans hw.symm
  · have hu_ne : u ≠ sink := by
      have hne := play_ne_cycleLeader_of_lt_length hpos
      rwa [play_zero, cycleLeader_eq_sink_of_priority_one hWF hsink_prio hcp_u] at hne
    have hu_mem : u ∈ (playValue G σ τ u).path := by
      rw [mem_playValue_path_iff, hcp_u]
      exact ⟨⟨0, hpos, rfl⟩, hprio_gt u hu_ne⟩
    rw [hpath, mem_playValue_path_iff] at hu_mem
    rcases hu_mem with ⟨⟨t, ht, hplay⟩, _⟩
    have hle := playValue_length_play_le G σ τ w (le_of_lt ht)
    rw [hplay, ← hlen] at hle
    have ht0 : t = 0 := by omega
    rw [ht0, play_zero] at hplay
    exact hplay.symm

lemma value_injective_of_cyclePriority_eq_one {G : Game V} (hWF : WellFormed G)
    {σ : V → V} {sink : V}
    (hcp : ∀ v, (value G σ v).cyclePriority = 1)
    (_hsink_edge : G.edge sink sink)
    (hsink_prio : G.priority sink = 1)
    (hprio_gt : ∀ v, v ≠ sink → 1 < G.priority v)
    (_hσ : Legal G false σ)
    {u w : V} (heq : value G σ u = value G σ w) :
    u = w := by
  rcases exists_optimalCounterstrategy G hWF σ with ⟨τ, hτ⟩
  have hval := value_eq_playValue_of_optimalCounterstrategy hWF hτ
  have hcp_u : (playValue G σ τ u).cyclePriority = 1 := by
    rw [← hval u]; exact hcp u
  have hcp_w : (playValue G σ τ w).cyclePriority = 1 := by
    rw [← hval w]; exact hcp w
  have hpv_eq : playValue G σ τ u = playValue G σ τ w := by
    rw [← hval u, ← hval w, heq]
  exact eq_of_playValue_eq_of_cyclePriority_eq_one hWF hsink_prio hprio_gt hcp_u hcp_w hpv_eq

lemma localStep_eq_on_false {G : Game V} (hWF : WellFormed G)
    {σ σ₁ σ₂ : V → V} {sink : V}
    (hcp : ∀ v, (value G σ v).cyclePriority = 1)
    (hsink_edge : G.edge sink sink)
    (hsink_prio : G.priority sink = 1)
    (hprio_gt : ∀ v, v ≠ sink → 1 < G.priority v)
    (hσ : Legal G false σ)
    (hloc₁ : LocalStep G σ σ₁) (hloc₂ : LocalStep G σ σ₂)
    (v : V) (hv : G.owner v = false) :
    σ₁ v = σ₂ v := by
  have he₁ : G.edge v (σ₁ v) := hloc₁.1.1.1 v hv
  have he₂ : G.edge v (σ₂ v) := hloc₂.1.1.1 v hv
  have hle₁₂ : ValueLE G (value G σ (σ₁ v)) (value G σ (σ₂ v)) := hloc₂.2 v (σ₁ v) hv he₁
  have hle₂₁ : ValueLE G (value G σ (σ₂ v)) (value G σ (σ₁ v)) := hloc₁.2 v (σ₂ v) hv he₂
  have heq : value G σ (σ₁ v) = value G σ (σ₂ v) := valueLE_antisymm hWF.2 hle₁₂ hle₂₁
  exact value_injective_of_cyclePriority_eq_one hWF hcp hsink_edge hsink_prio hprio_gt hσ heq

lemma step_sink_eq_sink_of_priority_one {G : Game V} (hWF : WellFormed G)
    {sink : V} (hsink_prio : G.priority sink = 1)
    (hprio_gt : ∀ v, v ≠ sink → 1 < G.priority v)
    {σ τ : V → V} {v : V} (hcp : (playValue G σ τ v).cyclePriority = 1) :
    step G σ τ sink = sink := by
  have hcl := cycleLeader_eq_sink_of_priority_one hWF hsink_prio hcp
  have hmem : sink ∈ recurring (play G σ τ v) := hcl ▸ cycleLeader_mem_recurring G σ τ v
  have hstep_mem : step G σ τ sink ∈ recurring (play G σ τ v) := step_mem_recurring hmem
  have hle : G.priority (step G σ τ sink) ≤ (playValue G σ τ v).cyclePriority :=
    Finset.le_sup hstep_mem
  by_contra hne
  have hgt := hprio_gt (step G σ τ sink) hne
  omega

lemma eq_on_false_of_value_eq_of_cyclePriority_eq_one {G : Game V} (hWF : WellFormed G)
    {σ₁ σ₂ : V → V} {sink : V}
    (hcp₁ : ∀ v, (value G σ₁ v).cyclePriority = 1)
    (hsink_edge : G.edge sink sink)
    (hsink_prio : G.priority sink = 1)
    (hprio_gt : ∀ v, v ≠ sink → 1 < G.priority v)
    (hσ₁ : Legal G false σ₁)
    (hval_eq : ∀ u, value G σ₁ u = value G σ₂ u)
    (v : V) (hv : G.owner v = false) :
    σ₁ v = σ₂ v := by
  rcases exists_optimalCounterstrategy G hWF σ₁ with ⟨τ₁, hτ₁⟩
  rcases exists_optimalCounterstrategy G hWF σ₂ with ⟨τ₂, hτ₂⟩
  have hval₁ := value_eq_playValue_of_optimalCounterstrategy hWF hτ₁
  have hval₂ := value_eq_playValue_of_optimalCounterstrategy hWF hτ₂
  have hstep₁ : step G σ₁ τ₁ v = σ₁ v := by unfold step; rw [if_pos hv]
  have hstep₂ : step G σ₂ τ₂ v = σ₂ v := by unfold step; rw [if_pos hv]
  by_cases hvsink : v = sink
  · subst hvsink
    have hcp_pv₁ : (playValue G σ₁ τ₁ v).cyclePriority = 1 := by
      rw [← hval₁ v]; exact hcp₁ v
    have hcp_pv₂ : (playValue G σ₂ τ₂ v).cyclePriority = 1 := by
      rw [← hval₂ v, ← hval_eq v]; exact hcp₁ v
    have hs₁ := step_sink_eq_sink_of_priority_one hWF hsink_prio hprio_gt hcp_pv₁
    have hs₂ := step_sink_eq_sink_of_priority_one hWF hsink_prio hprio_gt hcp_pv₂
    rw [← hstep₁, hs₁, ← hstep₂, hs₂]
  · have hcp_pv₁ : (playValue G σ₁ τ₁ v).cyclePriority = 1 := by
      rw [← hval₁ v]; exact hcp₁ v
    have hcp_pv₂ : (playValue G σ₂ τ₂ v).cyclePriority = 1 := by
      rw [← hval₂ v, ← hval_eq v]; exact hcp₁ v
    have hne₁ : v ≠ cycleLeader G σ₁ τ₁ v := by
      rw [cycleLeader_eq_sink_of_priority_one hWF hsink_prio hcp_pv₁]
      exact hvsink
    have hne₂ : v ≠ cycleLeader G σ₂ τ₂ v := by
      rw [cycleLeader_eq_sink_of_priority_one hWF hsink_prio hcp_pv₂]
      exact hvsink
    have hprep₁ := playValue_eq_prepend_of_ne_cycleLeader hne₁
    have hnot₁ := notMem_playValue_step_path_of_ne_cycleLeader hne₁
    have hprep₂ := playValue_eq_prepend_of_ne_cycleLeader hne₂
    have hnot₂ := notMem_playValue_step_path_of_ne_cycleLeader hne₂
    rw [hstep₁, ← hval₁ (σ₁ v)] at hprep₁ hnot₁
    rw [hstep₂, ← hval₂ (σ₂ v), ← hval_eq (σ₂ v)] at hprep₂ hnot₂
    have hprep_eq : prepend G v (value G σ₁ (σ₁ v)) = prepend G v (value G σ₁ (σ₂ v)) := by
      rw [← hprep₁, ← hval₁ v, hval_eq v, hval₂ v, hprep₂]
    have hstep_val_eq := prepend_injective_of_notMem hWF.2 hnot₁ hnot₂ hprep_eq
    exact value_injective_of_cyclePriority_eq_one hWF hcp₁ hsink_edge hsink_prio hprio_gt hσ₁ hstep_val_eq

lemma globalStep_eq_on_false {G : Game V} (hWF : WellFormed G)
    {σ σ₁ σ₂ : V → V} {sink : V}
    (hcp₁ : ∀ v, (value G σ₁ v).cyclePriority = 1)
    (hsink_edge : G.edge sink sink)
    (hsink_prio : G.priority sink = 1)
    (hprio_gt : ∀ v, v ≠ sink → 1 < G.priority v)
    (hglob₁ : GlobalStep G σ σ₁) (hglob₂ : GlobalStep G σ σ₂)
    (v : V) (hv : G.owner v = false) :
    σ₁ v = σ₂ v := by
  have hval_eq : ∀ u, value G σ₁ u = value G σ₂ u := by
    intro u
    exact valueLE_antisymm hWF.2 (hglob₂.2 σ₁ hglob₁.1.1 u) (hglob₁.2 σ₂ hglob₂.1.1 u)
  exact eq_on_false_of_value_eq_of_cyclePriority_eq_one
    hWF hcp₁ hsink_edge hsink_prio hprio_gt hglob₁.1.1.1 hval_eq v hv

lemma globalStep_eq_on_false_of_local_in_next {G : Game V} (hWF : WellFormed G)
    {σ σ₁ σ₂ : V → V} {sink : V}
    (hcp₁ : ∀ v, (value G σ₁ v).cyclePriority = 1)
    (hsink_edge : G.edge sink sink)
    (hsink_prio : G.priority sink = 1)
    (hprio_gt : ∀ v, v ≠ sink → 1 < G.priority v)
    (hglob₁ : GlobalStep G σ σ₁) (hglob₂ : GlobalStep G σ σ₂)
    (_hnext : ∀ v w, G.owner v = false → G.edge v w →
      ValueLE G (value G σ (σ v)) (value G σ w) →
      ValueLE G (value G σ₁ w) (value G σ₁ (σ₁ v)))
    (v : V) (hv : G.owner v = false) :
    σ₁ v = σ₂ v :=
  globalStep_eq_on_false hWF hcp₁ hsink_edge hsink_prio hprio_gt hglob₁ hglob₂ v hv

end FriedmannParity
