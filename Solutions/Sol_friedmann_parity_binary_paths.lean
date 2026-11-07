import Solutions.Sol_friedmann_parity_binary_state

set_option autoImplicit false
set_option linter.unusedVariables false

namespace FriedmannParity

/-! ### Part 1: Priority Parities, Bounds, and Ladder Portal Lemmas -/

lemma shift_bin_even (n : ℕ) : shift_bin n % 2 = 0 := by
  dsimp [shift_bin, baseL_bin, M_bin]
  omega

lemma top_bin_even (n : ℕ) : top_bin n % 2 = 0 := by
  have h := shift_bin_even n
  dsimp [top_bin, Na_bin, M_bin]
  omega

lemma prio_z_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.z i) % 2 = 1 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_f_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.f i) % 2 = 1 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_k_even (n : ℕ) (i : Fin n) : (G_bin n).priority (.k i) % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_s_even (n : ℕ) : (G_bin n).priority .s % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_r_even (n : ℕ) : (G_bin n).priority .r % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_c_even (n : ℕ) : (G_bin n).priority .c % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_g_even (n : ℕ) (i : Fin n) : (G_bin n).priority (.g i) % 2 = 0 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_hy_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.hy i) % 2 = 1 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_hx_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.hx i) % 2 = 1 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_h_even (n : ℕ) (i : Fin n) : (G_bin n).priority (.h i) % 2 = 0 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_ge_c_iff (n : ℕ) (u : V_bin n) :
    (G_bin n).priority .c ≤ (G_bin n).priority u ↔
      u = .c ∨ u = .r ∨ u = .s ∨ ∃ j : Fin n, u = .z j ∨ u = .f j ∨ u = .k j := by
  constructor
  · intro h
    cases u with
    | c => exact Or.inl rfl
    | r => exact Or.inr (Or.inl rfl)
    | s => exact Or.inr (Or.inr (Or.inl rfl))
    | z j => exact Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩))
    | f j => exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inl rfl)⟩))
    | k j => exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr rfl)⟩))
    | _ =>
      exfalso
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin] at h
      try split_ifs at h
      all_goals omega
  · rintro (rfl | rfl | rfl | ⟨j, rfl | rfl | rfl⟩) <;>
    { dsimp [G_bin, priority_bin]; omega }

lemma prio_gt_s_iff (n : ℕ) (u : V_bin n) :
    (G_bin n).priority .s < (G_bin n).priority u ↔
      ∃ j : Fin n, u = .z j ∨ u = .f j ∨ u = .k j := by
  constructor
  · intro h
    rcases (prio_ge_c_iff n u).mp (by dsimp [G_bin, priority_bin] at h ⊢; omega) with
      rfl | rfl | rfl | hj
    · dsimp [G_bin, priority_bin] at h; omega
    · dsimp [G_bin, priority_bin] at h; omega
    · dsimp [G_bin, priority_bin] at h; omega
    · exact hj
  · rintro ⟨j, rfl | rfl | rfl⟩ <;>
    { dsimp [G_bin, priority_bin]; omega }

def InLadderCore (n : ℕ) : V_bin n → Prop
  | .lp1 _ | .lp2 _ | .lp3 _ | .l1 _ | .l2 _ | .l3 _
  | .b _ | .a _ | .r_2_odd | .r_2 | .r_a | .c_odd => True
  | _ => False

lemma inLadderCore_ne_x (n : ℕ) (w : V_bin n) (hw : InLadderCore n w) : w ≠ .x := by
  cases w <;> simp [InLadderCore] at hw ⊢

lemma inLadderCore_prio_lt_c (n : ℕ) (w : V_bin n) (hw : InLadderCore n w) :
    (G_bin n).priority w < (G_bin n).priority .c := by
  cases w <;> simp [InLadderCore] at hw
  all_goals
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]
    try split_ifs
    all_goals omega

lemma inLadderCore_step (glob : Bool) (n b s : ℕ) (w : V_bin n) (hw : InLadderCore n w) :
    let w' := step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w
    w' = .c ∨ w' = .r ∨ InLadderCore n w' := by
  cases w <;> simp [InLadderCore] at hw
  all_goals
    dsimp [step, G_bin, owner_bin, predState0, predTau0, chooseTauEdge1, edge0, edge1]
    repeat' split_ifs
    all_goals simp [InLadderCore]

lemma hitsPortal_of_inLadderCore (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    ∀ k w, predRank0 glob n b s w ≤ k → InLadderCore n w →
      HitsPortal glob n b s w .c ∨ HitsPortal glob n b s w .r
  | 0, w, hk, hw => by
    exfalso
    have hlt := predRank0_step_lt glob n b s hvalid w (inLadderCore_ne_x n w hw)
    omega
  | k + 1, w, hk, hw => by
    have hne := inLadderCore_ne_x n w hw
    have hprio := inLadderCore_prio_lt_c n w hw
    have hlt := predRank0_step_lt glob n b s hvalid w hne
    rcases inLadderCore_step glob n b s w hw with hstep | hstep | hstep
    · left
      apply hitsPortal_of_step glob n b s hvalid w .c hne hprio
      rw [hstep]
      exact hitsPortal_refl glob n b s hvalid .c (by nofun)
    · right
      apply hitsPortal_of_step glob n b s hvalid w .r hne hprio
      rw [hstep]
      exact hitsPortal_refl glob n b s hvalid .r (by nofun)
    · rcases hitsPortal_of_inLadderCore glob n b s hvalid k _ (by omega) hstep with hc | hr
      · left; exact hitsPortal_of_step glob n b s hvalid w .c hne hprio hc
      · right; exact hitsPortal_of_step glob n b s hvalid w .r hne hprio hr

lemma not_both_d2_d3_of_not_dClosed0 (glob : Bool) (n b s : ℕ) (i : Fin n)
    (hd : dClosed0 n b s i = false)
    (hd2 : chooseEdge1 glob n b s (.d2 i) = true) :
    chooseEdge1 glob n b s (.d3 i) = false := by
  unfold dClosed0 at hd
  dsimp [chooseEdge1] at hd2 ⊢
  cases hbit : b.testBit i.val with
  | true =>
    simp [hbit] at hd
    simp [hbit, hd] at hd2
  | false =>
    simp [hbit] at hd hd2 ⊢
    omega

lemma hitsPortal_d1_of_not_dClosed0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hd : dClosed0 n b s i = false) :
    HitsPortal glob n b s (.d1 i) .c ∨ HitsPortal glob n b s (.d1 i) .r := by
  have hp1 : (G_bin n).priority (.d1 i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  have hp2 : (G_bin n).priority (.d2 i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  have hp3 : (G_bin n).priority (.d3 i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  by_cases hc1 : chooseEdge1 glob n b s (.d1 i) = true
  · have hs1 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i) = .d2 i := by
      dsimp [step, G_bin, owner_bin, predState0]; rw [if_pos hc1]; rfl
    by_cases hc2 : chooseEdge1 glob n b s (.d2 i) = true
    · have hs2 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i) = .d3 i := by
        dsimp [step, G_bin, owner_bin, predState0]; rw [if_pos hc2]; rfl
      have hc3 := not_both_d2_d3_of_not_dClosed0 glob n b s i hd hc2
      have hs3 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d3 i) = .lp3 (tap_bin n i) := by
        dsimp [step, G_bin, owner_bin, predState0]; rw [hc3]; rfl
      rcases hitsPortal_of_inLadderCore glob n b s hvalid _ (.lp3 (tap_bin n i)) le_rfl trivial with h | h
      · left
        apply hitsPortal_of_step glob n b s hvalid (.d1 i) .c (by nofun) hp1
        rw [hs1]
        apply hitsPortal_of_step glob n b s hvalid (.d2 i) .c (by nofun) hp2
        rw [hs2]
        apply hitsPortal_of_step glob n b s hvalid (.d3 i) .c (by nofun) hp3
        rw [hs3]; exact h
      · right
        apply hitsPortal_of_step glob n b s hvalid (.d1 i) .r (by nofun) hp1
        rw [hs1]
        apply hitsPortal_of_step glob n b s hvalid (.d2 i) .r (by nofun) hp2
        rw [hs2]
        apply hitsPortal_of_step glob n b s hvalid (.d3 i) .r (by nofun) hp3
        rw [hs3]; exact h
    · have hc2' : chooseEdge1 glob n b s (.d2 i) = false := Bool.eq_false_of_not_eq_true hc2
      have hs2 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i) = .lp2 (tap_bin n i) := by
        dsimp [step, G_bin, owner_bin, predState0]; rw [hc2']; rfl
      rcases hitsPortal_of_inLadderCore glob n b s hvalid _ (.lp2 (tap_bin n i)) le_rfl trivial with h | h
      · left
        apply hitsPortal_of_step glob n b s hvalid (.d1 i) .c (by nofun) hp1
        rw [hs1]
        apply hitsPortal_of_step glob n b s hvalid (.d2 i) .c (by nofun) hp2
        rw [hs2]; exact h
      · right
        apply hitsPortal_of_step glob n b s hvalid (.d1 i) .r (by nofun) hp1
        rw [hs1]
        apply hitsPortal_of_step glob n b s hvalid (.d2 i) .r (by nofun) hp2
        rw [hs2]; exact h
  · have hc1' : chooseEdge1 glob n b s (.d1 i) = false := Bool.eq_false_of_not_eq_true hc1
    have hs1 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i) = .lp1 (tap_bin n i) := by
      dsimp [step, G_bin, owner_bin, predState0]; rw [hc1']; rfl
    rcases hitsPortal_of_inLadderCore glob n b s hvalid _ (.lp1 (tap_bin n i)) le_rfl trivial with h | h
    · left
      apply hitsPortal_of_step glob n b s hvalid (.d1 i) .c (by nofun) hp1
      rw [hs1]; exact h
    · right
      apply hitsPortal_of_step glob n b s hvalid (.d1 i) .r (by nofun) hp1
      rw [hs1]; exact h

lemma dClosed0_eq_false_of_tau_false (n b s : ℕ) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = false) :
    dClosed0 n b s i = false := by
  dsimp [chooseTauEdge1] at htau
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at htau
  rcases htau with ⟨⟨hbit, hlt_T⟩, _⟩
  unfold dClosed0
  simp [hbit, hlt_T]

lemma hitsPortal_g_of_tau_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = false) :
    HitsPortal glob n b s (.g i) .c ∨ HitsPortal glob n b s (.g i) .r := by
  have hpg : (G_bin n).priority (.g i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .d1 i := by
    dsimp [step, G_bin, owner_bin, predTau0]; rw [htau]; rfl
  rcases hitsPortal_d1_of_not_dClosed0 glob n b s hvalid i (dClosed0_eq_false_of_tau_false n b s i htau) with h | h
  · left; apply hitsPortal_of_step glob n b s hvalid (.g i) .c (by nofun) hpg; rw [hstep]; exact h
  · right; apply hitsPortal_of_step glob n b s hvalid (.g i) .r (by nofun) hpg; rw [hstep]; exact h

/-! ### Part 2: High-Priority Membership on the Spine and `portalOrderProp_holds` -/

lemma lt_n_of_hasHigherOne0 {b n i : ℕ} (h : hasHigherOne0 b n i = true) : i + 1 < n := by
  rcases (hasHigherOne0_iff b n i).mp h with ⟨j, hij, hjn, _⟩
  omega

lemma hasHigherOne0_succ_iff {b n i : ℕ} (hi1 : i + 1 < n) :
    hasHigherOne0 b n i = true ↔ b.testBit (i + 1) = true ∨ hasHigherOne0 b n (i + 1) = true := by
  rw [hasHigherOne0_iff, hasHigherOne0_iff]
  constructor
  · rintro ⟨j, hij, hjn, hbit⟩
    by_cases hj : j = i + 1
    · subst hj; exact Or.inl hbit
    · exact Or.inr ⟨j, by omega, hjn, hbit⟩
  · rintro (hbit | ⟨j, hij, hjn, hbit⟩)
    · exact ⟨i + 1, by omega, hi1, hbit⟩
    · exact ⟨j, by omega, hjn, hbit⟩

def highMemZ (n b : ℕ) (i : Fin n) : V_bin n → Prop
  | .z j => j = i ∨ (i.val < j.val ∧ b.testBit j.val = true)
  | .f j => i.val < j.val ∧ b.testBit j.val = true
  | .k j => i.val < j.val ∧ b.testBit j.val = true
  | _ => False

def highMemU (n b : ℕ) (m : Fin n) : V_bin n → Prop
  | .z j | .f j | .k j => m.val ≤ j.val ∧ b.testBit j.val = true
  | _ => False

def highMemF (n b : ℕ) (i : Fin n) : V_bin n → Prop
  | .z j | .f j | .k j => j = i ∨ (i.val < j.val ∧ b.testBit j.val = true)
  | _ => False

lemma uStillH0_succ_false_of_uStillH0_false (n b s : ℕ) (m : Fin n) (hm1 : m.val + 1 < n)
    (h : uStillH0 n b s m = false) :
    uStillH0 n b s ⟨m.val + 1, hm1⟩ = false := by
  unfold uStillH0 at h ⊢
  rw [decide_eq_false_iff_not] at h ⊢
  dsimp only
  intro hcond
  exact h ⟨hcond.1, by omega, by omega⟩

lemma uStillH0_succ_false_of_testBit_true (n b s : ℕ) (m : Fin n) (hm1 : m.val + 1 < n)
    (hbit : b.testBit m.val = true) :
    uStillH0 n b s ⟨m.val + 1, hm1⟩ = false := by
  unfold uStillH0
  rw [decide_eq_false_iff_not]
  dsimp only
  have hle := lowestOne0_le_of_testBit_true m.isLt hbit
  rintro ⟨_, hlt, _⟩
  omega

lemma uStillH0_succ_false_of_isBot0 (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hbot : isBot0 n b s i = true) (hi1 : i.val + 1 < n) :
    uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
  rcases hvalid with ⟨_, hbn, _⟩
  unfold uStillH0 uLim0
  rw [decide_eq_false_iff_not]
  dsimp only
  rintro ⟨hb0, hlt_prev, hlt_lim⟩
  unfold isBot0 at hbot
  rw [Bool.or_eq_true, decide_eq_true_eq] at hbot
  rcases hbot with hbit | ⟨_, _, hs_ge⟩
  · have hle := lowestOne0_le_of_testBit_true i.isLt hbit
    omega
  · have hprev_lt := lowestOne0_lt hb0 hbn
    unfold S_close0 at hs_ge
    split_ifs at hlt_lim <;> omega

lemma mem_path_step_high (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w u : V_bin n) (hw : w ≠ .x)
    (hprio : (G_bin n).priority w < (G_bin n).priority .c)
    (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s w ↔
      u ∈ predPath glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) := by
  rw [predPath, predVal, pred_path_step glob n b s hvalid w hw, Finset.mem_insert]
  have hne : u ≠ w := by intro heq; subst heq; omega
  simp [hne]

lemma highMem_z_and_u_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    ∀ k : ℕ,
      (∀ i : Fin n, n - i.val ≤ k →
        (∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false) →
        ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
          (u ∈ predPath glob n b s (.z i) ↔ highMemZ n b i u)) ∧
      (∀ m : Fin n, n - m.val ≤ k → 1 ≤ m.val →
        (b.testBit m.val = true ∨ hasHigherOne0 b n m.val = true) →
        uStillH0 n b s m = false →
        ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
          (u ∈ predPath glob n b s (.u m) ↔ highMemU n b m u))
  | 0 => ⟨fun i hk => by have := i.isLt; omega, fun m hk => by have := m.isLt; omega⟩
  | k + 1 => by
    rcases highMem_z_and_u_aux glob n b s hvalid k with ⟨ihZ, ihU⟩
    have hz : ∀ i : Fin n, n - i.val ≤ k + 1 →
        (∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false) →
        ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
          (u ∈ predPath glob n b s (.z i) ↔ highMemZ n b i u) := by
      intro i hk hstill u hu
      have hi := i.isLt
      rw [predPath, predVal, pred_path_step glob n b s hvalid (.z i) (by nofun), Finset.mem_insert]
      change u = .z i ∨ u ∈ predPath glob n b s (predState0 glob n b s (.z i)) ↔ highMemZ n b i u
      cases hhi : hasHigherOne0 b n i.val with
      | false =>
        have hce : chooseEdge1 glob n b s (.z i) = false := by
          dsimp [chooseEdge1]; rw [hhi, Bool.and_false]
        have hstep : predState0 glob n b s (.z i) = .x := by
          unfold predState0; rw [hce]; rfl
        rw [hstep, predPath, predVal, pred_path_x glob n b s hvalid]
        simp only [Finset.notMem_empty, or_false]
        have hall : ∀ j : Fin n, i.val < j.val → b.testBit j.val = false :=
          fun j hj => (hasHigherOne0_eq_false_iff b n i.val).mp hhi j.val hj j.isLt
        cases u with
        | z j =>
          dsimp [highMemZ]
          constructor
          · rintro ⟨rfl⟩; exact Or.inl rfl
          · rintro (rfl | ⟨hj, hbit⟩)
            · rfl
            · rw [hall j hj] at hbit; contradiction
        | f j | k j =>
          dsimp [highMemZ]
          simp only [reduceCtorEq, false_iff, not_and]
          intro hj; rw [hall j hj]; decide
        | _ =>
          dsimp [highMemZ]; simp
      | true =>
        have hi1 : i.val + 1 < n := lt_n_of_hasHigherOne0 hhi
        have hce : chooseEdge1 glob n b s (.z i) = true := by
          dsimp [chooseEdge1]; simp [hi1, hhi]
        have hstep : predState0 glob n b s (.z i) = .u ⟨i.val + 1, hi1⟩ := by
          unfold predState0; rw [if_pos hce]; dsimp [edge1]; rw [dif_pos hi1]
        rw [hstep]
        have hnext := (hasHigherOne0_succ_iff hi1).mp hhi
        have hmemU := ihU ⟨i.val + 1, hi1⟩ (by dsimp only; omega) (by dsimp only; omega) hnext (hstill hi1) u hu
        rw [hmemU]
        cases u with
        | z j =>
          dsimp [highMemU, highMemZ]
          constructor
          · rintro (h | ⟨hj, hbit⟩)
            · injection h with h'; subst h'; exact Or.inl rfl
            · exact Or.inr ⟨by omega, hbit⟩
          · rintro (rfl | ⟨hj, hbit⟩)
            · exact Or.inl rfl
            · exact Or.inr ⟨by omega, hbit⟩
        | f j | k j =>
          dsimp [highMemU, highMemZ]
          simp only [reduceCtorEq, false_or]
          exact ⟨fun ⟨hj, hbit⟩ => ⟨by omega, hbit⟩, fun ⟨hj, hbit⟩ => ⟨by omega, hbit⟩⟩
        | _ =>
          dsimp [highMemU, highMemZ]; simp
    refine ⟨hz, ?_⟩
    intro m hk hm1 hcond hstill u hu
    have hm := m.isLt
    have hp_u : (G_bin n).priority (.u m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    rw [mem_path_step_high glob n b s hvalid (.u m) u (by nofun) hp_u hu]
    have howner : (G_bin n).owner (.u m) = false := by
      dsimp [G_bin, owner_bin]; rw [if_neg (by omega)]
    have hstep_eq : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u m) =
        predState0 glob n b s (.u m) := by
      unfold step; rw [if_pos howner]
    rw [hstep_eq]
    cases hbit : b.testBit m.val with
    | true =>
      have hce_u : chooseEdge1 glob n b s (.u m) = false := by
        dsimp [chooseEdge1]; split_ifs <;> simp_all
      have hpred_u : predState0 glob n b s (.u m) = .h m := by
        unfold predState0; rw [hce_u]; rfl
      rw [hpred_u]
      have hp_h : (G_bin n).priority (.h m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hp_hx : (G_bin n).priority (.hx m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hp_hy : (G_bin n).priority (.hy m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hp_g : (G_bin n).priority (.g m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h m) = .hx m := by
        unfold step G_bin owner_bin predState0; simp [chooseEdge1, hbit, edge0]
      have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
        unfold step G_bin owner_bin predState0; simp [chooseEdge1, hbit, edge0]
      have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
        unfold step G_bin owner_bin predState0; simp [chooseEdge1, hbit, edge0]
      have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f m) = .g m := rfl
      have hs_g : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g m) = .k m := by
        unfold step G_bin owner_bin predTau0; simp [chooseTauEdge1, hbit, edge1]
      have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k m) = .z m := rfl
      rw [mem_path_step_high glob n b s hvalid (.h m) u (by nofun) hp_h hu, hs_h,
          mem_path_step_high glob n b s hvalid (.hx m) u (by nofun) hp_hx hu, hs_hx,
          mem_path_step_high glob n b s hvalid (.hy m) u (by nofun) hp_hy hu, hs_hy]
      rw [predPath, predVal, pred_path_step glob n b s hvalid (.f m) (by nofun), hs_f, Finset.mem_insert]
      change u = .f m ∨ u ∈ predPath glob n b s (.g m) ↔ _
      rw [mem_path_step_high glob n b s hvalid (.g m) u (by nofun) hp_g hu, hs_g]
      rw [predPath, predVal, pred_path_step glob n b s hvalid (.k m) (by nofun), hs_k, Finset.mem_insert]
      change u = .f m ∨ u = .k m ∨ u ∈ predPath glob n b s (.z m) ↔ _
      have hstill_succ : ∀ hm1 : m.val + 1 < n, uStillH0 n b s ⟨m.val + 1, hm1⟩ = false :=
        fun hm1 => uStillH0_succ_false_of_testBit_true n b s m hm1 hbit
      rw [hz m hk hstill_succ u hu]
      cases u with
      | z j =>
        dsimp [highMemZ, highMemU]
        simp only [reduceCtorEq, false_or]
        constructor
        · rintro (rfl | ⟨hj, hbj⟩)
          · exact ⟨le_rfl, hbit⟩
          · exact ⟨by omega, hbj⟩
        · rintro ⟨hj, hbj⟩
          by_cases heq : j = m
          · exact Or.inl heq
          · exact Or.inr ⟨by omega, hbj⟩
      | f j =>
        dsimp [highMemZ, highMemU]
        simp only [reduceCtorEq, false_or]
        constructor
        · rintro (h | ⟨hj, hbj⟩)
          · injection h with h'; subst h'; exact ⟨le_rfl, hbit⟩
          · exact ⟨by omega, hbj⟩
        · rintro ⟨hj, hbj⟩
          by_cases heq : j = m
          · subst heq; exact Or.inl rfl
          · exact Or.inr ⟨by omega, hbj⟩
      | k j =>
        dsimp [highMemZ, highMemU]
        simp only [reduceCtorEq, false_or]
        constructor
        · rintro (h | ⟨hj, hbj⟩)
          · injection h with h'; subst h'; exact ⟨le_rfl, hbit⟩
          · exact ⟨by omega, hbj⟩
        · rintro ⟨hj, hbj⟩
          by_cases heq : j = m
          · subst heq; exact Or.inl rfl
          · exact Or.inr ⟨by omega, hbj⟩
      | _ =>
        dsimp [highMemZ, highMemU]; simp
    | false =>
      have hhi : hasHigherOne0 b n m.val = true := by
        rcases hcond with h1 | h2
        · rw [hbit] at h1; contradiction
        · exact h2
      have hm_succ : m.val + 1 < n := lt_n_of_hasHigherOne0 hhi
      have hce_u : chooseEdge1 glob n b s (.u m) = true := by
        dsimp [chooseEdge1]
        rw [if_neg (by omega), if_neg (by simp [hbit, hhi])]
        split_ifs with h3
        · rw [decide_eq_true_eq]
          unfold uStillH0 at hstill
          rw [decide_eq_false_iff_not] at hstill
          intro hlt
          exact hstill ⟨h3.1, h3.2, hlt⟩
        · rfl
      have hpred_u : predState0 glob n b s (.u m) = .u ⟨m.val + 1, hm_succ⟩ := by
        unfold predState0; rw [if_pos hce_u]; dsimp [edge1]; rw [dif_pos ⟨by omega, hm_succ⟩]
      rw [hpred_u]
      have hnext := (hasHigherOne0_succ_iff hm_succ).mp hhi
      have hstill_succ := uStillH0_succ_false_of_uStillH0_false n b s m hm_succ hstill
      rw [ihU ⟨m.val + 1, hm_succ⟩ (by dsimp only; omega) (by dsimp only; omega) hnext hstill_succ u hu]
      cases u with
      | z j | f j | k j =>
        dsimp [highMemU]
        constructor
        · rintro ⟨hj, hbj⟩; exact ⟨by omega, hbj⟩
        · rintro ⟨hj, hbj⟩
          have hne : j.val ≠ m.val := by intro heq; rw [heq, hbit] at hbj; contradiction
          exact ⟨by omega, hbj⟩
      | _ =>
        dsimp [highMemU]; rfl

lemma highMem_z (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.z i) ↔ highMemZ n b i u :=
  (highMem_z_and_u_aux glob n b s hvalid n).1 i (by omega) hstill u hu

lemma highMem_u (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (m : Fin n)
    (hm1 : 1 ≤ m.val) (hcond : b.testBit m.val = true ∨ hasHigherOne0 b n m.val = true)
    (hstill : uStillH0 n b s m = false)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.u m) ↔ highMemU n b m u :=
  (highMem_z_and_u_aux glob n b s hvalid n).2 m (by omega) hm1 hcond hstill u hu

lemma tau_true_of_isBot0 (n b s : ℕ) (i : Fin n) (hbot : isBot0 n b s i = true) :
    chooseTauEdge1 n b s (.g i) = true := by
  unfold isBot0 S_close0 at hbot
  dsimp [chooseTauEdge1]
  rcases Bool.or_eq_true_iff.mp hbot with hbit | h2
  · simp [hbit]
  · rw [decide_eq_true_eq] at h2
    rcases h2 with ⟨_, hik, hs⟩
    rw [← hik] at hs
    have hd : decide (3 * (n + 2 * i.val + 1) + 2 ≤ s) = true := decide_eq_true hs
    simp [hd]

lemma highMem_f_of_tau_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = true)
    (hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.f i) ↔ highMemF n b i u := by
  have hp_g : (G_bin n).priority (.g i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f i) = .g i := rfl
  have hs_g : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .k i := by
    unfold step G_bin owner_bin predTau0; rw [if_pos htau]; rfl
  have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid (.f i) (by nofun), hs_f, Finset.mem_insert]
  change u = .f i ∨ u ∈ predPath glob n b s (.g i) ↔ _
  rw [mem_path_step_high glob n b s hvalid (.g i) u (by nofun) hp_g hu, hs_g]
  rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k, Finset.mem_insert]
  change u = .f i ∨ u = .k i ∨ u ∈ predPath glob n b s (.z i) ↔ _
  rw [highMem_z glob n b s hvalid i hstill u hu]
  cases u with
  | z j =>
    dsimp [highMemZ, highMemF]
    simp
  | f j =>
    dsimp [highMemZ, highMemF]
    simp only [reduceCtorEq, false_or]
    exact ⟨fun h => h.elim (fun h' => by injection h' with h''; exact Or.inl h'') Or.inr,
           fun h => h.elim (fun h' => Or.inl (by subst h'; rfl)) Or.inr⟩
  | k j =>
    dsimp [highMemZ, highMemF]
    simp only [reduceCtorEq, false_or]
    exact ⟨fun h => h.elim (fun h' => by injection h' with h''; exact Or.inl h'') Or.inr,
           fun h => h.elim (fun h' => Or.inl (by subst h'; rfl)) Or.inr⟩
  | _ =>
    dsimp [highMemZ, highMemF]; simp

lemma highMem_f_of_isBot0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hbot : isBot0 n b s i = true)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.f i) ↔ highMemF n b i u :=
  highMem_f_of_tau_true glob n b s hvalid i
    (tau_true_of_isBot0 n b s i hbot)
    (uStillH0_succ_false_of_isBot0 n b s hvalid i hbot)
    u hu

lemma rTarg0_lt_of_rActive0' (n b s : ℕ) (hbn : b < 2 ^ n) (hact : rActive0 n b s = true) :
    rTarg0 n b s < n := by
  unfold rActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold rTarg0
  split_ifs with h2
  · exact lowestZero0_lt h2.1
  · rcases hact with hb0 | h2'
    · exact lowestOne0_lt hb0 hbn
    · exact False.elim (h2 h2')

lemma sTarg0_lt_of_sActive0' (n b s : ℕ) (hbn : b < 2 ^ n) (hact : sActive0 n b s = true) :
    sTarg0 n b s < n := by
  unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold sTarg0
  split_ifs with h2
  · exact lowestZero0_lt h2.1
  · rcases hact with hb0 | h2'
    · exact lowestOne0_lt hb0 hbn
    · exact False.elim (h2 h2')

lemma isBot0_rTarg0 (n b s : ℕ) (hbn : b < 2 ^ n) (hact : rActive0 n b s = true) :
    isBot0 n b s ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hbn hact⟩ = true := by
  unfold rActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold isBot0 rTarg0
  rw [Bool.or_eq_true, decide_eq_true_eq]
  dsimp only
  split_ifs with h2
  · exact Or.inr ⟨h2.1, rfl, by omega⟩
  · rcases hact with hb0 | h2'
    · exact Or.inl (testBit_lowestOne0 hb0 hbn)
    · exact False.elim (h2 h2')

lemma isBot0_sTarg0 (n b s : ℕ) (hbn : b < 2 ^ n) (hact : sActive0 n b s = true) :
    isBot0 n b s ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hbn hact⟩ = true := by
  unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold isBot0 sTarg0
  rw [Bool.or_eq_true, decide_eq_true_eq]
  dsimp only
  split_ifs with h2
  · exact Or.inr ⟨h2.1, rfl, by omega⟩
  · rcases hact with hb0 | h2'
    · exact Or.inl (testBit_lowestOne0 hb0 hbn)
    · exact False.elim (h2 h2')

lemma step_rp_of_eq_rTarg0 (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hact : rActive0 n b s = true) (heq : m.val = rTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.rp m) = .f m := by
  change predState0 glob n b s (.rp m) = .f m
  by_cases hm0 : m.val = 0
  · unfold predState0
    have hce : chooseEdge1 glob n b s (.rp m) = true := by dsimp [chooseEdge1]; rw [if_pos hm0]
    rw [if_pos hce]
    simp [edge1, hm0]
  · have hce : chooseEdge1 glob n b s (.rp m) = false := by
      dsimp [chooseEdge1]
      rw [if_neg hm0]
      unfold rActive0 at hact; rw [decide_eq_true_eq] at hact
      unfold rTarg0 at heq
      split_ifs with h2
      · rw [if_pos h2] at heq; simp [heq]
      · rw [if_neg h2] at heq
        have hb0 : 0 < b := hact.resolve_right h2
        simp [hb0, heq]
    unfold predState0; rw [hce]; rfl

lemma step_rp_of_ne_rTarg0 (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hm0 : m.val ≠ 0) (hne : m.val ≠ rTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.rp m) =
      .rp ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  change predState0 glob n b s (.rp m) = _
  have hce : chooseEdge1 glob n b s (.rp m) = true := by
    dsimp [chooseEdge1]
    rw [if_neg hm0]
    unfold rTarg0 at hne
    split_ifs with h2
    · rw [if_pos h2] at hne; exact decide_eq_true hne
    · rw [if_neg h2] at hne; rw [decide_eq_true_eq]; rintro ⟨_, h⟩; exact hne h
  unfold predState0; rw [if_pos hce]; simp [edge1, hm0]

lemma highMem_rp_of_ge (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : rActive0 n b s = true) :
    ∀ k (m : Fin n), m.val - rTarg0 n b s ≤ k → rTarg0 n b s ≤ m.val →
      ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
        (u ∈ predPath glob n b s (.rp m) ↔
          highMemF n b ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hact⟩ u)
  | 0, m, hk, hge, u, hu => by
    have heq : m.val = rTarg0 n b s := by omega
    have hp_rp : (G_bin n).priority (.rp m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    rw [mem_path_step_high glob n b s hvalid (.rp m) u (by nofun) hp_rp hu,
        step_rp_of_eq_rTarg0 glob n b s m hact heq]
    have hm_eq : m = ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hact⟩ := Fin.ext heq
    rw [hm_eq]
    exact highMem_f_of_isBot0 glob n b s hvalid _ (isBot0_rTarg0 n b s hvalid.2.1 hact) u hu
  | k + 1, m, hk, hge, u, hu => by
    by_cases heq : m.val = rTarg0 n b s
    · exact highMem_rp_of_ge glob n b s hvalid hact 0 m (by omega) hge u hu
    · have hm0 : m.val ≠ 0 := by omega
      have hp_rp : (G_bin n).priority (.rp m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      rw [mem_path_step_high glob n b s hvalid (.rp m) u (by nofun) hp_rp hu,
          step_rp_of_ne_rTarg0 glob n b s m hm0 heq]
      exact highMem_rp_of_ge glob n b s hvalid hact k ⟨m.val - 1, by have := m.isLt; omega⟩
        (by dsimp only; omega) (by dsimp only; omega) u hu

lemma highMem_r_of_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : rActive0 n b s = false) (u : V_bin n) :
    u ∈ predPath glob n b s .r ↔ u = .r := by
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r = .x := by
    unfold step G_bin owner_bin predState0 chooseEdge1; rw [if_pos rfl, hact]; rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid .r (by nofun), hstep,
      pred_path_x glob n b s hvalid]
  simp

lemma highMem_r_of_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : rActive0 n b s = true) (u : V_bin n)
    (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s .r ↔
      u = .r ∨ highMemF n b ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hact⟩ u := by
  have hn := hvalid.1
  have ht := rTarg0_lt_of_rActive0' n b s hvalid.2.1 hact
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r = .rp ⟨n - 1, by omega⟩ := by
    unfold step G_bin owner_bin predState0 chooseEdge1
    rw [if_pos rfl, if_pos hact]
    dsimp [edge1]; rw [dif_pos hn]
  rw [predPath, predVal, pred_path_step glob n b s hvalid .r (by nofun), hstep, Finset.mem_insert]
  change u = .r ∨ u ∈ predPath glob n b s (.rp ⟨n - 1, by omega⟩) ↔ _
  rw [highMem_rp_of_ge glob n b s hvalid hact n ⟨n - 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega) u hu]

lemma step_sp_of_eq_sTarg0 (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hact : sActive0 n b s = true) (heq : m.val = sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.sp m) = .hx m := by
  change predState0 glob n b s (.sp m) = .hx m
  by_cases hm0 : m.val = 0
  · unfold predState0
    have hce : chooseEdge1 glob n b s (.sp m) = true := by dsimp [chooseEdge1]; rw [if_pos hm0]
    rw [if_pos hce]
    simp [edge1, hm0]
  · have hce : chooseEdge1 glob n b s (.sp m) = false := by
      dsimp [chooseEdge1]
      rw [if_neg hm0]
      unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
      unfold sTarg0 at heq
      split_ifs with h2
      · rw [if_pos h2] at heq; simp [heq]
      · rw [if_neg h2] at heq
        have hb0 : 0 < b := hact.resolve_right h2
        simp [hb0, heq]
    unfold predState0; rw [hce]; rfl

lemma step_sp_of_ne_sTarg0 (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hm0 : m.val ≠ 0) (hne : m.val ≠ sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.sp m) =
      .sp ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  change predState0 glob n b s (.sp m) = _
  have hce : chooseEdge1 glob n b s (.sp m) = true := by
    dsimp [chooseEdge1]
    rw [if_neg hm0]
    unfold sTarg0 at hne
    split_ifs with h2
    · rw [if_pos h2] at hne; exact decide_eq_true hne
    · rw [if_neg h2] at hne; rw [decide_eq_true_eq]; rintro ⟨_, h⟩; exact hne h
  unfold predState0; rw [if_pos hce]; simp [edge1, hm0]

lemma step_hx_of_eq_sTarg0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (m : Fin n)
    (hact : sActive0 n b s = true) (heq : m.val = sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
  change predState0 glob n b s (.hx m) = .hy m
  unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold sTarg0 at heq
  have hce : chooseEdge1 glob n b s (.hx m) = false := by
    dsimp [chooseEdge1]
    split_ifs with hbit hlim hzero
    · rfl
    · exfalso
      rcases hlim with ⟨hb0, hlt_kp, hlt_hy⟩
      split_ifs at heq with h2
      · have hkp := lowestOne0_lt hb0 hvalid.2.1
        have hs_ge := h2.2
        unfold S_close0 at hs_ge
        unfold hyLim0 at hlt_hy
        split_ifs at hlt_hy <;> omega
      · omega
    · split_ifs at heq with h2
      · rw [decide_eq_false_iff_not]; omega
      · exfalso
        have hb0 : 0 < b := hact.resolve_right h2
        rw [heq, testBit_lowestOne0 hb0 hvalid.2.1] at hbit
        contradiction
    · exfalso
      split_ifs at heq with h2
      · exact hzero ⟨h2.1, heq⟩
      · have hb0 : 0 < b := hact.resolve_right h2
        rw [heq, testBit_lowestOne0 hb0 hvalid.2.1] at hbit
        contradiction
  unfold predState0; rw [hce]; rfl

lemma step_hy_of_eq_sTarg0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (m : Fin n)
    (hact : sActive0 n b s = true) (heq : m.val = sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
  change predState0 glob n b s (.hy m) = .f m
  unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold sTarg0 at heq
  have hce : chooseEdge1 glob n b s (.hy m) = false := by
    dsimp [chooseEdge1]
    split_ifs with hbit hlim hzero
    · rfl
    · exfalso
      rcases hlim with ⟨hb0, hlt_kp, hlt_hy⟩
      split_ifs at heq with h2
      · have hkp := lowestOne0_lt hb0 hvalid.2.1
        have hs_ge := h2.2
        unfold S_close0 at hs_ge
        unfold hyLim0 at hlt_hy
        split_ifs at hlt_hy <;> omega
      · omega
    · split_ifs at heq with h2
      · rw [decide_eq_false_iff_not]; omega
      · exfalso
        have hb0 : 0 < b := hact.resolve_right h2
        rw [heq, testBit_lowestOne0 hb0 hvalid.2.1] at hbit
        contradiction
    · exfalso
      split_ifs at heq with h2
      · exact hzero ⟨h2.1, heq⟩
      · have hb0 : 0 < b := hact.resolve_right h2
        rw [heq, testBit_lowestOne0 hb0 hvalid.2.1] at hbit
        contradiction
  unfold predState0; rw [hce]; rfl

lemma highMem_sp_of_ge (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = true) :
    ∀ k (m : Fin n), m.val - sTarg0 n b s ≤ k → sTarg0 n b s ≤ m.val →
      ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
        (u ∈ predPath glob n b s (.sp m) ↔
          highMemF n b ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact⟩ u)
  | 0, m, hk, hge, u, hu => by
    have heq : m.val = sTarg0 n b s := by omega
    have hp_sp : (G_bin n).priority (.sp m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    have hp_hx : (G_bin n).priority (.hx m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    have hp_hy : (G_bin n).priority (.hy m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    rw [mem_path_step_high glob n b s hvalid (.sp m) u (by nofun) hp_sp hu,
        step_sp_of_eq_sTarg0 glob n b s m hact heq,
        mem_path_step_high glob n b s hvalid (.hx m) u (by nofun) hp_hx hu,
        step_hx_of_eq_sTarg0 glob n b s hvalid m hact heq,
        mem_path_step_high glob n b s hvalid (.hy m) u (by nofun) hp_hy hu,
        step_hy_of_eq_sTarg0 glob n b s hvalid m hact heq]
    have hm_eq : m = ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact⟩ := Fin.ext heq
    rw [hm_eq]
    exact highMem_f_of_isBot0 glob n b s hvalid _ (isBot0_sTarg0 n b s hvalid.2.1 hact) u hu
  | k + 1, m, hk, hge, u, hu => by
    by_cases heq : m.val = sTarg0 n b s
    · exact highMem_sp_of_ge glob n b s hvalid hact 0 m (by omega) hge u hu
    · have hm0 : m.val ≠ 0 := by omega
      have hp_sp : (G_bin n).priority (.sp m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      rw [mem_path_step_high glob n b s hvalid (.sp m) u (by nofun) hp_sp hu,
          step_sp_of_ne_sTarg0 glob n b s m hm0 heq]
      exact highMem_sp_of_ge glob n b s hvalid hact k ⟨m.val - 1, by have := m.isLt; omega⟩
        (by dsimp only; omega) (by dsimp only; omega) u hu

lemma highMem_s_of_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = false) (u : V_bin n) :
    u ∈ predPath glob n b s .s ↔ u = .s := by
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .s = .x := by
    unfold step G_bin owner_bin predState0 chooseEdge1; rw [if_pos rfl, hact]; rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid .s (by nofun), hstep,
      pred_path_x glob n b s hvalid]
  simp

lemma highMem_s_of_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = true) (u : V_bin n)
    (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s .s ↔
      u = .s ∨ highMemF n b ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact⟩ u := by
  have hn := hvalid.1
  have ht := sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .s = .sp ⟨n - 1, by omega⟩ := by
    unfold step G_bin owner_bin predState0 chooseEdge1
    rw [if_pos rfl, if_pos hact]
    dsimp [edge1]; rw [dif_pos hn]
  rw [predPath, predVal, pred_path_step glob n b s hvalid .s (by nofun), hstep, Finset.mem_insert]
  change u = .s ∨ u ∈ predPath glob n b s (.sp ⟨n - 1, by omega⟩) ↔ _
  rw [highMem_sp_of_ge glob n b s hvalid hact n ⟨n - 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega) u hu]

lemma highMem_c_of_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = false) (u : V_bin n) :
    u ∈ predPath glob n b s .c ↔ u = .c ∨ u = .s := by
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .c = .s := rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid .c (by nofun), hstep, Finset.mem_insert]
  change u = .c ∨ u ∈ predPath glob n b s .s ↔ _
  rw [highMem_s_of_false glob n b s hvalid hact u]

lemma highMem_c_of_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = true) (u : V_bin n)
    (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s .c ↔
      u = .c ∨ u = .s ∨ highMemF n b ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact⟩ u := by
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .c = .s := rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid .c (by nofun), hstep, Finset.mem_insert]
  change u = .c ∨ u ∈ predPath glob n b s .s ↔ _
  rw [highMem_s_of_true glob n b s hvalid hact u hu]

lemma highMemF_lowestOne0_iff (n b : ℕ) (hb0 : 0 < b) (hbn : b < 2 ^ n) (j : Fin n) :
    (j = ⟨lowestOne0 b n, lowestOne0_lt hb0 hbn⟩ ∨
      (lowestOne0 b n < j.val ∧ b.testBit j.val = true)) ↔
      b.testBit j.val = true := by
  constructor
  · rintro (rfl | ⟨_, hbit⟩)
    · exact testBit_lowestOne0 hb0 hbn
    · exact hbit
  · intro hbit
    have hle := lowestOne0_le_of_testBit_true j.isLt hbit
    by_cases heq : j.val = lowestOne0 b n
    · left; exact Fin.ext heq
    · right; exact ⟨by omega, hbit⟩

theorem portalOrderProp_holds (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    PortalOrderProp glob n b s := by
  rcases hvalid with ⟨hn, hbn, hs_max⟩
  have hvalid' : ValidState n b s := ⟨hn, hbn, hs_max⟩
  unfold PortalOrderProp
  split_ifs with hbranch
  · intro w₁ w₂ hc hr
    rcases hbranch with ⟨hb_lt, hs12⟩
    have hk : lowestZero0 b n < n := lowestZero0_lt hb_lt
    let kFin : Fin n := ⟨lowestZero0 b n, hk⟩
    have hract : rActive0 n b s = true := by
      unfold rActive0; rw [decide_eq_true_eq]; right; exact ⟨hb_lt, by omega⟩
    have hrtarg : rTarg0 n b s = lowestZero0 b n := by
      unfold rTarg0; rw [if_pos ⟨hb_lt, by omega⟩]
    have hp_k : (G_bin n).priority .c ≤ (G_bin n).priority (.k kFin) := by
      dsimp [G_bin, priority_bin]; omega
    apply predVal_lt_of_setLT glob n b s hvalid'
    apply setLT_of_top_diff_even (G_bin_priority_injective n hn) (d := .k kFin)
    · rw [hc.2 (.k kFin) hp_k]
      cases hsact : sActive0 n b s with
      | false =>
        rw [highMem_c_of_false glob n b s hvalid' hsact]
        simp
      | true =>
        rw [highMem_c_of_true glob n b s hvalid' hsact (.k kFin) hp_k]
        have hb0 : 0 < b := by
          unfold sActive0 at hsact; rw [decide_eq_true_eq] at hsact
          rcases hsact with h | h; exact h; omega
        have hstarg : sTarg0 n b s = lowestOne0 b n := by
          unfold sTarg0; rw [if_neg (by omega)]
        simp only [reduceCtorEq, false_or, highMemF]
        rw [Fin.ext_iff]
        dsimp only [kFin]
        rw [hstarg]
        have hbit_k : b.testBit (lowestZero0 b n) = false := testBit_lowestZero0 hb_lt
        have hbit_kp : b.testBit (lowestOne0 b n) = true := testBit_lowestOne0 hb0 hbn
        rintro (heq | ⟨_, htrue⟩)
        · rw [heq, hbit_kp] at hbit_k; contradiction
        · rw [hbit_k] at htrue; contradiction
    · rw [hr.2 (.k kFin) hp_k, highMem_r_of_true glob n b s hvalid' hract (.k kFin) hp_k]
      right
      dsimp [highMemF, kFin]
      left
      exact Fin.ext hrtarg.symm
    · exact prio_k_even n kFin
    · intro u hu
      have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by omega
      rw [hc.2 u hp_u, hr.2 u hp_u, highMem_r_of_true glob n b s hvalid' hract u hp_u]
      have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
        dsimp [G_bin, priority_bin] at hu ⊢; omega
      rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨j, rfl | rfl | rfl⟩
      all_goals
        have hkj : lowestZero0 b n < j.val := by
          dsimp [G_bin, priority_bin, kFin] at hu; omega
        cases hsact : sActive0 n b s with
        | false =>
          have hb0 : b = 0 := by
            unfold sActive0 at hsact; rw [decide_eq_false_iff_not] at hsact; omega
          subst hb0
          rw [highMem_c_of_false glob n 0 s hvalid' hsact]
          simp only [reduceCtorEq, false_or, highMemF, Fin.ext_iff, hrtarg, Nat.zero_testBit, and_false, or_false]
          exact ⟨False.elim, fun h => by omega⟩
        | true =>
          have hb0 : 0 < b := by
            unfold sActive0 at hsact; rw [decide_eq_true_eq] at hsact
            rcases hsact with h | h; exact h; omega
          have hstarg : ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hbn hsact⟩ =
              (⟨lowestOne0 b n, lowestOne0_lt hb0 hbn⟩ : Fin n) := by
            apply Fin.ext
            dsimp only
            unfold sTarg0
            rw [if_neg (by omega)]
          rw [highMem_c_of_true glob n b s hvalid' hsact _ hp_u, hstarg]
          simp only [reduceCtorEq, false_or, highMemF]
          rw [highMemF_lowestOne0_iff n b hb0 hbn j]
          simp only [Fin.ext_iff, hrtarg]
          exact ⟨fun h => Or.inr ⟨hkj, h⟩, fun h => h.elim (by omega) And.right⟩
  · intro w₁ w₂ hr hc
    have hact_eq : rActive0 n b s = sActive0 n b s := by
      unfold rActive0 sActive0
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      omega
    have htarg_eq : rTarg0 n b s = sTarg0 n b s := by
      unfold rTarg0 sTarg0
      split_ifs <;> omega
    have hp_s : (G_bin n).priority .c ≤ (G_bin n).priority .s := by
      dsimp [G_bin, priority_bin]; omega
    apply predVal_lt_of_setLT glob n b s hvalid'
    apply setLT_of_top_diff_even (G_bin_priority_injective n hn) (d := .s)
    · rw [hr.2 .s hp_s]
      cases hract : rActive0 n b s with
      | false => rw [highMem_r_of_false glob n b s hvalid' hract]; nofun
      | true => rw [highMem_r_of_true glob n b s hvalid' hract .s hp_s]; simp [highMemF]
    · rw [hc.2 .s hp_s]
      cases hsact : sActive0 n b s with
      | false => rw [highMem_c_of_false glob n b s hvalid' hsact]; exact Or.inr rfl
      | true => rw [highMem_c_of_true glob n b s hvalid' hsact .s hp_s]; exact Or.inr (Or.inl rfl)
    · exact prio_s_even n
    · intro u hu
      have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by omega
      have hne_c : u ≠ .c := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
      have hne_r : u ≠ .r := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
      have hne_s : u ≠ .s := by intro h; subst h; omega
      rw [hr.2 u hp_u, hc.2 u hp_u]
      cases hract : rActive0 n b s with
      | false =>
        have hsact : sActive0 n b s = false := hact_eq.symm.trans hract
        rw [highMem_r_of_false glob n b s hvalid' hract,
            highMem_c_of_false glob n b s hvalid' hsact]
        simp [hne_r, hne_c, hne_s]
      | true =>
        have hsact : sActive0 n b s = true := hact_eq.symm.trans hract
        rw [highMem_r_of_true glob n b s hvalid' hract u hp_u,
            highMem_c_of_true glob n b s hvalid' hsact u hp_u]
        have hfin_eq : (⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hbn hract⟩ : Fin n) =
            ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hbn hsact⟩ := Fin.ext htarg_eq
        rw [hfin_eq]
        simp [hne_r, hne_c, hne_s]

/-! ### Part 3: Binary Increment Lemmas for `b + 1` at `s = S_close0 n b + 3` -/

lemma testBit_add_one_aux :
    ∀ (k b : ℕ), (∀ i < k, b.testBit i = true) → b.testBit k = false →
      (∀ i < k, (b + 1).testBit i = false) ∧
      (b + 1).testBit k = true ∧
      (∀ i, k < i → (b + 1).testBit i = b.testBit i)
  | 0, b, _, h0 => by
    rw [testBit_zero_eq, decide_eq_false_iff_not] at h0
    have hdiv : (b + 1) / 2 = b / 2 := by omega
    refine ⟨fun i hi => by omega, ?_, ?_⟩
    · rw [testBit_zero_eq, decide_eq_true_eq]; omega
    · intro i hi
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0) with ⟨j, rfl⟩
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
  | k + 1, b, h1, h0 => by
    have hb0 : b.testBit 0 = true := h1 0 (Nat.zero_lt_succ k)
    rw [testBit_zero_eq, decide_eq_true_eq] at hb0
    have hdiv : (b + 1) / 2 = b / 2 + 1 := by omega
    have h1' : ∀ i < k, (b / 2).testBit i = true := by
      intro i hi
      have h := h1 (i + 1) (Nat.succ_lt_succ hi)
      rwa [Nat.testBit_succ] at h
    have h0' : (b / 2).testBit k = false := by
      rwa [Nat.testBit_succ] at h0
    rcases testBit_add_one_aux k (b / 2) h1' h0' with ⟨ih_lt, ih_eq, ih_gt⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases i with _ | j
      · rw [testBit_zero_eq, decide_eq_false_iff_not]; omega
      · rw [Nat.testBit_succ, hdiv]
        exact ih_lt j (by omega)
    · rw [Nat.testBit_succ, hdiv]
      exact ih_eq
    · intro i hi
      rcases i with _ | j
      · omega
      · rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
        exact ih_gt j (by omega)

lemma testBit_add_one_of_lt_lowestZero0 {n b i : ℕ} (hb : b < 2 ^ n - 1)
    (hi : i < lowestZero0 b n) :
    (b + 1).testBit i = false :=
  (testBit_add_one_aux (lowestZero0 b n) b
    (fun _ hj => testBit_of_lt_lowestZero0 hb hj)
    (testBit_lowestZero0 hb)).1 i hi

lemma testBit_add_one_lowestZero0 {n b : ℕ} (hb : b < 2 ^ n - 1) :
    (b + 1).testBit (lowestZero0 b n) = true :=
  (testBit_add_one_aux (lowestZero0 b n) b
    (fun _ hj => testBit_of_lt_lowestZero0 hb hj)
    (testBit_lowestZero0 hb)).2.1

lemma testBit_add_one_of_gt_lowestZero0 {n b i : ℕ} (hb : b < 2 ^ n - 1)
    (hi : lowestZero0 b n < i) :
    (b + 1).testBit i = b.testBit i :=
  (testBit_add_one_aux (lowestZero0 b n) b
    (fun _ hj => testBit_of_lt_lowestZero0 hb hj)
    (testBit_lowestZero0 hb)).2.2 i hi

lemma lowestOne0_add_one {n b : ℕ} (hb : b < 2 ^ n - 1) :
    lowestOne0 (b + 1) n = lowestZero0 b n := by
  have hk := lowestZero0_lt hb
  have hle : lowestOne0 (b + 1) n ≤ lowestZero0 b n :=
    lowestOne0_le_of_testBit_true hk (testBit_add_one_lowestZero0 hb)
  have hbn1 : b + 1 < 2 ^ n := by omega
  have hbit := testBit_lowestOne0 (by omega : 0 < b + 1) hbn1
  by_contra hne
  have hlt : lowestOne0 (b + 1) n < lowestZero0 b n := by omega
  have hfalse := testBit_add_one_of_lt_lowestZero0 hb hlt
  rw [hbit] at hfalse
  contradiction

lemma hasHigherOne0_add_one_of_lt {n b i : ℕ} (hb : b < 2 ^ n - 1)
    (hi : i < lowestZero0 b n) :
    hasHigherOne0 (b + 1) n i = true := by
  rw [hasHigherOne0_iff]
  exact ⟨lowestZero0 b n, hi, lowestZero0_lt hb, testBit_add_one_lowestZero0 hb⟩

lemma hasHigherOne0_add_one_of_ge {n b i : ℕ} (hb : b < 2 ^ n - 1)
    (hi : lowestZero0 b n ≤ i) :
    hasHigherOne0 (b + 1) n i = hasHigherOne0 b n i := by
  rw [Bool.eq_iff_iff, hasHigherOne0_iff, hasHigherOne0_iff]
  constructor
  · rintro ⟨j, hij, hjn, hbit⟩
    rw [testBit_add_one_of_gt_lowestZero0 hb (by omega)] at hbit
    exact ⟨j, hij, hjn, hbit⟩
  · rintro ⟨j, hij, hjn, hbit⟩
    rw [← testBit_add_one_of_gt_lowestZero0 hb (by omega)] at hbit
    exact ⟨j, hij, hjn, hbit⟩

lemma eq_two_pow_iff_all_testBit_false :
    ∀ (n k x : ℕ), k < n → x < 2 ^ n →
      (∀ i < k, x.testBit i = false) → x.testBit k = true →
      (x = 2 ^ k ↔ ∀ j, k < j → j < n → x.testBit j = false)
  | 0, k, x, hkn, _, _, _ => by omega
  | n + 1, 0, x, _, hxn, _, hx0 => by
    rw [testBit_zero_eq, decide_eq_true_eq] at hx0
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    simp only [pow_zero]
    constructor
    · rintro rfl j hj _
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0) with ⟨m, rfl⟩
      rw [Nat.testBit_succ]
      exact Nat.zero_testBit m
    · intro hall
      by_contra hne
      have hdiv0 : 0 < x / 2 := by omega
      have hdivn : x / 2 < 2 ^ n := by omega
      rcases exists_testBit_true_of_pos_of_lt_two_pow n (x / 2) hdiv0 hdivn with ⟨m, hmn, hbit⟩
      have hfalse := hall (m + 1) (by omega) (by omega)
      rw [Nat.testBit_succ, hbit] at hfalse
      contradiction
  | n + 1, k + 1, x, hkn, hxn, hlt, hxk => by
    have hx0 : x.testBit 0 = false := hlt 0 (Nat.zero_lt_succ k)
    rw [testBit_zero_eq, decide_eq_false_iff_not] at hx0
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have hpow_k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hlt' : ∀ i < k, (x / 2).testBit i = false := by
      intro i hi
      have h := hlt (i + 1) (Nat.succ_lt_succ hi)
      rwa [Nat.testBit_succ] at h
    have hxk' : (x / 2).testBit k = true := by
      rwa [Nat.testBit_succ] at hxk
    have ih := eq_two_pow_iff_all_testBit_false n k (x / 2) (by omega) (by omega) hlt' hxk'
    constructor
    · intro hx j hj hjn
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0) with ⟨m, rfl⟩
      rw [Nat.testBit_succ]
      exact ih.mp (by omega) m (by omega) (by omega)
    · intro hall
      have hdiv_eq : x / 2 = 2 ^ k := by
        apply ih.mpr
        intro m hm hmn
        have h := hall (m + 1) (by omega) (by omega)
        rwa [Nat.testBit_succ] at h
      omega

lemma topFlip0_add_one {n b : ℕ} (hb : b < 2 ^ n - 1) :
    topFlip0 (b + 1) n = !hasHigherOne0 b n (lowestZero0 b n) := by
  unfold topFlip0
  rw [lowestOne0_add_one hb]
  have hk := lowestZero0_lt hb
  have hbn1 : b + 1 < 2 ^ n := by omega
  have hiff := eq_two_pow_iff_all_testBit_false n (lowestZero0 b n) (b + 1) hk hbn1
    (fun _ hi => testBit_add_one_of_lt_lowestZero0 hb hi)
    (testBit_add_one_lowestZero0 hb)
  cases hhi : hasHigherOne0 b n (lowestZero0 b n) with
  | true =>
    simp only [Bool.not_true, decide_eq_false_iff_not, not_and]
    intro _ heq
    rcases (hasHigherOne0_iff b n (lowestZero0 b n)).mp hhi with ⟨j, hkj, hjn, hbit⟩
    have hfalse := hiff.mp heq j hkj hjn
    rw [testBit_add_one_of_gt_lowestZero0 hb hkj, hbit] at hfalse
    contradiction
  | false =>
    simp only [Bool.not_false, decide_eq_true_eq]
    refine ⟨by omega, hiff.mpr ?_⟩
    intro j hkj hjn
    rw [testBit_add_one_of_gt_lowestZero0 hb hkj]
    exact (hasHigherOne0_eq_false_iff b n (lowestZero0 b n)).mp hhi j hkj hjn

/-! ### Part 4: Portal Membership, `uStillH0 = true` Chain, `predTau0_optimal`, and `hy / hx / h` -/

lemma mem_portal_zfk_iff_testBit (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w : V_bin n} (hport : HitsPortal glob n b s w .c ∨ HitsPortal glob n b s w .r)
    (j : Fin n) (hj : b < 2 ^ n - 1 → S_close0 n b + 1 ≤ s → lowestZero0 b n < j.val)
    (u : V_bin n) (hu : u = .z j ∨ u = .f j ∨ u = .k j) :
    u ∈ predPath glob n b s w ↔ b.testBit j.val = true := by
  rcases hvalid with ⟨hn, hbn, hs_max⟩
  have hvalid' : ValidState n b s := ⟨hn, hbn, hs_max⟩
  have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    rcases hu with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin]; omega }
  have hne_c : u ≠ .c := by rcases hu with rfl | rfl | rfl <;> nofun
  have hne_r : u ≠ .r := by rcases hu with rfl | rfl | rfl <;> nofun
  have hne_s : u ≠ .s := by rcases hu with rfl | rfl | rfl <;> nofun
  have hF_iff : ∀ (t : Fin n),
      (t.val = lowestOne0 b n ∧ 0 < b) ∨ (t.val = lowestZero0 b n ∧ lowestZero0 b n < j.val) →
      (highMemF n b t u ↔ b.testBit j.val = true) := by
    intro t ht_cond
    rcases hu with rfl | rfl | rfl <;>
    { dsimp [highMemF]
      rcases ht_cond with ⟨ht_eq, hb0⟩ | ⟨ht_eq, hlt⟩
      · have hfin : t = ⟨lowestOne0 b n, lowestOne0_lt hb0 hbn⟩ := Fin.ext ht_eq
        rw [hfin]
        exact highMemF_lowestOne0_iff n b hb0 hbn j
      · rw [Fin.ext_iff, ht_eq]
        exact ⟨fun h => h.elim (by omega) And.right, fun h => Or.inr ⟨hlt, h⟩⟩ }
  rcases hport with hc | hr
  · rw [hc.2 u hp_u]
    cases hsact : sActive0 n b s with
    | false =>
      have hb0 : b = 0 := by
        unfold sActive0 at hsact; rw [decide_eq_false_iff_not] at hsact; omega
      subst hb0
      rw [highMem_c_of_false glob n 0 s hvalid' hsact, Nat.zero_testBit]
      simp [hne_c, hne_s]
    | true =>
      rw [highMem_c_of_true glob n b s hvalid' hsact u hp_u]
      simp only [hne_c, hne_s, false_or]
      apply hF_iff
      unfold sActive0 at hsact; rw [decide_eq_true_eq] at hsact
      unfold sTarg0
      split_ifs with h2
      · right; exact ⟨rfl, hj h2.1 (by omega)⟩
      · left; exact ⟨rfl, hsact.resolve_right h2⟩
  · rw [hr.2 u hp_u]
    cases hract : rActive0 n b s with
    | false =>
      have hb0 : b = 0 := by
        unfold rActive0 at hract; rw [decide_eq_false_iff_not] at hract; omega
      subst hb0
      rw [highMem_r_of_false glob n 0 s hvalid' hract, Nat.zero_testBit]
      simp [hne_r]
    | true =>
      rw [highMem_r_of_true glob n b s hvalid' hract u hp_u]
      simp only [hne_r, false_or]
      apply hF_iff
      unfold rActive0 at hract; rw [decide_eq_true_eq] at hract
      unfold rTarg0
      split_ifs with h2
      · right; exact ⟨rfl, hj h2.1 h2.2⟩
      · left; exact ⟨rfl, hract.resolve_right h2⟩

lemma mem_portal_of_s_eq_close_add_three (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hb : b < 2 ^ n - 1) (hs : s = S_close0 n b + 3)
    {w : V_bin n} (hport : HitsPortal glob n b s w .c ∨ HitsPortal glob n b s w .r)
    (u : V_bin n) (hu : (G_bin n).priority .s < (G_bin n).priority u) :
    u ∈ predPath glob n b s w ↔ highMemF n b ⟨lowestZero0 b n, lowestZero0_lt hb⟩ u := by
  have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    dsimp [G_bin, priority_bin] at hu ⊢; omega
  have hne_c : u ≠ .c := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
  have hne_r : u ≠ .r := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
  have hne_s : u ≠ .s := by intro h; subst h; omega
  rcases hport with hc | hr
  · have hsact : sActive0 n b s = true := by
      unfold sActive0; rw [decide_eq_true_eq]; exact Or.inr ⟨hb, by omega⟩
    have hstarg : (⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hsact⟩ : Fin n) =
        ⟨lowestZero0 b n, lowestZero0_lt hb⟩ := by
      apply Fin.ext; dsimp only; unfold sTarg0; rw [if_pos ⟨hb, by omega⟩]
    rw [hc.2 u hp_u, highMem_c_of_true glob n b s hvalid hsact u hp_u, hstarg]
    simp [hne_c, hne_s]
  · have hract : rActive0 n b s = true := by
      unfold rActive0; rw [decide_eq_true_eq]; exact Or.inr ⟨hb, by omega⟩
    have hrtarg : (⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hract⟩ : Fin n) =
        ⟨lowestZero0 b n, lowestZero0_lt hb⟩ := by
      apply Fin.ext; dsimp only; unfold rTarg0; rw [if_pos ⟨hb, by omega⟩]
    rw [hr.2 u hp_u, highMem_r_of_true glob n b s hvalid hract u hp_u, hrtarg]
    simp [hne_r]

lemma uLim0_le_lowestOne0 (b n : ℕ) : uLim0 b n ≤ lowestOne0 b n := by
  unfold uLim0; split_ifs <;> omega

lemma uLim0_le_hyLim0 (b n s : ℕ) : uLim0 b n ≤ hyLim0 b n s := by
  unfold uLim0 hyLim0; split_ifs <;> simp_all

lemma hitsWithTop_u_of_still (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hb0 : 0 < b) (m₀ : Fin n) (hm₀_eq : m₀.val = uLim0 b n - 1 - s)
    (hm₀_lt : m₀.val + s < uLim0 b n) :
    ∀ k (m : Fin n), m₀.val - m.val ≤ k → 1 ≤ m.val → m.val ≤ m₀.val →
      HitsWithTop glob n b s (.u m) (.g m₀) (.f m₀)
  | 0, m, hk, hm1, hle => by
    have hm_eq : m = m₀ := Fin.ext (by omega)
    subst hm_eq
    have hle_kp := uLim0_le_lowestOne0 b n
    have hle_hy := uLim0_le_hyLim0 b n s
    have hlt_kp : m.val < lowestOne0 b n := by omega
    have hlt_hy : m.val + s < hyLim0 b n s := by omega
    have hbit : b.testBit m.val = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 hlt_kp
    have howner_u : (G_bin n).owner (.u m) = false := by
      dsimp [G_bin, owner_bin]; rw [if_neg (by omega)]
    have hce_u : chooseEdge1 glob n b s (.u m) = false := by
      dsimp [chooseEdge1]
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · rw [decide_eq_false_iff_not, not_not]; exact hm₀_lt
      · exfalso; exact h3 ⟨hb0, hlt_kp⟩
    have hs_u : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u m) = .h m := by
      unfold step predState0; rw [if_pos howner_u, hce_u]; rfl
    have hce_h : chooseEdge1 glob n b s (.h m) = false := by
      dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
    have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h m) = .hx m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
    have hce_hx : chooseEdge1 glob n b s (.hx m) = false := by
      dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
    have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
    have hce_hy : chooseEdge1 glob n b s (.hy m) = false := by
      dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
    have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hy]; rfl
    have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f m) = .g m := rfl
    have hf : HitsWithTop glob n b s (.f m) (.g m) (.f m) :=
      hitsWithTop_of_step_eq glob n b s hvalid (.f m) (.g m) (by nofun) hs_f
    have hhy : HitsWithTop glob n b s (.hy m) (.g m) (.f m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.hy m) (.g m) (.f m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      · rw [hs_hy]; exact hf
    have hhx : HitsWithTop glob n b s (.hx m) (.g m) (.f m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.hx m) (.g m) (.f m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      · rw [hs_hx]; exact hhy
    have hh : HitsWithTop glob n b s (.h m) (.g m) (.f m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.h m) (.g m) (.f m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      · rw [hs_h]; exact hhx
    apply hitsWithTop_of_step_lt glob n b s hvalid (.u m) (.g m) (.f m) (by nofun)
    · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    · rw [hs_u]; exact hh
  | k + 1, m, hk, hm1, hle => by
    by_cases heq : m.val = m₀.val
    · exact hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ hm₀_eq hm₀_lt 0 m (by omega) hm1 hle
    · have hlt_m₀ : m.val < m₀.val := by omega
      have hle_kp := uLim0_le_lowestOne0 b n
      have hle_hy := uLim0_le_hyLim0 b n s
      have hlt_kp : m.val < lowestOne0 b n := by omega
      have hlt_u : m.val + 1 + s < uLim0 b n := by omega
      have hlt_hy : m.val + s < hyLim0 b n s := by omega
      have hbit : b.testBit m.val = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 hlt_kp
      have hm_succ : m.val + 1 < n := by have := m₀.isLt; omega
      have hhi : hasHigherOne0 b n m.val = true := by
        rw [hasHigherOne0_iff]
        exact ⟨lowestOne0 b n, hlt_kp, lowestOne0_lt hb0 hvalid.2.1, testBit_lowestOne0 hb0 hvalid.2.1⟩
      have howner_u : (G_bin n).owner (.u m) = false := by
        dsimp [G_bin, owner_bin]; rw [if_neg (by omega)]
      have hce_u : chooseEdge1 glob n b s (.u m) = false := by
        dsimp [chooseEdge1]
        split_ifs with h1 h2 h3
        · rfl
        · rfl
        · rw [decide_eq_false_iff_not, not_not]; omega
        · exfalso; exact h3 ⟨hb0, hlt_kp⟩
      have hs_u : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u m) = .h m := by
        unfold step predState0; rw [if_pos howner_u, hce_u]; rfl
      have hce_h : chooseEdge1 glob n b s (.h m) = false := by
        dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
      have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h m) = .hx m := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
      have hce_hx : chooseEdge1 glob n b s (.hx m) = false := by
        dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
      have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
      have hce_hy : chooseEdge1 glob n b s (.hy m) = false := by
        dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
      have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hy]; rfl
      have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f m) = .g m := rfl
      have htau : chooseTauEdge1 n b s (.g m) = true := by
        dsimp [chooseTauEdge1]
        have hd : decide (0 < b ∧ m.val < lowestOne0 b n ∧ m.val + 1 + s < uLim0 b n) = true :=
          decide_eq_true ⟨hb0, hlt_kp, hlt_u⟩
        simp [hd]
      have hs_g : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g m) = .k m := by
        unfold step G_bin owner_bin predTau0; rw [if_pos htau]; rfl
      have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k m) = .z m := rfl
      have hce_z : chooseEdge1 glob n b s (.z m) = true := by
        dsimp [chooseEdge1]; simp [hm_succ, hhi]
      have hs_z : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z m) = .u ⟨m.val + 1, hm_succ⟩ := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_z]; dsimp [edge1]; rw [dif_pos hm_succ]
      have ih := hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ hm₀_eq hm₀_lt k ⟨m.val + 1, hm_succ⟩
        (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
      have hz : HitsWithTop glob n b s (.z m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.z m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin]; omega
        · rw [hs_z]; exact ih
      have hk_hit : HitsWithTop glob n b s (.k m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.k m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin]; omega
        · rw [hs_k]; exact hz
      have hg : HitsWithTop glob n b s (.g m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.g m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
        · rw [hs_g]; exact hk_hit
      have hf : HitsWithTop glob n b s (.f m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.f m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin]; omega
        · rw [hs_f]; exact hg
      have hhy : HitsWithTop glob n b s (.hy m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.hy m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
        · rw [hs_hy]; exact hf
      have hhx : HitsWithTop glob n b s (.hx m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.hx m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
        · rw [hs_hx]; exact hhy
      have hh : HitsWithTop glob n b s (.h m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.h m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
        · rw [hs_h]; exact hhx
      apply hitsWithTop_of_step_lt glob n b s hvalid (.u m) (.g m₀) (.f m₀) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      · rw [hs_u]; exact hh

lemma predVal_lt_portal_of_hitsWithTop_still (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hb0 : 0 < b) (m₀ : Fin n) (hm₀_eq : m₀.val = uLim0 b n - 1 - s)
    (hm₀_lt : m₀.val + s < uLim0 b n)
    {w₁ w₂ : V_bin n}
    (hw₁ : HitsWithTop glob n b s w₁ (.g m₀) (.f m₀))
    (hw₂ : HitsPortal glob n b s w₂ .c ∨ HitsPortal glob n b s w₂ .r) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  have hle_kp := uLim0_le_lowestOne0 b n
  have hkp_lt := lowestOne0_lt hb0 hvalid.2.1
  have hlt_kp : m₀.val < lowestOne0 b n := by omega
  have hbit_m₀ : b.testBit m₀.val = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 hlt_kp
  have hs_lt : s < n := by omega
  have htau_m₀ : chooseTauEdge1 n b s (.g m₀) = false := by
    dsimp [chooseTauEdge1]
    simp only [hbit_m₀, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨by omega, by omega⟩
  have hport_g := hitsPortal_g_of_tau_false glob n b s hvalid m₀ htau_m₀
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .f m₀)
  · exact hw₁.2.1
  · rw [mem_portal_zfk_iff_testBit glob n b s hvalid hw₂ m₀ (by unfold S_close0; omega) (.f m₀) (Or.inr (Or.inl rfl)),
        hbit_m₀]
    decide
  · exact prio_f_odd n m₀
  · intro u hu
    rw [hw₁.2.2 u hu]
    have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
      dsimp [G_bin, priority_bin] at hu ⊢; omega
    rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨j, hu_eq⟩
    rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g j (by unfold S_close0; omega) u hu_eq,
        mem_portal_zfk_iff_testBit glob n b s hvalid hw₂ j (by unfold S_close0; omega) u hu_eq]

lemma hitsWithTop_d1_k_of_dClosed0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hd : dClosed0 n b s i = true) :
    HitsWithTop glob n b s (.d1 i) (.k i) (.g i) := by
  have hce1 : chooseEdge1 glob n b s (.d1 i) = true := by
    unfold dClosed0 at hd; dsimp [chooseEdge1]
    rcases Bool.or_eq_true_iff.mp hd with h1 | h2
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h1; rw [if_pos h1.1, if_neg h1.2]
    · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2; rw [if_neg (by simp [h2.1]), if_pos (by omega)]
  have hce2 : chooseEdge1 glob n b s (.d2 i) = true := by
    unfold dClosed0 at hd; dsimp [chooseEdge1]
    rcases Bool.or_eq_true_iff.mp hd with h1 | h2
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h1; rw [if_pos h1.1, if_neg h1.2]
    · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2; rw [if_neg (by simp [h2.1]), if_pos h2.2]
  have hce3 : chooseEdge1 glob n b s (.d3 i) = true := by
    unfold dClosed0 at hd; dsimp [chooseEdge1]
    rcases Bool.or_eq_true_iff.mp hd with h1 | h2
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h1; rw [if_pos h1.1, if_neg h1.2]
    · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2; rw [if_neg (by simp [h2.1]), if_pos (by omega)]
  have htau : chooseTauEdge1 n b s (.g i) = true := by
    unfold dClosed0 at hd; dsimp [chooseTauEdge1]
    rcases Bool.or_eq_true_iff.mp hd with h1 | h2
    · rw [Bool.and_eq_true] at h1; simp [h1.1]
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h2
      have hd' : decide (3 * (n + 2 * i.val + 1) + 2 ≤ s) = true := decide_eq_true h2.2
      simp [hd']
  have hs1 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i) = .d2 i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce1]; rfl
  have hs2 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i) = .d3 i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce2]; rfl
  have hs3 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d3 i) = .g i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce3]; rfl
  have hsg : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .k i := by
    unfold step G_bin owner_bin predTau0; rw [if_pos htau]; rfl
  have hg : HitsWithTop glob n b s (.g i) (.k i) (.g i) :=
    hitsWithTop_of_step_eq glob n b s hvalid (.g i) (.k i) (by nofun) hsg
  have hd3 : HitsWithTop glob n b s (.d3 i) (.k i) (.g i) := by
    apply hitsWithTop_of_step_lt glob n b s hvalid (.d3 i) (.k i) (.g i) (by nofun)
    · dsimp [G_bin, priority_bin]; omega
    · rw [hs3]; exact hg
  have hd2 : HitsWithTop glob n b s (.d2 i) (.k i) (.g i) := by
    apply hitsWithTop_of_step_lt glob n b s hvalid (.d2 i) (.k i) (.g i) (by nofun)
    · dsimp [G_bin, priority_bin]; omega
    · rw [hs2]; exact hd3
  apply hitsWithTop_of_step_lt glob n b s hvalid (.d1 i) (.k i) (.g i) (by nofun)
  · dsimp [G_bin, priority_bin]; omega
  · rw [hs1]; exact hd2

private lemma predTau0_eq_of_ne_g (n b s : ℕ) (v : V_bin n)
    (howner : (G_bin n).owner v = true) (hne : ∀ i, v ≠ .g i) :
    predTau0 n b s v = edge0 n v ∧ edge1 n v = edge0 n v := by
  cases v with
  | rp _ | sp _ | l2 _ | l3 _ | r_2 | r | s | d1 _ | d2 _ | d3 _ | hy _ | hx _ | h _ | z _ =>
    contradiction
  | g i => exact False.elim (hne i rfl)
  | u i =>
    dsimp [G_bin, owner_bin] at howner
    split_ifs at howner with hi0
    refine ⟨rfl, ?_⟩
    dsimp [edge0, edge1]
    rw [dif_neg (by omega)]
  | l1 m =>
    dsimp [G_bin, owner_bin] at howner
    split_ifs at howner with hm0
    refine ⟨rfl, ?_⟩
    dsimp [edge0, edge1]
    rw [if_pos hm0]
    congr 1
    ext
    dsimp
    omega
  | lp1 m | lp2 m | lp3 m =>
    dsimp [G_bin, owner_bin] at howner
    split_ifs at howner with hm0
    refine ⟨rfl, ?_⟩
    simp [edge0, edge1, hm0]
  | a j =>
    dsimp [G_bin, owner_bin] at howner
    split_ifs at howner with hj
    refine ⟨rfl, ?_⟩
    rcases hj with hj0 | hj1
    · simp [edge0, edge1, hj0]
    · have hj1' : j.val = 3 * (3 * n - 1) - 1 := hj1
      simp [edge0, edge1, hj1']
  | x | r_2_odd | r_a | c_odd | c | b _ | f _ | k _ =>
    exact ⟨rfl, rfl⟩

theorem predTau0_optimal (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
    ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v := by
  apply optimalCounterstrategy_of_min_step (G_bin_wellFormed n hvalid.1) (predTau0_legal n b s)
  intro v w howner hedge
  cases v with
  | g i =>
    rcases hedge with rfl | rfl
    · -- w = edge0 n (.g i) = .d1 i
      unfold predTau0
      split_ifs with htau
      · right
        dsimp [edge0, edge1]
        cases hd : dClosed0 n b s i with
        | true =>
          exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid
            (hitsWithTop_d1_k_of_dClosed0 glob n b s hvalid i hd)
            (prio_g_even n i)
        | false =>
          have hport_d1 := hitsPortal_d1_of_not_dClosed0 glob n b s hvalid i hd
          cases hbit : b.testBit i.val with
          | true =>
            have hcond : b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 3 := by
              unfold dClosed0 at hd
              simp [hbit] at hd
              exact hd
            rcases hcond with ⟨hb_lt, hik, hs3⟩
            let kFin : Fin n := ⟨lowestZero0 b n, lowestZero0_lt hb_lt⟩
            have hp_c : (G_bin n).priority .c ≤ (G_bin n).priority (.k kFin) := by
              dsimp [G_bin, priority_bin]; omega
            have hp_s : (G_bin n).priority .s < (G_bin n).priority (.k kFin) := by
              dsimp [G_bin, priority_bin]; omega
            have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
            have hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false :=
              fun hi1 => uStillH0_succ_false_of_testBit_true n b s i hi1 hbit
            apply predVal_lt_of_setLT glob n b s hvalid
            apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := .k kFin)
            · rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k, Finset.mem_insert]
              change V_bin.k kFin = V_bin.k i ∨ V_bin.k kFin ∈ predPath glob n b s (.z i) → False
              rw [highMem_z glob n b s hvalid i hstill (.k kFin) hp_c]
              dsimp [highMemZ, kFin]
              rw [testBit_lowestZero0 hb_lt]
              rintro (h | ⟨_, htrue⟩)
              · injection h with h'; have := Fin.ext_iff.mp h'; dsimp [kFin] at this; omega
              · contradiction
            · rw [mem_portal_of_s_eq_close_add_three glob n b s hvalid hb_lt hs3 hport_d1 (.k kFin) hp_s]
              exact Or.inl rfl
            · exact prio_k_even n kFin
            · intro u hu
              have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
                dsimp [G_bin, priority_bin] at hu ⊢; omega
              have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
                dsimp [G_bin, priority_bin] at hu ⊢; omega
              rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k, Finset.mem_insert]
              change u = .k i ∨ u ∈ predPath glob n b s (.z i) ↔ _
              rw [highMem_z glob n b s hvalid i hstill u hp_u_c,
                  mem_portal_of_s_eq_close_add_three glob n b s hvalid hb_lt hs3 hport_d1 u hp_u_s]
              have hkFin_val : kFin.val = lowestZero0 b n := rfl
              rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, rfl | rfl | rfl⟩
              · have hkj : lowestZero0 b n < j.val := by
                  dsimp [G_bin, priority_bin] at hu; omega
                dsimp [highMemZ, highMemF]
                simp only [reduceCtorEq, false_or, Fin.ext_iff]
                constructor
                · rintro (heq | ⟨_, hbj⟩)
                  · omega
                  · exact Or.inr ⟨hkj, hbj⟩
                · rintro (heq | ⟨_, hbj⟩)
                  · omega
                  · exact Or.inr ⟨by omega, hbj⟩
              · have hkj : lowestZero0 b n < j.val := by
                  dsimp [G_bin, priority_bin] at hu; omega
                dsimp [highMemZ, highMemF]
                simp only [reduceCtorEq, false_or]
                constructor
                · rintro ⟨_, hbj⟩
                  exact Or.inr ⟨hkj, hbj⟩
                · rintro (heq | ⟨_, hbj⟩)
                  · omega
                  · exact ⟨by omega, hbj⟩
              · have hkj : lowestZero0 b n < j.val := by
                  dsimp [G_bin, priority_bin] at hu; omega
                dsimp [highMemZ, highMemF]
                constructor
                · rintro (h | ⟨_, hbj⟩)
                  · injection h with h'; have := Fin.ext_iff.mp h'; omega
                  · exact Or.inr ⟨hkj, hbj⟩
                · rintro (heq | ⟨_, hbj⟩)
                  · omega
                  · exact Or.inr ⟨by omega, hbj⟩
          | false =>
            have hlt_T : ¬(3 * (n + 2 * i.val + 1) + 2 ≤ s) := by
              unfold dClosed0 at hd; simp [hbit] at hd; omega
            have hstill : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + 1 + s < uLim0 b n := by
              dsimp [chooseTauEdge1] at htau
              simp [hbit, hlt_T] at htau
              exact htau
            rcases hstill with ⟨hb0, hikp, hlt_u⟩
            have hle_kp := uLim0_le_lowestOne0 b n
            have hkp_lt := lowestOne0_lt hb0 hvalid.2.1
            let m₀ : Fin n := ⟨uLim0 b n - 1 - s, by omega⟩
            have hi1 : i.val + 1 < n := by omega
            have hhi : hasHigherOne0 b n i.val = true := by
              rw [hasHigherOne0_iff]
              exact ⟨lowestOne0 b n, hikp, hkp_lt, testBit_lowestOne0 hb0 hvalid.2.1⟩
            have hce_z : chooseEdge1 glob n b s (.z i) = true := by
              dsimp [chooseEdge1]; simp [hi1, hhi]
            have hs_z : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z i) = .u ⟨i.val + 1, hi1⟩ := by
              unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_z]; dsimp [edge1]; rw [dif_pos hi1]
            have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
            have hu_hit := hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ rfl (by dsimp [m₀]; omega)
              n ⟨i.val + 1, hi1⟩ (by dsimp [m₀]; omega) (by dsimp only; omega) (by dsimp [m₀]; omega)
            have hz_hit : HitsWithTop glob n b s (.z i) (.g m₀) (.f m₀) := by
              apply hitsWithTop_of_step_lt glob n b s hvalid (.z i) (.g m₀) (.f m₀) (by nofun)
              · dsimp [G_bin, priority_bin, m₀]; omega
              · rw [hs_z]; exact hu_hit
            have hk_hit : HitsWithTop glob n b s (.k i) (.g m₀) (.f m₀) := by
              apply hitsWithTop_of_step_lt glob n b s hvalid (.k i) (.g m₀) (.f m₀) (by nofun)
              · dsimp [G_bin, priority_bin, m₀]; omega
              · rw [hs_k]; exact hz_hit
            exact predVal_lt_portal_of_hitsWithTop_still glob n b s hvalid hb0 m₀ rfl (by dsimp [m₀]; omega)
              hk_hit hport_d1
      · exact valueLE_refl (G_bin n) _
    · -- w = edge1 n (.g i) = .k i
      unfold predTau0
      split_ifs with htau
      · exact valueLE_refl (G_bin n) _
      · right
        dsimp [edge0, edge1]
        have htau_false : chooseTauEdge1 n b s (.g i) = false := Bool.eq_false_of_not_eq_true htau
        have hd := dClosed0_eq_false_of_tau_false n b s i htau_false
        have hport_d1 := hitsPortal_d1_of_not_dClosed0 glob n b s hvalid i hd
        have hcond := htau_false
        dsimp [chooseTauEdge1] at hcond
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hcond
        rcases hcond with ⟨⟨hbit, hlt_T⟩, hnot_still⟩
        have hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
          intro hi1
          unfold uStillH0
          rw [decide_eq_false_iff_not]
          dsimp only
          intro h
          exact hnot_still ⟨h.1, by omega, h.2.2⟩
        have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
        have hk_path : predPath glob n b s (.k i) = insert (V_bin.k i) (predPath glob n b s (.z i)) :=
          by rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k]
        apply predVal_lt_of_setLT glob n b s hvalid
        apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := .k i)
        · rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_d1 i (by unfold S_close0; omega) (.k i) (Or.inr (Or.inr rfl)),
              hbit]
          decide
        · rw [hk_path]
          exact Finset.mem_insert_self (V_bin.k i) _
        · exact prio_k_even n i
        · intro u hu
          have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          rw [hk_path, Finset.mem_insert]
          rw [highMem_z glob n b s hvalid i hstill u hp_u_c]
          rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, hu_eq⟩
          have hij : i.val < j.val := by
            rcases hu_eq with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin] at hu; omega }
          rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_d1 j (by unfold S_close0; omega) u hu_eq]
          rcases hu_eq with rfl | rfl | rfl
          · dsimp [highMemZ]
            simp only [reduceCtorEq, false_or, Fin.ext_iff]
            exact ⟨fun h => Or.inr ⟨hij, h⟩, fun h => h.elim (by omega) And.right⟩
          · dsimp [highMemZ]
            simp only [reduceCtorEq, false_or]
            exact ⟨fun h => ⟨hij, h⟩, And.right⟩
          · dsimp [highMemZ]
            constructor
            · intro h; exact Or.inr ⟨hij, h⟩
            · rintro (h | ⟨_, h⟩)
              · injection h with h'; have := Fin.ext_iff.mp h'; omega
              · exact h
  | x | r_2_odd | r_a | c_odd | c | u _ | f _ | k _ | l1 _ | lp1 _ | lp2 _ | lp3 _ | a _ | b _ =>
    have htau_v := predTau0_eq_of_ne_g n b s _ howner (by nofun)
    rcases hedge with rfl | rfl
    · rw [htau_v.1]; exact valueLE_refl (G_bin n) _
    · rw [htau_v.1, htau_v.2]; exact valueLE_refl (G_bin n) _
  | rp _ | sp _ | l2 _ | l3 _ | r_2 | r | s | d1 _ | d2 _ | d3 _ | hy _ | hx _ | h _ | z _ =>
    contradiction

/-! ### Part 5: `bestEdge_hy`, `bestEdge_hx`, and `bestEdge_h` -/

lemma testBit_two_pow_sub_one : ∀ (n i : ℕ), i < n → (2 ^ n - 1).testBit i = true
  | 0, i, hi => by omega
  | n + 1, 0, _ => by
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [testBit_zero_eq, decide_eq_true_eq]
    omega
  | n + 1, i + 1, hi => by
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by omega
    rw [Nat.testBit_succ, hdiv]
    exact testBit_two_pow_sub_one n i (Nat.lt_of_succ_lt_succ hi)

lemma hitsWithTop_f_z_of_tau_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (htau : chooseTauEdge1 n b s (.g i) = true) :
    HitsWithTop glob n b s (.f i) (.z i) (.k i) := by
  have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
  have hs_g : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .k i := by
    unfold step predTau0; rw [if_neg (by nofun), if_pos htau]; rfl
  have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f i) = .g i := rfl
  have hk := hitsWithTop_of_step_eq glob n b s hvalid (.k i) (.z i) (by nofun) hs_k
  have hg : HitsWithTop glob n b s (.g i) (.z i) (.k i) := by
    apply hitsWithTop_of_step_lt glob n b s hvalid (.g i) (.z i) (.k i) (by nofun)
    · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega
    · rw [hs_g]; exact hk
  apply hitsWithTop_of_step_lt glob n b s hvalid (.f i) (.z i) (.k i) (by nofun)
  · dsimp [G_bin, priority_bin]; omega
  · rw [hs_f]; exact hg

lemma hitsWithTop_f_z_of_tau_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (htau : chooseTauEdge1 n b s (.g i) = false) :
    HitsWithTop glob n b s (.f i) (.z i) (.f i) := by
  have hport_g := hitsPortal_g_of_tau_false glob n b s hvalid i htau
  have hcond := htau
  dsimp [chooseTauEdge1] at hcond
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hcond
  rcases hcond with ⟨⟨hbit, hlt_T⟩, hnot_still⟩
  have hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
    intro hi1
    unfold uStillH0
    rw [decide_eq_false_iff_not]
    dsimp only
    intro h
    exact hnot_still ⟨h.1, by omega, h.2.2⟩
  have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f i) = .g i := rfl
  have hf_path : predPath glob n b s (.f i) = insert (V_bin.f i) (predPath glob n b s (.g i)) :=
    by rw [predPath, predVal, pred_path_step glob n b s hvalid (.f i) (by nofun), hs_f]
  refine ⟨by dsimp [predRank0]; omega, ?_, ?_⟩
  · rw [hf_path]
    exact Finset.mem_insert_self (V_bin.f i) _
  · intro u hu
    have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
      dsimp [G_bin, priority_bin] at hu ⊢; omega
    have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
      dsimp [G_bin, priority_bin] at hu ⊢; omega
    have hne_f : u ≠ .f i := by intro heq; subst heq; omega
    rw [hf_path, Finset.mem_insert, highMem_z glob n b s hvalid i hstill u hp_u_c]
    simp only [hne_f, false_or]
    rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, hu_eq⟩
    rcases hu_eq with rfl | rfl | rfl
    · have hij : i.val < j.val := by dsimp [G_bin, priority_bin] at hu; omega
      rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g j (by unfold S_close0; omega) (.z j) (Or.inl rfl)]
      dsimp [highMemZ]
      simp only [Fin.ext_iff]
      exact ⟨fun h => Or.inr ⟨hij, h⟩, fun h => h.elim (by omega) And.right⟩
    · have hij : i.val < j.val := by
        by_cases heq : j.val = i.val
        · exfalso; exact hne_f (congrArg V_bin.f (Fin.ext heq))
        · dsimp [G_bin, priority_bin] at hu; omega
      rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g j (by unfold S_close0; omega) (.f j) (Or.inr (Or.inl rfl))]
      dsimp [highMemZ]
      exact ⟨fun h => ⟨hij, h⟩, And.right⟩
    · have hij : i.val ≤ j.val := by dsimp [G_bin, priority_bin] at hu; omega
      rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g j (by unfold S_close0; omega) (.k j) (Or.inr (Or.inr rfl))]
      dsimp [highMemZ]
      by_cases heq : j.val = i.val
      · rw [heq, hbit]
        simp
      · have hlt : i.val < j.val := by omega
        exact ⟨fun h => ⟨hlt, h⟩, And.right⟩

lemma hyLim0_le_n (b n s : ℕ) : hyLim0 b n s ≤ n := by
  have := lowestOne0_le b n
  unfold hyLim0
  split_ifs <;> omega

lemma bestEdge1_hy_eq (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    bestEdge1 n b s (.hy i) = !chooseTauEdge1 n b s (.g i) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have hi := i.isLt
  unfold bestEdge1 nextPair
  split_ifs with h1 h2
  · have hbit : b.testBit i.val = true := by
      rw [h1.1]
      exact testBit_two_pow_sub_one n i.val hi
    dsimp [chooseEdge1, chooseTauEdge1]
    simp [hbit]
  · rcases h2 with ⟨hb_lt, hs3⟩
    have hb1_0 : 0 < b + 1 := by omega
    have hlo1 := lowestOne0_add_one hb_lt
    have hhy0 : hyLim0 (b + 1) n 0 = lowestZero0 b n := by
      unfold hyLim0; simp [hlo1]
    by_cases hik : i.val < lowestZero0 b n
    · have hbit : b.testBit i.val = true := testBit_of_lt_lowestZero0 hb_lt hik
      have hbit1 : (b + 1).testBit i.val = false := testBit_add_one_of_lt_lowestZero0 hb_lt hik
      dsimp [chooseEdge1, chooseTauEdge1]
      rw [if_neg (by simp [hbit1]), if_pos ⟨hb1_0, by omega, by omega⟩]
      simp [hbit]
    · by_cases heq : i.val = lowestZero0 b n
      · have hbit1 : (b + 1).testBit i.val = true := by
          rw [heq]; exact testBit_add_one_lowestZero0 hb_lt
        have hle_s : 3 * (n + 2 * i.val + 1) + 2 ≤ s := by
          unfold S_close0 at hs3; omega
        dsimp [chooseEdge1, chooseTauEdge1]
        rw [if_pos hbit1]
        simp [hle_s]
      · have hgt : lowestZero0 b n < i.val := by omega
        have hbit1 : (b + 1).testBit i.val = b.testBit i.val := testBit_add_one_of_gt_lowestZero0 hb_lt hgt
        dsimp [chooseEdge1, chooseTauEdge1]
        rw [hbit1]
        cases hbit : b.testBit i.val with
        | true => simp
        | false =>
          have hnot_lo1 : ¬(0 < b + 1 ∧ i.val < lowestOne0 (b + 1) n ∧ i.val < hyLim0 (b + 1) n 0) := by
            rw [hlo1]; omega
          have hnot_T : ¬(3 * (n + 2 * i.val + 1) + 2 ≤ s) := by
            unfold S_close0 at hs3; omega
          have hnot_u : ¬(0 < b ∧ i.val < lowestOne0 b n ∧ i.val + 1 + s < uLim0 b n) := by
            have := uLim0_le_lowestOne0 b n
            have := lowestOne0_le b n
            unfold S_close0 at hs3
            omega
          rw [if_neg (by decide), if_neg hnot_lo1]
          by_cases hcond : b + 1 < 2 ^ n - 1 ∧ i.val = lowestZero0 (b + 1) n
          · rw [if_pos hcond]; simp [hnot_T, hnot_u]
          · rw [if_neg hcond]; simp [hnot_T, hnot_u]
  · dsimp [chooseEdge1, chooseTauEdge1]
    cases hbit : b.testBit i.val with
    | true => simp
    | false =>
      have hb_lt : b < 2 ^ n - 1 := by
        by_contra hge
        have heq_b : b = 2 ^ n - 1 := by omega
        rw [heq_b, testBit_two_pow_sub_one n i.val hi] at hbit
        contradiction
      have hs_max := maxStep0_of_lt hb_lt
      have hs_le : s ≤ S_close0 n b + 2 := by omega
      have hle_k : lowestZero0 b n ≤ i.val := lowestZero0_le_of_testBit_false hi hbit
      have hhy_s1 : hyLim0 b n (s + 1) = uLim0 b n := by
        unfold hyLim0 uLim0; simp
      rw [if_neg (by decide), hhy_s1]
      by_cases hstill : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + (s + 1) < uLim0 b n
      · have hstill' : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + 1 + s < uLim0 b n :=
          ⟨hstill.1, hstill.2.1, by omega⟩
        rw [if_pos hstill]
        simp [hstill']
      · rw [if_neg hstill]
        have hnot_still' : ¬(0 < b ∧ i.val < lowestOne0 b n ∧ i.val + 1 + s < uLim0 b n) := by
          intro h; exact hstill ⟨h.1, h.2.1, by omega⟩
        by_cases h_eq_k : b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n
        · rw [if_pos h_eq_k]
          have hT_eq : 3 * (n + 2 * i.val + 1) + 2 = S_close0 n b := by
            unfold S_close0; rw [h_eq_k.2]
          rw [hT_eq]
          by_cases hs_lt : s < S_close0 n b
          · have hs1 : s + 1 < S_close0 n b + 1 := by omega
            have hs2 : ¬(S_close0 n b ≤ s) := by omega
            simp [hs1, hs2, hnot_still']
          · have hs1 : ¬(s + 1 < S_close0 n b + 1) := by omega
            have hs2 : S_close0 n b ≤ s := by omega
            simp [hs1, hs2, hnot_still']
        · rw [if_neg h_eq_k]
          have hgt_k : lowestZero0 b n < i.val := by
            by_contra hle; exact h_eq_k ⟨hb_lt, by omega⟩
          have hnot_T : ¬(3 * (n + 2 * i.val + 1) + 2 ≤ s) := by
            unfold S_close0 at hs_le; omega
          simp [hnot_T, hnot_still']

lemma chooseEdge1_hy_eq (glob : Bool) (n b s : ℕ) (i : Fin n) :
    chooseEdge1 glob n b s (.hy i) =
      (!b.testBit i.val &&
       !decide (0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s) &&
       !decide (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 1 ≤ s)) := by
  dsimp [chooseEdge1]
  split_ifs with h1 h2 h3
  · simp only [h1, Bool.not_true, Bool.false_and]
  · rw [decide_eq_true h2]; simp
  · have h3_iff : (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 1 ≤ s) ↔ ¬(s < S_close0 n b + 1) :=
      ⟨fun ⟨_, _, h⟩ => by omega, fun h => ⟨h3.1, h3.2, by omega⟩⟩
    rw [decide_eq_false h2]
    simp only [h1, h3_iff, Bool.not_false, Bool.true_and, decide_not, Bool.not_not]
  · have h3' : ¬(b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 1 ≤ s) :=
      fun ⟨ha, hb, _⟩ => h3 ⟨ha, hb⟩
    rw [decide_eq_false h2, decide_eq_false h3']
    simp [h1]

lemma chooseEdge1_hx_eq (glob : Bool) (n b s : ℕ) (i : Fin n) :
    chooseEdge1 glob n b s (.hx i) =
      (!b.testBit i.val &&
       !decide (0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s) &&
       !decide (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s)) := by
  dsimp [chooseEdge1]
  split_ifs with h1 h2 h3
  · simp only [h1, Bool.not_true, Bool.false_and]
  · rw [decide_eq_true h2]; simp
  · have h3_iff : (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) ↔ ¬(s < S_close0 n b + 2) :=
      ⟨fun ⟨_, _, h⟩ => by omega, fun h => ⟨h3.1, h3.2, by omega⟩⟩
    rw [decide_eq_false h2]
    simp only [h1, h3_iff, Bool.not_false, Bool.true_and, decide_not, Bool.not_not]
  · have h3' : ¬(b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) :=
      fun ⟨ha, hb, _⟩ => h3 ⟨ha, hb⟩
    rw [decide_eq_false h2, decide_eq_false h3']
    simp [h1]

lemma chooseEdge1_h_eq (glob : Bool) (n b s : ℕ) (i : Fin n) :
    chooseEdge1 glob n b s (.h i) =
      (!b.testBit i.val &&
       !decide (0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s) &&
       !decide (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 3 ≤ s)) := by
  dsimp [chooseEdge1]
  split_ifs with h1 h2 h3
  · simp only [h1, Bool.not_true, Bool.false_and]
  · rw [decide_eq_true h2]; simp
  · have h3_iff : (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 3 ≤ s) ↔ ¬(s < S_close0 n b + 3) :=
      ⟨fun ⟨_, _, h⟩ => by omega, fun h => ⟨h3.1, h3.2, by omega⟩⟩
    rw [decide_eq_false h2]
    simp only [h1, h3_iff, Bool.not_false, Bool.true_and, decide_not, Bool.not_not]
  · have h3' : ¬(b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 3 ≤ s) :=
      fun ⟨ha, hb, _⟩ => h3 ⟨ha, hb⟩
    rw [decide_eq_false h2, decide_eq_false h3']
    simp [h1]

private lemma bool_eq_or_of_imp {L R : Bool} (h : R = true → L = true) : L = (R || L) := by
  cases L <;> cases R <;> simp_all

private lemma bool_and_eq_or_and {A0 A1 B0 B1 : Bool}
    (hA : A0 = true → A1 = true)
    (hB : B0 = true → B1 = true)
    (hAB : A0 = false → B0 = true) :
    (A1 && B1) = ((A0 && B1) || (A1 && B0)) := by
  cases A0 <;> cases A1 <;> cases B0 <;> cases B1 <;> simp_all

lemma bestEdge1_hx_eq (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    bestEdge1 n b s (.hx i) = (chooseEdge1 glob n b s (.hy i) || !chooseTauEdge1 n b s (.g i)) := by
  rw [← bestEdge1_hy_eq n b s hvalid i]
  rcases hvalid with ⟨hn, hbn, hs⟩
  have hi := i.isLt
  unfold bestEdge1 nextPair
  split_ifs with h1 h2
  · have hbit : b.testBit i.val = true := by
      rw [h1.1]
      exact testBit_two_pow_sub_one n i.val hi
    rw [chooseEdge1_hx_eq, chooseEdge1_hy_eq, chooseEdge1_hy_eq]
    simp [hbit]
  · rcases h2 with ⟨hb_lt, hs3⟩
    rw [chooseEdge1_hx_eq, chooseEdge1_hy_eq, chooseEdge1_hy_eq]
    have h0_2 : ¬(b + 1 < 2 ^ n - 1 ∧ i.val = lowestZero0 (b + 1) n ∧ S_close0 n (b + 1) + 2 ≤ 0) := by omega
    have h0_1 : ¬(b + 1 < 2 ^ n - 1 ∧ i.val = lowestZero0 (b + 1) n ∧ S_close0 n (b + 1) + 1 ≤ 0) := by omega
    simp only [h0_2, h0_1, decide_false, Bool.not_false, Bool.and_true]
    apply bool_eq_or_of_imp
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    rintro ⟨⟨hbit, _⟩, hnot_k⟩
    have hle_k := lowestZero0_le_of_testBit_false hi hbit
    have hne_k : i.val ≠ lowestZero0 b n := fun heq => hnot_k ⟨hb_lt, heq, by omega⟩
    have hgt_k : lowestZero0 b n < i.val := by omega
    have hbit1 : (b + 1).testBit i.val = false := by
      rw [testBit_add_one_of_gt_lowestZero0 hb_lt hgt_k, hbit]
    have hlo1 := lowestOne0_add_one hb_lt
    exact ⟨hbit1, by omega⟩
  · rw [chooseEdge1_hx_eq, chooseEdge1_hy_eq, chooseEdge1_hy_eq]
    cases hbit : b.testBit i.val with
    | true => simp
    | false =>
      simp only [Bool.not_false, Bool.true_and]
      have hhy_s1 : hyLim0 b n (s + 1) = uLim0 b n := by unfold hyLim0 uLim0; simp
      have hle_u_hy := uLim0_le_hyLim0 b n s
      rw [hhy_s1]
      have hB1 : (!decide (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s + 1)) =
          (!decide (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 1 ≤ s)) := by
        congr 2; exact propext ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩⟩
      rw [hB1]
      apply bool_and_eq_or_and
      · simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        intro hnot h
        exact hnot ⟨h.1, h.2.1, by omega⟩
      · simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        intro hnot h
        exact hnot ⟨h.1, h.2.1, by omega⟩
      · simp only [Bool.not_eq_false', Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
        intro h
        have := hyLim0_le_n b n s
        unfold S_close0
        omega

lemma bestEdge1_h_eq (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    bestEdge1 n b s (.h i) = (chooseEdge1 glob n b s (.hx i) || !chooseTauEdge1 n b s (.g i)) := by
  rw [← bestEdge1_hy_eq n b s hvalid i]
  rcases hvalid with ⟨hn, hbn, hs⟩
  have hi := i.isLt
  unfold bestEdge1 nextPair
  split_ifs with h1 h2
  · have hbit : b.testBit i.val = true := by
      rw [h1.1]
      exact testBit_two_pow_sub_one n i.val hi
    rw [chooseEdge1_h_eq, chooseEdge1_hx_eq, chooseEdge1_hy_eq]
    simp [hbit]
  · rcases h2 with ⟨hb_lt, hs3⟩
    rw [chooseEdge1_h_eq, chooseEdge1_hx_eq, chooseEdge1_hy_eq]
    have h0_3 : ¬(b + 1 < 2 ^ n - 1 ∧ i.val = lowestZero0 (b + 1) n ∧ S_close0 n (b + 1) + 3 ≤ 0) := by omega
    have h0_1 : ¬(b + 1 < 2 ^ n - 1 ∧ i.val = lowestZero0 (b + 1) n ∧ S_close0 n (b + 1) + 1 ≤ 0) := by omega
    simp only [h0_3, h0_1, decide_false, Bool.not_false, Bool.and_true]
    apply bool_eq_or_of_imp
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    rintro ⟨⟨hbit, _⟩, hnot_k⟩
    have hle_k := lowestZero0_le_of_testBit_false hi hbit
    have hne_k : i.val ≠ lowestZero0 b n := fun heq => hnot_k ⟨hb_lt, heq, by omega⟩
    have hgt_k : lowestZero0 b n < i.val := by omega
    have hbit1 : (b + 1).testBit i.val = false := by
      rw [testBit_add_one_of_gt_lowestZero0 hb_lt hgt_k, hbit]
    have hlo1 := lowestOne0_add_one hb_lt
    exact ⟨hbit1, by omega⟩
  · rw [chooseEdge1_h_eq, chooseEdge1_hx_eq, chooseEdge1_hy_eq]
    cases hbit : b.testBit i.val with
    | true => simp
    | false =>
      simp only [Bool.not_false, Bool.true_and]
      have hhy_s1 : hyLim0 b n (s + 1) = uLim0 b n := by unfold hyLim0 uLim0; simp
      have hle_u_hy := uLim0_le_hyLim0 b n s
      rw [hhy_s1]
      have hB1 : (!decide (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 3 ≤ s + 1)) =
          (!decide (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s)) := by
        congr 2; exact propext ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩⟩
      rw [hB1]
      apply bool_and_eq_or_and
      · simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        intro hnot h
        exact hnot ⟨h.1, h.2.1, by omega⟩
      · simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        intro hnot h
        exact hnot ⟨h.1, h.2.1, by omega⟩
      · simp only [Bool.not_eq_false', Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
        intro h
        have := hyLim0_le_n b n s
        unfold S_close0
        omega

theorem bestEdge_hy (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    BestEdgeProp glob n b s (.hy i) := by
  intro _ _
  unfold bestEdge worstEdge
  rw [bestEdge1_hy_eq n b s hvalid i]
  cases htau : chooseTauEdge1 n b s (.g i) with
  | true =>
    dsimp [edge0, edge1]
    exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid
      (hitsWithTop_f_z_of_tau_true glob n b s hvalid i htau) (prio_k_even n i)
  | false =>
    dsimp [edge0, edge1]
    exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid
      (hitsWithTop_f_z_of_tau_false glob n b s hvalid i htau) (prio_f_odd n i)

lemma hitsWithTop_hy_z_of_ce_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hce : chooseEdge1 glob n b s (.hy i) = true) :
    HitsWithTop glob n b s (.hy i) (.z i) (.hy i) := by
  have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy i) = .z i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce]; rfl
  exact hitsWithTop_of_step_eq glob n b s hvalid (.hy i) (.z i) (by nofun) hs_hy

lemma hitsWithTop_hy_z_of_ce_false_tau_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hce : chooseEdge1 glob n b s (.hy i) = false)
    (htau : chooseTauEdge1 n b s (.g i) = false) :
    HitsWithTop glob n b s (.hy i) (.z i) (.f i) := by
  have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy i) = .f i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce]; rfl
  apply hitsWithTop_of_step_lt glob n b s hvalid (.hy i) (.z i) (.f i) (by nofun)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega
  · rw [hs_hy]; exact hitsWithTop_f_z_of_tau_false glob n b s hvalid i htau

lemma hitsWithTop_hy_z_of_ce_false_tau_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hce : chooseEdge1 glob n b s (.hy i) = false)
    (htau : chooseTauEdge1 n b s (.g i) = true) :
    HitsWithTop glob n b s (.hy i) (.z i) (.k i) := by
  have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy i) = .f i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce]; rfl
  apply hitsWithTop_of_step_lt glob n b s hvalid (.hy i) (.z i) (.k i) (by nofun)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega
  · rw [hs_hy]; exact hitsWithTop_f_z_of_tau_true glob n b s hvalid i htau

theorem bestEdge_hx (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    BestEdgeProp glob n b s (.hx i) := by
  intro _ _
  unfold bestEdge worstEdge
  rw [bestEdge1_hx_eq glob n b s hvalid i]
  cases hce : chooseEdge1 glob n b s (.hy i) with
  | true =>
    dsimp [edge0, edge1]
    exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid
      (hitsWithTop_hy_z_of_ce_true glob n b s hvalid i hce) (prio_hy_odd n i)
  | false =>
    cases htau : chooseTauEdge1 n b s (.g i) with
    | true =>
      dsimp [edge0, edge1]
      exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid
        (hitsWithTop_hy_z_of_ce_false_tau_true glob n b s hvalid i hce htau) (prio_k_even n i)
    | false =>
      dsimp [edge0, edge1]
      exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid
        (hitsWithTop_hy_z_of_ce_false_tau_false glob n b s hvalid i hce htau) (prio_f_odd n i)

theorem bestEdge_h (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    BestEdgeProp glob n b s (.h i) := by
  intro _ _
  unfold bestEdge worstEdge
  rw [bestEdge1_h_eq glob n b s hvalid i]
  cases hce_hx : chooseEdge1 glob n b s (.hx i) with
  | true =>
    dsimp [edge0, edge1]
    have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx i) = .z i := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_hx]; rfl
    exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid
      (hitsWithTop_of_step_eq glob n b s hvalid (.hx i) (.z i) (by nofun) hs_hx) (prio_hx_odd n i)
  | false =>
    have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx i) = .hy i := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
    have hce_hy : chooseEdge1 glob n b s (.hy i) = false := by
      dsimp [chooseEdge1] at hce_hx ⊢
      split_ifs at hce_hx ⊢ with h1 h2 h3
      · rfl
      · rfl
      · rw [decide_eq_false_iff_not] at hce_hx ⊢
        omega
    cases htau : chooseTauEdge1 n b s (.g i) with
    | true =>
      dsimp [edge0, edge1]
      have hhit : HitsWithTop glob n b s (.hx i) (.z i) (.k i) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.hx i) (.z i) (.k i) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega
        · rw [hs_hx]; exact hitsWithTop_hy_z_of_ce_false_tau_true glob n b s hvalid i hce_hy htau
      exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid hhit (prio_k_even n i)
    | false =>
      dsimp [edge0, edge1]
      have hhit : HitsWithTop glob n b s (.hx i) (.z i) (.f i) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.hx i) (.z i) (.f i) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega
        · rw [hs_hx]; exact hitsWithTop_hy_z_of_ce_false_tau_false glob n b s hvalid i hce_hy htau
      exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid hhit (prio_f_odd n i)

/-! ### Part 6: `bestEdge` for `.z i` and `.u i` -/

lemma predVal_lt_of_top_even_gt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w₁ w₂ d : V_bin n)
    (hd : d ∈ predPath glob n b s w₂)
    (heven : (G_bin n).priority d % 2 = 0)
    (hmax₂ : ∀ u, (G_bin n).priority d < (G_bin n).priority u → u ∉ predPath glob n b s w₂)
    (hmax₁ : ∀ u, (G_bin n).priority d ≤ (G_bin n).priority u → u ∉ predPath glob n b s w₁) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := d)
  · exact hmax₁ d le_rfl
  · exact hd
  · exact heven
  · intro u hu
    exact ⟨fun h => False.elim (hmax₁ u (le_of_lt hu) h),
           fun h => False.elim (hmax₂ u hu h)⟩

lemma predVal_lt_of_top_odd_gt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w₁ w₂ d : V_bin n)
    (hd : d ∈ predPath glob n b s w₂)
    (hodd : (G_bin n).priority d % 2 = 1)
    (hmax₂ : ∀ u, (G_bin n).priority d < (G_bin n).priority u → u ∉ predPath glob n b s w₂)
    (hmax₁ : ∀ u, (G_bin n).priority d ≤ (G_bin n).priority u → u ∉ predPath glob n b s w₁) :
    ValueLT (G_bin n) (predVal glob n b s w₂) (predVal glob n b s w₁) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := d)
  · exact hd
  · exact hmax₁ d le_rfl
  · exact hodd
  · intro u hu
    exact ⟨fun h => False.elim (hmax₂ u hu h),
           fun h => False.elim (hmax₁ u (le_of_lt hu) h)⟩

lemma hitsWithTop_trans_of_lt (glob : Bool) (n b s : ℕ)
    (w p q d₁ d₂ : V_bin n)
    (h₁ : HitsWithTop glob n b s w p d₁)
    (h₂ : HitsWithTop glob n b s p q d₂)
    (hrank : predRank0 glob n b s q < predRank0 glob n b s p)
    (hd : (G_bin n).priority d₂ < (G_bin n).priority d₁) :
    HitsWithTop glob n b s w q d₁ := by
  refine ⟨lt_trans hrank h₁.1, h₁.2.1, ?_⟩
  intro u hu
  exact (h₁.2.2 u hu).trans (h₂.2.2 u (lt_trans hd hu))

private lemma exists_max_testBit_true_aux (n b : ℕ) :
    ∀ k (j₀ : Fin n), n - j₀.val ≤ k → b.testBit j₀.val = true →
      ∃ j : Fin n, j₀.val ≤ j.val ∧ b.testBit j.val = true ∧
        ∀ l : Fin n, j.val < l.val → b.testBit l.val = false
  | 0, j₀, hk, _ => by have := j₀.isLt; omega
  | k + 1, j₀, hk, hj₀ => by
    by_cases hex : ∃ m : Fin n, j₀.val < m.val ∧ b.testBit m.val = true
    · rcases hex with ⟨m, hm_gt, hm_bit⟩
      rcases exists_max_testBit_true_aux n b k m (by omega) hm_bit with ⟨j, hj_ge, hj_bit, hj_max⟩
      exact ⟨j, by omega, hj_bit, hj_max⟩
    · refine ⟨j₀, le_rfl, hj₀, ?_⟩
      intro l hl
      cases hbit : b.testBit l.val with
      | false => rfl
      | true => exact False.elim (hex ⟨l, hl, hbit⟩)

lemma exists_max_testBit_ge (n b : ℕ) (i : Fin n)
    (hex : ∃ j₀ : Fin n, i.val ≤ j₀.val ∧ b.testBit j₀.val = true) :
    ∃ j : Fin n, i.val ≤ j.val ∧ b.testBit j.val = true ∧
      ∀ l : Fin n, j.val < l.val → b.testBit l.val = false ∧ hasHigherOne0 b n l.val = false := by
  rcases hex with ⟨j₀, hj₀_ge, hj₀_bit⟩
  rcases exists_max_testBit_true_aux n b (n - j₀.val) j₀ le_rfl hj₀_bit with ⟨j, hj_ge, hj_bit, hj_max⟩
  refine ⟨j, by omega, hj_bit, ?_⟩
  intro l hl
  refine ⟨hj_max l hl, ?_⟩
  rw [← Bool.not_eq_true, hasHigherOne0_iff]
  rintro ⟨m, hm_gt, hm_lt, hm_bit⟩
  have hm_false := hj_max ⟨m, hm_lt⟩ (by dsimp; omega)
  exact Bool.false_ne_true (hm_false.symm.trans hm_bit)

lemma not_highMemU_of_gt_max (n b : ℕ) (i j : Fin n)
    (hmax : ∀ l : Fin n, j.val < l.val → b.testBit l.val = false ∧ hasHigherOne0 b n l.val = false)
    (u : V_bin n) (hu : (G_bin n).priority (.k j) < (G_bin n).priority u) :
    ¬highMemU n b i u := by
  have hu_gt_s : top_bin n + 10 < (G_bin n).priority u := by
    have : top_bin n + 10 < (G_bin n).priority (.k j) := by dsimp [G_bin, priority_bin]; omega
    omega
  rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, rfl | rfl | rfl⟩
  · have hjl : j.val < l.val := by dsimp [G_bin, priority_bin] at hu; omega
    rcases hmax l hjl with ⟨hb1, _⟩
    dsimp [highMemU]; rw [hb1]; rintro ⟨_, h⟩; exact Bool.false_ne_true h
  · have hjl : j.val < l.val := by dsimp [G_bin, priority_bin] at hu; omega
    rcases hmax l hjl with ⟨hb1, _⟩
    dsimp [highMemU]; rw [hb1]; rintro ⟨_, h⟩; exact Bool.false_ne_true h
  · have hjl : j.val < l.val := by dsimp [G_bin, priority_bin] at hu; omega
    rcases hmax l hjl with ⟨hb1, _⟩
    dsimp [highMemU]; rw [hb1]; rintro ⟨_, h⟩; exact Bool.false_ne_true h

lemma not_highMemF_of_gt_max (n b : ℕ) (i j : Fin n) (hij : i.val ≤ j.val)
    (hmax : ∀ l : Fin n, j.val < l.val → b.testBit l.val = false ∧ hasHigherOne0 b n l.val = false)
    (u : V_bin n) (hu : (G_bin n).priority (.k j) < (G_bin n).priority u) :
    ¬highMemF n b i u := by
  have hu_gt_s : top_bin n + 10 < (G_bin n).priority u := by
    have : top_bin n + 10 < (G_bin n).priority (.k j) := by dsimp [G_bin, priority_bin]; omega
    omega
  rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, rfl | rfl | rfl⟩
  · have hjl : j.val < l.val := by dsimp [G_bin, priority_bin] at hu; omega
    rcases hmax l hjl with ⟨hb1, _⟩
    dsimp [highMemF]; rw [hb1]
    rintro (rfl | ⟨_, h⟩)
    · omega
    · exact Bool.false_ne_true h
  · have hjl : j.val < l.val := by dsimp [G_bin, priority_bin] at hu; omega
    rcases hmax l hjl with ⟨hb1, _⟩
    dsimp [highMemF]; rw [hb1]
    rintro (rfl | ⟨_, h⟩)
    · omega
    · exact Bool.false_ne_true h
  · have hjl : j.val < l.val := by dsimp [G_bin, priority_bin] at hu; omega
    rcases hmax l hjl with ⟨hb1, _⟩
    dsimp [highMemF]; rw [hb1]
    rintro (rfl | ⟨_, h⟩)
    · omega
    · exact Bool.false_ne_true h

lemma exists_max_highMemF (n b : ℕ) (i : Fin n) :
    ∃ j : Fin n, i.val ≤ j.val ∧ highMemF n b i (.k j) ∧
      ∀ u, (G_bin n).priority (.k j) < (G_bin n).priority u → ¬highMemF n b i u := by
  by_cases hex : ∃ j₀ : Fin n, i.val ≤ j₀.val ∧ b.testBit j₀.val = true
  · rcases exists_max_testBit_ge n b i hex with ⟨j, hj_ge, hj_bit, hj_max⟩
    have hmem : highMemF n b i (.k j) := by
      by_cases heq : j = i
      · exact Or.inl heq
      · exact Or.inr ⟨by have : j.val ≠ i.val := fun h => heq (Fin.ext h); omega, hj_bit⟩
    refine ⟨j, hj_ge, hmem, ?_⟩
    exact not_highMemF_of_gt_max n b i j hj_ge hj_max
  · refine ⟨i, le_rfl, Or.inl rfl, ?_⟩
    apply not_highMemF_of_gt_max n b i i le_rfl
    intro l hl
    have hl_bit : b.testBit l.val = false := by
      cases hbit : b.testBit l.val with
      | false => rfl
      | true => exact False.elim (hex ⟨l, le_of_lt hl, hbit⟩)
    refine ⟨hl_bit, ?_⟩
    rw [← Bool.not_eq_true, hasHigherOne0_iff]
    rintro ⟨m, hm_gt, hm_lt, hm_bit⟩
    exact hex ⟨⟨m, hm_lt⟩, by dsimp; omega, hm_bit⟩

lemma mem_u_of_not_hasHigherOne0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hi1 : i.val + 1 < n) (hh : hasHigherOne0 b n i.val = false) :
    let m : Fin n := ⟨i.val + 1, hi1⟩
    if b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n then
      (.k m) ∈ predPath glob n b s (.u m) ∧
        ∀ u, (G_bin n).priority (.k m) < (G_bin n).priority u → u ∉ predPath glob n b s (.u m)
    else
      (.z m) ∈ predPath glob n b s (.u m) ∧
        ∀ u, (G_bin n).priority (.z m) < (G_bin n).priority u → u ∉ predPath glob n b s (.u m) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have hvalid' : ValidState n b s := ⟨hn, hbn, hs⟩
  dsimp only
  set m : Fin n := ⟨i.val + 1, hi1⟩
  have hbit_gt : ∀ l : Fin n, i.val < l.val → b.testBit l.val = false := by
    intro l hl
    cases hbit : b.testBit l.val with
    | false => rfl
    | true =>
      have hh' : hasHigherOne0 b n i.val = true := (hasHigherOne0_iff b n i.val).mpr ⟨l.val, hl, l.isLt, hbit⟩
      exact False.elim (Bool.false_ne_true (hh.symm.trans hh'))
  have hm_bit : b.testBit m.val = false := hbit_gt m (by dsimp [m]; omega)
  have hm_hh : hasHigherOne0 b n m.val = false := by
    rw [← Bool.not_eq_true, hasHigherOne0_iff]
    rintro ⟨l, hl_gt, hl_lt, hl_bit⟩
    have hl_false := hbit_gt ⟨l, hl_lt⟩ (by dsimp [m] at hl_gt ⊢; omega)
    exact Bool.false_ne_true (hl_false.symm.trans hl_bit)
  have howner_um : (G_bin n).owner (.u m) = false := by
    dsimp [G_bin, owner_bin, m]
  have hs_um : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u m) = .h m := by
    unfold step predState0; rw [if_pos howner_um]
    have hce_um : chooseEdge1 glob n b s (.u m) = false := by
      dsimp [chooseEdge1]
      by_cases h1 : m.val = 0 ∨ ¬(m.val + 1 < n)
      · rw [if_pos h1]
      · rw [if_neg h1, if_pos (Or.inr (by simp [hm_hh]))]
    rw [hce_um]; rfl
  have hs_zm : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z m) = .x := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl]
    have hce_zm : chooseEdge1 glob n b s (.z m) = false := by
      dsimp [chooseEdge1]; rw [hm_hh, Bool.and_false]
    rw [hce_zm]; rfl
  have hpath_zm : predPath glob n b s (.z m) = {.z m} := by
    rw [predPath, predVal, pred_path_step glob n b s hvalid' (.z m) (by nofun), hs_zm,
        pred_path_x glob n b s hvalid']
    rfl
  have hpath_um : predPath glob n b s (.u m) = insert (.u m) (predPath glob n b s (.h m)) := by
    rw [predPath, predVal, pred_path_step glob n b s hvalid' (.u m) (by nofun), hs_um]
  split_ifs with hcond
  · rcases hcond with ⟨hb_lt, hs_eq, hi_lt_k⟩
    have hm_le_k := lowestZero0_le_of_testBit_false hi1 hm_bit
    have hm_eq_k : m.val = lowestZero0 b n := by dsimp [m] at hm_le_k ⊢; omega
    have hce_hm : chooseEdge1 glob n b s (.h m) = false := by
      rw [chooseEdge1_h_eq]
      have : b < 2 ^ n - 1 ∧ m.val = lowestZero0 b n ∧ S_close0 n b + 3 ≤ s := ⟨hb_lt, hm_eq_k, by omega⟩
      rw [decide_eq_true this]; simp
    have hce_hxm : chooseEdge1 glob n b s (.hx m) = false := by
      rw [chooseEdge1_hx_eq]
      have : b < 2 ^ n - 1 ∧ m.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s := ⟨hb_lt, hm_eq_k, by omega⟩
      rw [decide_eq_true this]; simp
    have hce_hym : chooseEdge1 glob n b s (.hy m) = false := by
      rw [chooseEdge1_hy_eq]
      have : b < 2 ^ n - 1 ∧ m.val = lowestZero0 b n ∧ S_close0 n b + 1 ≤ s := ⟨hb_lt, hm_eq_k, by omega⟩
      rw [decide_eq_true this]; simp
    have htau_gm : chooseTauEdge1 n b s (.g m) = true := by
      dsimp [chooseTauEdge1]
      have : 3 * (n + 2 * m.val + 1) + 2 ≤ s := by unfold S_close0 at hs_eq; omega
      rw [decide_eq_true this]; simp
    have hs_hm : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h m) = .hx m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hm]; rfl
    have hs_hxm : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hxm]; rfl
    have hhit_hxm : HitsWithTop glob n b s (.hx m) (.z m) (.k m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid' (.hx m) (.z m) (.k m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := m.isLt; omega
      · rw [hs_hxm]; exact hitsWithTop_hy_z_of_ce_false_tau_true glob n b s hvalid' m hce_hym htau_gm
    have hhit_hm : HitsWithTop glob n b s (.h m) (.z m) (.k m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid' (.h m) (.z m) (.k m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := m.isLt; omega
      · rw [hs_hm]; exact hhit_hxm
    have hhit_um : HitsWithTop glob n b s (.u m) (.z m) (.k m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid' (.u m) (.z m) (.k m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := m.isLt; omega
      · rw [hs_um]; exact hhit_hm
    rcases hhit_um with ⟨_, hkm_mem, hkm_top⟩
    refine ⟨hkm_mem, ?_⟩
    intro u hu hmem
    have hu_in_zm := (hkm_top u hu).mp hmem
    rw [hpath_zm, Finset.mem_singleton] at hu_in_zm
    subst hu_in_zm
    dsimp [G_bin, priority_bin] at hu
    omega
  · have hce_hm : chooseEdge1 glob n b s (.h m) = true := by
      rw [chooseEdge1_h_eq]
      have hnot_lo : ¬(0 < b ∧ m.val < lowestOne0 b n ∧ m.val + s < hyLim0 b n s) := by
        rintro ⟨hb0, hm_lt_lo, _⟩
        have hlo_lt := lowestOne0_lt hb0 hbn
        have hlo_bit := testBit_lowestOne0 hb0 hbn
        have hlo_gt : i.val < lowestOne0 b n := by dsimp [m] at hm_lt_lo; omega
        have hlo_false := hbit_gt ⟨lowestOne0 b n, hlo_lt⟩ hlo_gt
        exact Bool.false_ne_true (hlo_false.symm.trans hlo_bit)
      have hnot_k : ¬(b < 2 ^ n - 1 ∧ m.val = lowestZero0 b n ∧ S_close0 n b + 3 ≤ s) := by
        rintro ⟨hb_lt, hm_eq_k, hs_ge⟩
        have hmax := maxStep0_of_lt hb_lt
        exact hcond ⟨hb_lt, by omega, by dsimp [m] at hm_eq_k; omega⟩
      rw [decide_eq_false hnot_lo, decide_eq_false hnot_k]
      simp [hm_bit]
    have hs_hm : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h m) = .z m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_hm]; rfl
    have hpath_hm : predPath glob n b s (.h m) = insert (.h m) {.z m} := by
      rw [predPath, predVal, pred_path_step glob n b s hvalid' (.h m) (by nofun), hs_hm]
      exact congrArg (insert (.h m)) hpath_zm
    rw [hpath_um, hpath_hm]
    refine ⟨by simp, ?_⟩
    intro u hu hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin] at hu; have := m.isLt; omega
    · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin] at hu; have := m.isLt; omega
    · omega

lemma bestEdge1_z_eq (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) (hi1 : i.val + 1 < n) :
    bestEdge1 n b s (.z i) =
      (hasHigherOne0 b n i.val || decide (b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n)) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  unfold bestEdge1 nextPair
  split_ifs with h1 h2
  · have hnot : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n) := by omega
    rw [decide_eq_false hnot, Bool.or_false]
    dsimp [chooseEdge1]; rw [decide_eq_true hi1, Bool.true_and]
  · rcases h2 with ⟨hb_lt, hs3⟩
    dsimp [chooseEdge1]; rw [decide_eq_true hi1, Bool.true_and]
    by_cases hlt : i.val < lowestZero0 b n
    · have hcond : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n := ⟨hb_lt, hs3, hlt⟩
      rw [decide_eq_true hcond, Bool.or_true, hasHigherOne0_add_one_of_lt hb_lt hlt]
    · have hcond : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n) := fun h => hlt h.2.2
      rw [decide_eq_false hcond, Bool.or_false, hasHigherOne0_add_one_of_ge hb_lt (by omega)]
  · have hnot : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n) :=
      fun ⟨hb_lt, hs3, _⟩ => h2 ⟨hb_lt, hs3⟩
    rw [decide_eq_false hnot, Bool.or_false]
    dsimp [chooseEdge1]; rw [decide_eq_true hi1, Bool.true_and]

theorem bestEdge_z (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    BestEdgeProp glob n b s (.z i) := by
  intro _ hne
  by_cases hi1 : i.val + 1 < n
  · unfold bestEdge worstEdge
    rw [bestEdge1_z_eq n b s hvalid i hi1]
    set m : Fin n := ⟨i.val + 1, hi1⟩
    have he0 : edge0 n (.z i) = .x := rfl
    have he1 : edge1 n (.z i) = .u m := by dsimp [edge1, m]; rw [dif_pos hi1]
    cases hh : hasHigherOne0 b n i.val with
    | true =>
      simp only [Bool.true_or]
      rw [he0, he1]
      rcases (hasHigherOne0_iff b n i.val).mp hh with ⟨j₀, hj₀_gt, hj₀_lt, hj₀_bit⟩
      have hex_m : ∃ l : Fin n, m.val ≤ l.val ∧ b.testBit l.val = true :=
        ⟨⟨j₀, hj₀_lt⟩, by dsimp [m]; omega, hj₀_bit⟩
      rcases exists_max_testBit_ge n b m hex_m with ⟨j, hj_ge, hj_bit, hj_max⟩
      have hm_cond : b.testBit m.val = true ∨ hasHigherOne0 b n m.val = true := by
        by_cases hmeq : m.val = j₀
        · left; rw [hmeq]; exact hj₀_bit
        · right; exact (hasHigherOne0_iff b n m.val).mpr ⟨j₀, by dsimp [m] at hmeq ⊢; omega, hj₀_lt, hj₀_bit⟩
      cases hstill : uStillH0 n b s m with
      | false =>
        have hmem_kj : (.k j) ∈ predPath glob n b s (.u m) := by
          have := (highMem_u glob n b s hvalid m (by dsimp [m]; omega) hm_cond hstill (.k j)
            (by dsimp [G_bin, priority_bin]; omega)).mpr ⟨hj_ge, hj_bit⟩
          exact this
        apply predVal_lt_of_top_even_gt glob n b s hvalid .x (.u m) (.k j) hmem_kj (prio_k_even n j)
        · intro u hu
          have hu_ge_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
            have : (G_bin n).priority .c < (G_bin n).priority (.k j) := by dsimp [G_bin, priority_bin]; omega
            omega
          rw [highMem_u glob n b s hvalid m (by dsimp [m]; omega) hm_cond hstill u hu_ge_c]
          exact not_highMemU_of_gt_max n b m j hj_max u hu
        · intro u _; rw [predPath, predVal, pred_path_x glob n b s hvalid]; exact Finset.notMem_empty u
      | true =>
        have hstill' : 0 < b ∧ m.val < lowestOne0 b n ∧ m.val + s < uLim0 b n := by
          unfold uStillH0 at hstill; exact of_decide_eq_true hstill
        rcases hstill' with ⟨hb0, hm_lt_lo, hm_lt_u⟩
        have hle_u_lo := uLim0_le_lowestOne0 b n
        have hlo_lt := lowestOne0_lt hb0 hvalid.2.1
        set m₀ : Fin n := ⟨uLim0 b n - 1 - s, by omega⟩
        have hhit_um : HitsWithTop glob n b s (.u m) (.g m₀) (.f m₀) :=
          hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ rfl (by dsimp [m₀]; omega)
            (m₀.val - m.val) m le_rfl (by dsimp [m]; omega) (by dsimp [m₀]; omega)
        have hm₀_lt_lo : m₀.val < lowestOne0 b n := by dsimp [m₀]; omega
        have hbit₀ : b.testBit m₀.val = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 hm₀_lt_lo
        have htau₀ : chooseTauEdge1 n b s (.g m₀) = false := by
          dsimp [chooseTauEdge1]
          simp only [hbit₀, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
          refine ⟨by dsimp [m₀]; omega, by dsimp [m₀]; omega⟩
        have hport_g := hitsPortal_g_of_tau_false glob n b s hvalid m₀ htau₀
        have hj_ge_lo : lowestOne0 b n ≤ j.val := lowestOne0_le_of_testBit_true j.isLt hj_bit
        have hprio_fm₀_kj : (G_bin n).priority (.f m₀) < (G_bin n).priority (.k j) := by
          dsimp [G_bin, priority_bin]; omega
        have hkj_g : (.k j) ∈ predPath glob n b s (.g m₀) := by
          rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g j
            (by unfold S_close0; omega) (.k j) (Or.inr (Or.inr rfl))]
          exact hj_bit
        have hkj_um : (.k j) ∈ predPath glob n b s (.u m) :=
          (hhit_um.2.2 (.k j) hprio_fm₀_kj).mpr hkj_g
        apply predVal_lt_of_top_even_gt glob n b s hvalid .x (.u m) (.k j) hkj_um (prio_k_even n j)
        · intro u hu
          rw [hhit_um.2.2 u (lt_trans hprio_fm₀_kj hu)]
          have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
            have : (G_bin n).priority .s < (G_bin n).priority (.k j) := by dsimp [G_bin, priority_bin]; omega
            omega
          rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, hu_eq⟩
          have hjl : j.val < l.val := by
            rcases hu_eq with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin] at hu; omega }
          rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g l (by unfold S_close0; omega) u hu_eq,
              (hj_max l hjl).1]
          exact Bool.false_ne_true
        · intro u _; rw [predPath, predVal, pred_path_x glob n b s hvalid]; exact Finset.notMem_empty u
    | false =>
      simp only [Bool.false_or]
      have hmem_um := mem_u_of_not_hasHigherOne0 glob n b s hvalid i hi1 hh
      dsimp only at hmem_um
      by_cases hcond : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n
      · rw [if_pos hcond] at hmem_um
        rw [decide_eq_true hcond, if_pos rfl, if_pos rfl, he0, he1]
        apply predVal_lt_of_top_even_gt glob n b s hvalid .x (.u m) (.k m) hmem_um.1 (prio_k_even n m) hmem_um.2
        intro u _; rw [predPath, predVal, pred_path_x glob n b s hvalid]; exact Finset.notMem_empty u
      · rw [if_neg hcond] at hmem_um
        rw [decide_eq_false hcond]
        dsimp
        rw [he0, he1]
        apply predVal_lt_of_top_odd_gt glob n b s hvalid .x (.u m) (.z m) hmem_um.1 (prio_z_odd n m) hmem_um.2
        intro u _; rw [predPath, predVal, pred_path_x glob n b s hvalid]; exact Finset.notMem_empty u
  · exfalso; apply hne; dsimp [edge0, edge1]; rw [dif_neg hi1]

lemma bestEdge1_u_of_hasHigherOne0_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hi0 : 1 ≤ i.val) (hi1 : i.val + 1 < n) (hh : hasHigherOne0 b n i.val = true) :
    bestEdge1 n b s (.u i) = (chooseEdge1 glob n b s (.h i) || !chooseTauEdge1 n b s (.g i)) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have hi := i.isLt
  have h1_neg : ¬(i.val = 0 ∨ ¬(i.val + 1 < n)) := by omega
  unfold bestEdge1 nextPair
  split_ifs with hc1 hc2
  · have hbit : b.testBit i.val = true := by
      rw [hc1.1]; exact testBit_two_pow_sub_one n i.val hi
    dsimp [chooseEdge1, chooseTauEdge1]
    rw [if_neg h1_neg, if_pos (Or.inl hbit), if_pos hbit, hbit]; rfl
  · rcases hc2 with ⟨hb_lt, hs3⟩
    dsimp [chooseEdge1]
    rw [if_neg h1_neg]
    by_cases hlt_k : i.val < lowestZero0 b n
    · have hbit : b.testBit i.val = true := testBit_of_lt_lowestZero0 hb_lt hlt_k
      have hbit1 : (b + 1).testBit i.val = false := testBit_add_one_of_lt_lowestZero0 hb_lt hlt_k
      have hh1 : hasHigherOne0 (b + 1) n i.val = true := hasHigherOne0_add_one_of_lt hb_lt hlt_k
      have h2_neg : ¬((b + 1).testBit i.val = true ∨ (!hasHigherOne0 (b + 1) n i.val) = true) := by
        simp [hbit1, hh1]
      have hlo1 := lowestOne0_add_one hb_lt
      have h3_pos : 0 < b + 1 ∧ i.val < lowestOne0 (b + 1) n := ⟨by omega, by omega⟩
      rw [if_neg h2_neg, if_pos h3_pos, if_pos hbit]
      dsimp [chooseTauEdge1]; rw [hbit]; simp only [Bool.true_or, Bool.not_true, Bool.false_or]
      rw [decide_eq_false_iff_not, not_not]
      unfold uLim0
      rw [topFlip0_add_one hb_lt, hlo1]
      by_cases hi1_lt_k : i.val + 1 < lowestZero0 b n
      · split_ifs <;> omega
      · have hi1_eq_k : i.val + 1 = lowestZero0 b n := by omega
        have hh_k : hasHigherOne0 b n (lowestZero0 b n) = true := by
          rcases (hasHigherOne0_iff b n i.val).mp hh with ⟨j, hj_gt, hj_lt, hj_bit⟩
          have hj_ne_k : j ≠ lowestZero0 b n := by
            intro heq; subst heq; exact Bool.false_ne_true ((testBit_lowestZero0 hb_lt).symm.trans hj_bit)
          exact (hasHigherOne0_iff b n (lowestZero0 b n)).mpr ⟨j, by omega, hj_lt, hj_bit⟩
        rw [hh_k]; simp; omega
    · by_cases heq_k : i.val = lowestZero0 b n
      · have hbit1 : (b + 1).testBit i.val = true := by
          rw [heq_k]; exact testBit_add_one_lowestZero0 hb_lt
        rw [if_pos (Or.inl hbit1)]
        have hbit : b.testBit i.val = false := by
          rw [heq_k]; exact testBit_lowestZero0 hb_lt
        have hnot_lo : ¬(0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s) := by
          rintro ⟨hb0, hi_lt_lo, _⟩
          have hbit0 := testBit_of_lt_lowestOne0 hb0 hbn (by omega : 0 < lowestOne0 b n)
          have hk0 := lowestZero0_le_of_testBit_false hn hbit0
          omega
        rw [if_neg (by simp [hbit]), if_neg hnot_lo, if_pos ⟨hb_lt, heq_k⟩]
        have hnot_lt3 : ¬(s < S_close0 n b + 3) := by omega
        rw [decide_eq_false hnot_lt3, Bool.false_or]
        dsimp [chooseTauEdge1]
        have hT : 3 * (n + 2 * i.val + 1) + 2 ≤ s := by unfold S_close0 at hs3; omega
        rw [decide_eq_true hT]; simp
      · have hgt_k : lowestZero0 b n < i.val := by omega
        have hbit1 : (b + 1).testBit i.val = b.testBit i.val := testBit_add_one_of_gt_lowestZero0 hb_lt hgt_k
        have hh1 : hasHigherOne0 (b + 1) n i.val = true := by
          rw [hasHigherOne0_add_one_of_ge hb_lt (by omega), hh]
        have hlo1 := lowestOne0_add_one hb_lt
        have h3_neg : ¬(0 < b + 1 ∧ i.val < lowestOne0 (b + 1) n) := by omega
        by_cases hbit : b.testBit i.val = true
        · rw [if_pos (Or.inl (by rw [hbit1, hbit])), if_pos hbit]
          dsimp [chooseTauEdge1]; rw [hbit]; simp
        · have hbit_f : b.testBit i.val = false := Bool.eq_false_iff.mpr hbit
          have h2_neg : ¬((b + 1).testBit i.val = true ∨ (!hasHigherOne0 (b + 1) n i.val) = true) := by
            simp [hbit1, hbit_f, hh1]
          rw [if_neg h2_neg, if_neg h3_neg, if_neg hbit]
          have hnot_lo : ¬(0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s) := by
            have := hyLim0_le_n b n s
            unfold S_close0 at hs3
            omega
          rw [if_neg hnot_lo, if_neg (fun h => heq_k h.2)]; simp
  · dsimp [chooseEdge1]
    rw [if_neg h1_neg]
    by_cases hbit : b.testBit i.val = true
    · rw [if_pos (Or.inl hbit), if_pos hbit]
      dsimp [chooseTauEdge1]; rw [hbit]; simp
    · have hbit_f : b.testBit i.val = false := Bool.eq_false_iff.mpr hbit
      have h2_neg : ¬(b.testBit i.val = true ∨ (!hasHigherOne0 b n i.val) = true) := by simp [hbit_f, hh]
      rw [if_neg h2_neg, if_neg hbit]
      have hb_lt : b < 2 ^ n - 1 := by
        by_contra hge
        have heq : b = 2 ^ n - 1 := by omega
        have hbit' : b.testBit i.val = true := by rw [heq]; exact testBit_two_pow_sub_one n i.val hi
        exact hbit hbit'
      have hs_lt : s < S_close0 n b + 3 := by
        have := maxStep0_of_lt hb_lt; omega
      by_cases hlo : 0 < b ∧ i.val < lowestOne0 b n
      · rw [if_pos hlo]
        have hbit0 : b.testBit 0 = false := testBit_of_lt_lowestOne0 hlo.1 hbn (by omega)
        have hk0 : lowestZero0 b n = 0 := by
          have := lowestZero0_le_of_testBit_false hn hbit0; omega
        have hnot_T : ¬(3 * (n + 2 * i.val + 1) + 2 ≤ s) := by
          unfold S_close0 at hs_lt; omega
        dsimp [chooseTauEdge1]
        rw [hbit_f, decide_eq_false hnot_T, Bool.false_or, Bool.false_or]
        have heq_u : (decide ¬(i.val + (s + 1) < uLim0 b n)) =
            (!decide (0 < b ∧ i.val < lowestOne0 b n ∧ i.val + 1 + s < uLim0 b n)) := by
          rw [← decide_not]
          congr 1
          exact propext ⟨fun h ⟨_, _, h'⟩ => h (by omega), fun h h' => h ⟨hlo.1, hlo.2, by omega⟩⟩
        rw [heq_u]
        apply bool_eq_or_of_imp
        intro hce_h
        by_cases hlo_hy : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s
        · rw [if_pos hlo_hy] at hce_h; cases hce_h
        · have hle_u_hy := uLim0_le_hyLim0 b n s
          rw [Bool.not_eq_true', decide_eq_false_iff_not]
          rintro ⟨_, _, hlt_u⟩
          exact hlo_hy ⟨hlo.1, hlo.2, by omega⟩
      · rw [if_neg hlo]
        have hnot_lo_hy : ¬(0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s) :=
          fun ⟨h1, h2, _⟩ => hlo ⟨h1, h2⟩
        rw [if_neg hnot_lo_hy]
        split_ifs with hk_eq
        · rw [decide_eq_true hs_lt, Bool.true_or]
        · rfl

lemma bestEdge1_u_of_hasHigherOne0_false (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hi0 : 1 ≤ i.val) (hi1 : i.val + 1 < n) (hh : hasHigherOne0 b n i.val = false) :
    bestEdge1 n b s (.u i) = decide (b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have hi := i.isLt
  have h1_neg : ¬(i.val = 0 ∨ ¬(i.val + 1 < n)) := by omega
  unfold bestEdge1 nextPair
  split_ifs with hc1 hc2
  · have hnot : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n) := by omega
    rw [decide_eq_false hnot]
    dsimp [chooseEdge1]
    rw [if_neg h1_neg, if_pos (Or.inr (by simp [hh]))]
  · rcases hc2 with ⟨hb_lt, hs3⟩
    dsimp [chooseEdge1]
    rw [if_neg h1_neg]
    by_cases hlt_k : i.val < lowestZero0 b n
    · have hcond : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n := ⟨hb_lt, hs3, hlt_k⟩
      rw [decide_eq_true hcond]
      have hbit1 : (b + 1).testBit i.val = false := testBit_add_one_of_lt_lowestZero0 hb_lt hlt_k
      have hh1 : hasHigherOne0 (b + 1) n i.val = true := hasHigherOne0_add_one_of_lt hb_lt hlt_k
      have h2_neg : ¬((b + 1).testBit i.val = true ∨ (!hasHigherOne0 (b + 1) n i.val) = true) := by
        simp [hbit1, hh1]
      have hlo1 := lowestOne0_add_one hb_lt
      have h3_pos : 0 < b + 1 ∧ i.val < lowestOne0 (b + 1) n := ⟨by omega, by omega⟩
      rw [if_neg h2_neg, if_pos h3_pos, decide_eq_true_eq]
      have hi1_eq_k : i.val + 1 = lowestZero0 b n := by
        by_contra hne
        have hi1_lt_k : i.val + 1 < lowestZero0 b n := by omega
        have hbit_i1 := testBit_of_lt_lowestZero0 hb_lt hi1_lt_k
        have hh' : hasHigherOne0 b n i.val = true :=
          (hasHigherOne0_iff b n i.val).mpr ⟨i.val + 1, by omega, hi1, hbit_i1⟩
        exact Bool.false_ne_true (hh.symm.trans hh')
      have hh_k : hasHigherOne0 b n (lowestZero0 b n) = false := by
        rw [← Bool.not_eq_true, hasHigherOne0_iff]
        rintro ⟨j, hj_gt, hj_lt, hj_bit⟩
        have hh' : hasHigherOne0 b n i.val = true :=
          (hasHigherOne0_iff b n i.val).mpr ⟨j, by omega, hj_lt, hj_bit⟩
        exact Bool.false_ne_true (hh.symm.trans hh')
      unfold uLim0
      rw [topFlip0_add_one hb_lt, hlo1, hh_k]
      simp; omega
    · have hcond : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n) := fun h => hlt_k h.2.2
      rw [decide_eq_false hcond]
      have hh1 : hasHigherOne0 (b + 1) n i.val = false := by
        rw [hasHigherOne0_add_one_of_ge hb_lt (by omega), hh]
      rw [if_pos (Or.inr (by simp [hh1]))]
  · have hnot : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n) :=
      fun ⟨hb_lt, hs3, _⟩ => hc2 ⟨hb_lt, hs3⟩
    rw [decide_eq_false hnot]
    dsimp [chooseEdge1]
    rw [if_neg h1_neg, if_pos (Or.inr (by simp [hh]))]

lemma not_mem_h_of_not_hasHigherOne0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hh : hasHigherOne0 b n i.val = false)
    (u : V_bin n) (hu : (G_bin n).priority (.k i) < (G_bin n).priority u) :
    u ∉ predPath glob n b s (.h i) := by
  have hs_zi : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z i) = .x := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl]
    have hce_zi : chooseEdge1 glob n b s (.z i) = false := by
      dsimp [chooseEdge1]; rw [hh, Bool.and_false]
    rw [hce_zi]; rfl
  have hpath_zi : predPath glob n b s (.z i) = {.z i} := by
    rw [predPath, predVal, pred_path_step glob n b s hvalid (.z i) (by nofun), hs_zi,
        pred_path_x glob n b s hvalid]
    rfl
  have hnot_zi : u ∉ predPath glob n b s (.z i) := by
    rw [hpath_zi, Finset.mem_singleton]
    intro rfl
    dsimp [G_bin, priority_bin] at hu
    omega
  have hu_ge_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    dsimp [G_bin, priority_bin] at hu ⊢; omega
  have hp_h : (G_bin n).priority (.h i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega
  have hp_hx : (G_bin n).priority (.hx i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega
  have hp_hy : (G_bin n).priority (.hy i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega
  rw [mem_path_step_high glob n b s hvalid (.h i) u (by nofun) hp_h hu_ge_c]
  cases hce_h : chooseEdge1 glob n b s (.h i) with
  | true =>
    have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h i) = .z i := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_h]; rfl
    rw [hs_h]; exact hnot_zi
  | false =>
    have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h i) = .hx i := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
    rw [hs_h, mem_path_step_high glob n b s hvalid (.hx i) u (by nofun) hp_hx hu_ge_c]
    cases hce_hx : chooseEdge1 glob n b s (.hx i) with
    | true =>
      have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx i) = .z i := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_hx]; rfl
      rw [hs_hx]; exact hnot_zi
    | false =>
      have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx i) = .hy i := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
      rw [hs_hx, mem_path_step_high glob n b s hvalid (.hy i) u (by nofun) hp_hy hu_ge_c]
      cases hce_hy : chooseEdge1 glob n b s (.hy i) with
      | true =>
        have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy i) = .z i := by
          unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_hy]; rfl
        rw [hs_hy]; exact hnot_zi
      | false =>
        have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy i) = .f i := by
          unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hy]; rfl
        rw [hs_hy]
        cases htau_g : chooseTauEdge1 n b s (.g i) with
        | true =>
          rw [(hitsWithTop_f_z_of_tau_true glob n b s hvalid i htau_g).2.2 u hu]
          exact hnot_zi
        | false =>
          rw [(hitsWithTop_f_z_of_tau_false glob n b s hvalid i htau_g).2.2 u
            (by dsimp [G_bin, priority_bin] at hu ⊢; omega)]
          exact hnot_zi

theorem bestEdge_u (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    BestEdgeProp glob n b s (.u i) := by
  intro _ hne
  by_cases hi : i.val ≠ 0 ∧ i.val + 1 < n
  · rcases hi with ⟨hi_ne0, hi1⟩
    have hi0 : 1 ≤ i.val := by omega
    set m : Fin n := ⟨i.val + 1, hi1⟩
    have he0 : edge0 n (.u i) = .h i := rfl
    have he1 : edge1 n (.u i) = .u m := by dsimp [edge1, m]; rw [dif_pos ⟨hi_ne0, hi1⟩]
    unfold bestEdge worstEdge
    cases hh : hasHigherOne0 b n i.val with
    | true =>
      rw [bestEdge1_u_of_hasHigherOne0_true glob n b s hvalid i hi0 hi1 hh]
      have hs_zi : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z i) = .u m := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl]
        have hce_zi : chooseEdge1 glob n b s (.z i) = true := by
          dsimp [chooseEdge1]; rw [decide_eq_true hi1, hh]; rfl
        rw [if_pos hce_zi]; dsimp [edge1, m]; rw [dif_pos hi1]
      have hhit_zi : HitsWithTop glob n b s (.z i) (.u m) (.z i) :=
        hitsWithTop_of_step_eq glob n b s hvalid (.z i) (.u m) (by nofun) hs_zi
      cases hce_h : chooseEdge1 glob n b s (.h i) with
      | true =>
        simp only [Bool.true_or, he0, he1]
        dsimp
        have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h i) = .z i := by
          unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_h]; rfl
        have hhit_h : HitsWithTop glob n b s (.h i) (.u m) (.z i) := by
          apply hitsWithTop_of_step_lt glob n b s hvalid (.h i) (.u m) (.z i) (by nofun)
          · dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega
          · rw [hs_h]; exact hhit_zi
        exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid hhit_h (prio_z_odd n i)
      | false =>
        simp only [Bool.false_or]
        have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h i) = .hx i := by
          unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
        have hce_hx : chooseEdge1 glob n b s (.hx i) = false := by
          dsimp [chooseEdge1] at hce_h ⊢
          split_ifs at hce_h ⊢ with h1 h2 h3
          · rfl
          · rfl
          · rw [decide_eq_false_iff_not] at hce_h ⊢; omega
        have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx i) = .hy i := by
          unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
        have hce_hy : chooseEdge1 glob n b s (.hy i) = false := by
          dsimp [chooseEdge1] at hce_hx ⊢
          split_ifs at hce_hx ⊢ with h1 h2 h3
          · rfl
          · rfl
          · rw [decide_eq_false_iff_not] at hce_hx ⊢; omega
        cases htau_g : chooseTauEdge1 n b s (.g i) with
        | true =>
          dsimp; rw [he0, he1]
          have hhit_hy := hitsWithTop_hy_z_of_ce_false_tau_true glob n b s hvalid i hce_hy htau_g
          have hhit_hx := hitsWithTop_of_step_lt glob n b s hvalid (.hx i) (.z i) (.k i) (by nofun)
            (by dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega)
            (by rw [hs_hx]; exact hhit_hy)
          have hhit_hz := hitsWithTop_of_step_lt glob n b s hvalid (.h i) (.z i) (.k i) (by nofun)
            (by dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega)
            (by rw [hs_h]; exact hhit_hx)
          have hhit_hu := hitsWithTop_trans_of_lt glob n b s (.h i) (.z i) (.u m) (.k i) (.z i)
            hhit_hz hhit_zi hhit_zi.1 (by dsimp [G_bin, priority_bin]; omega)
          exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid hhit_hu (prio_k_even n i)
        | false =>
          dsimp; rw [he0, he1]
          have hhit_hy := hitsWithTop_hy_z_of_ce_false_tau_false glob n b s hvalid i hce_hy htau_g
          have hhit_hx := hitsWithTop_of_step_lt glob n b s hvalid (.hx i) (.z i) (.f i) (by nofun)
            (by dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega)
            (by rw [hs_hx]; exact hhit_hy)
          have hhit_hz := hitsWithTop_of_step_lt glob n b s hvalid (.h i) (.z i) (.f i) (by nofun)
            (by dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := i.isLt; omega)
            (by rw [hs_h]; exact hhit_hx)
          have hhit_hu := hitsWithTop_trans_of_lt glob n b s (.h i) (.z i) (.u m) (.f i) (.z i)
            hhit_hz hhit_zi hhit_zi.1 (by dsimp [G_bin, priority_bin]; omega)
          exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid hhit_hu (prio_f_odd n i)
    | false =>
      rw [bestEdge1_u_of_hasHigherOne0_false n b s hvalid i hi0 hi1 hh]
      have hmem_um := mem_u_of_not_hasHigherOne0 glob n b s hvalid i hi1 hh
      dsimp only at hmem_um
      by_cases hcond : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 ∧ i.val < lowestZero0 b n
      · rw [if_pos hcond] at hmem_um
        rw [decide_eq_true hcond, if_pos rfl, if_pos rfl, he0, he1]
        apply predVal_lt_of_top_even_gt glob n b s hvalid (.h i) (.u m) (.k m) hmem_um.1 (prio_k_even n m) hmem_um.2
        intro u hu
        apply not_mem_h_of_not_hasHigherOne0 glob n b s hvalid i hh u
        dsimp [G_bin, priority_bin, m] at hu ⊢; omega
      · rw [if_neg hcond] at hmem_um
        rw [decide_eq_false hcond]
        dsimp; rw [he0, he1]
        apply predVal_lt_of_top_odd_gt glob n b s hvalid (.h i) (.u m) (.z m) hmem_um.1 (prio_z_odd n m) hmem_um.2
        intro u hu
        apply not_mem_h_of_not_hasHigherOne0 glob n b s hvalid i hh u
        dsimp [G_bin, priority_bin, m] at hu ⊢; omega
  · exfalso; apply hne; dsimp [edge0, edge1]; rw [dif_neg hi]

/-! ### Part 7: `bestEdge` for `.r`, `.s`, `.rp i`, and `.sp i` -/

lemma step_rp_zero (glob : Bool) (n b s : ℕ) (hn : 0 < n) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.rp ⟨0, hn⟩) = .f ⟨0, hn⟩ := by
  unfold step G_bin owner_bin predState0 chooseEdge1; simp [edge1]

lemma step_sp_zero (glob : Bool) (n b s : ℕ) (hn : 0 < n) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.sp ⟨0, hn⟩) = .hx ⟨0, hn⟩ := by
  unfold step G_bin owner_bin predState0 chooseEdge1; simp [edge1]

lemma step_rp_of_below (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hm0 : m.val ≠ 0) (hbelow : rActive0 n b s = true → m.val < rTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.rp m) =
      .rp ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  cases hact : rActive0 n b s with
  | true =>
    exact step_rp_of_ne_rTarg0 glob n b s m hm0 (by have := hbelow hact; omega)
  | false =>
    unfold rActive0 at hact; rw [decide_eq_false_iff_not] at hact
    have hnot1 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s) := fun h => hact (Or.inr h)
    have hnot2 : ¬(0 < b ∧ m.val = lowestOne0 b n) := fun h => hact (Or.inl h.1)
    have hce : chooseEdge1 glob n b s (.rp m) = true := by
      dsimp [chooseEdge1]; rw [if_neg hm0, if_neg hnot1, decide_eq_true hnot2]
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce]; simp [edge1, hm0]

lemma step_sp_of_below (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hm0 : m.val ≠ 0) (hbelow : sActive0 n b s = true → m.val < sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.sp m) =
      .sp ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  cases hact : sActive0 n b s with
  | true =>
    exact step_sp_of_ne_sTarg0 glob n b s m hm0 (by have := hbelow hact; omega)
  | false =>
    unfold sActive0 at hact; rw [decide_eq_false_iff_not] at hact
    have hnot1 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s) := fun h => hact (Or.inr h)
    have hnot2 : ¬(0 < b ∧ m.val = lowestOne0 b n) := fun h => hact (Or.inl h.1)
    have hce : chooseEdge1 glob n b s (.sp m) = true := by
      dsimp [chooseEdge1]; rw [if_neg hm0, if_neg hnot1, decide_eq_true hnot2]
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce]; simp [edge1, hm0]

lemma hitsWithTop_rp_of_f_zero (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {q d : V_bin n} (hf : HitsWithTop glob n b s (.f ⟨0, hvalid.1⟩) q d)
    (hd : 4 * n < (G_bin n).priority d) :
    ∀ k (m : Fin n), m.val ≤ k → (rActive0 n b s = true → m.val < rTarg0 n b s) →
      HitsWithTop glob n b s (.rp m) q d
  | 0, m, hk, _ => by
    have hm_eq : m = ⟨0, hvalid.1⟩ := Fin.ext (by dsimp; omega)
    subst hm_eq
    have hp : (G_bin n).priority (.rp ⟨0, hvalid.1⟩) = 2 := rfl
    apply hitsWithTop_of_step_lt glob n b s hvalid (.rp ⟨0, hvalid.1⟩) q d (by nofun)
      (by have := hvalid.1; omega)
    rw [step_rp_zero glob n b s hvalid.1]; exact hf
  | k + 1, m, hk, hbelow => by
    by_cases hm0 : m.val = 0
    · exact hitsWithTop_rp_of_f_zero glob n b s hvalid hf hd 0 m (by omega) hbelow
    · have hp : (G_bin n).priority (.rp m) = 2 * (m.val + 1) := rfl
      apply hitsWithTop_of_step_lt glob n b s hvalid (.rp m) q d (by nofun)
        (by have := m.isLt; omega)
      rw [step_rp_of_below glob n b s m hm0 hbelow]
      exact hitsWithTop_rp_of_f_zero glob n b s hvalid hf hd k ⟨m.val - 1, by have := m.isLt; omega⟩
        (by dsimp; omega) (fun h => by have := hbelow h; dsimp; omega)

lemma mem_rp_below_iff_f_zero (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    ∀ k (m : Fin n), m.val ≤ k → (rActive0 n b s = true → m.val < rTarg0 n b s) →
      ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
        (u ∈ predPath glob n b s (.rp m) ↔ u ∈ predPath glob n b s (.f ⟨0, hvalid.1⟩))
  | 0, m, hk, _, u, hu => by
    have hm_eq : m = ⟨0, hvalid.1⟩ := Fin.ext (by dsimp; omega)
    subst hm_eq
    rw [mem_path_step_high glob n b s hvalid (.rp ⟨0, hvalid.1⟩) u (by nofun)
      (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega) hu,
      step_rp_zero glob n b s hvalid.1]
  | k + 1, m, hk, hbelow, u, hu => by
    by_cases hm0 : m.val = 0
    · exact mem_rp_below_iff_f_zero glob n b s hvalid 0 m (by omega) hbelow u hu
    · rw [mem_path_step_high glob n b s hvalid (.rp m) u (by nofun)
        (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega) hu,
        step_rp_of_below glob n b s m hm0 hbelow]
      exact mem_rp_below_iff_f_zero glob n b s hvalid k ⟨m.val - 1, by have := m.isLt; omega⟩
        (by dsimp; omega) (fun h => by have := hbelow h; dsimp; omega) u hu

lemma hitsWithTop_sp_of_hx_zero (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {q d : V_bin n} (hhx : HitsWithTop glob n b s (.hx ⟨0, hvalid.1⟩) q d)
    (hd : 4 * n < (G_bin n).priority d) :
    ∀ k (m : Fin n), m.val ≤ k → (sActive0 n b s = true → m.val < sTarg0 n b s) →
      HitsWithTop glob n b s (.sp m) q d
  | 0, m, hk, _ => by
    have hm_eq : m = ⟨0, hvalid.1⟩ := Fin.ext (by dsimp; omega)
    subst hm_eq
    have hp : (G_bin n).priority (.sp ⟨0, hvalid.1⟩) = 2 * n + 2 := rfl
    apply hitsWithTop_of_step_lt glob n b s hvalid (.sp ⟨0, hvalid.1⟩) q d (by nofun)
      (by have := hvalid.1; omega)
    rw [step_sp_zero glob n b s hvalid.1]; exact hhx
  | k + 1, m, hk, hbelow => by
    by_cases hm0 : m.val = 0
    · exact hitsWithTop_sp_of_hx_zero glob n b s hvalid hhx hd 0 m (by omega) hbelow
    · have hp : (G_bin n).priority (.sp m) = 2 * n + 2 * (m.val + 1) := rfl
      apply hitsWithTop_of_step_lt glob n b s hvalid (.sp m) q d (by nofun)
        (by have := m.isLt; omega)
      rw [step_sp_of_below glob n b s m hm0 hbelow]
      exact hitsWithTop_sp_of_hx_zero glob n b s hvalid hhx hd k ⟨m.val - 1, by have := m.isLt; omega⟩
        (by dsimp; omega) (fun h => by have := hbelow h; dsimp; omega)

lemma mem_sp_below_iff_hx_zero (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    ∀ k (m : Fin n), m.val ≤ k → (sActive0 n b s = true → m.val < sTarg0 n b s) →
      ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
        (u ∈ predPath glob n b s (.sp m) ↔ u ∈ predPath glob n b s (.hx ⟨0, hvalid.1⟩))
  | 0, m, hk, _, u, hu => by
    have hm_eq : m = ⟨0, hvalid.1⟩ := Fin.ext (by dsimp; omega)
    subst hm_eq
    rw [mem_path_step_high glob n b s hvalid (.sp ⟨0, hvalid.1⟩) u (by nofun)
      (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega) hu,
      step_sp_zero glob n b s hvalid.1]
  | k + 1, m, hk, hbelow, u, hu => by
    by_cases hm0 : m.val = 0
    · exact mem_sp_below_iff_hx_zero glob n b s hvalid 0 m (by omega) hbelow u hu
    · rw [mem_path_step_high glob n b s hvalid (.sp m) u (by nofun)
        (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega) hu,
        step_sp_of_below glob n b s m hm0 hbelow]
      exact mem_sp_below_iff_hx_zero glob n b s hvalid k ⟨m.val - 1, by have := m.isLt; omega⟩
        (by dsimp; omega) (fun h => by have := hbelow h; dsimp; omega) u hu

lemma two_le_two_pow {n : ℕ} (hn : 0 < n) : 2 ≤ 2 ^ n := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k, rfl⟩
  rw [Nat.pow_succ]
  have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  omega

lemma bestEdge1_r_eq (n b s : ℕ) (hvalid : ValidState n b s) :
    bestEdge1 n b s .r = decide (0 < b ∨ (b < 2 ^ n - 1 ∧ S_close0 n b ≤ s)) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have h2pow := two_le_two_pow hn
  unfold bestEdge1 nextPair
  split_ifs with hc1 hc2
  · dsimp [chooseEdge1, rActive0]
    congr 1; exact propext ⟨fun _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩
  · rcases hc2 with ⟨hb_lt, hs3⟩
    dsimp [chooseEdge1, rActive0]
    congr 1; exact propext ⟨fun _ => Or.inr ⟨hb_lt, by omega⟩, fun _ => Or.inl (by omega)⟩
  · dsimp [chooseEdge1, rActive0]
    congr 1; exact propext ⟨fun h => h.elim Or.inl (fun ⟨h1, h2⟩ => Or.inr ⟨h1, by omega⟩),
      fun h => h.elim Or.inl (fun ⟨h1, h2⟩ => Or.inr ⟨h1, by omega⟩)⟩

lemma bestEdge1_s_eq (n b s : ℕ) (hvalid : ValidState n b s) :
    bestEdge1 n b s .s = decide (0 < b ∨ (b < 2 ^ n - 1 ∧ S_close0 n b + 2 ≤ s)) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have h2pow := two_le_two_pow hn
  unfold bestEdge1 nextPair
  split_ifs with hc1 hc2
  · dsimp [chooseEdge1, sActive0]
    congr 1; exact propext ⟨fun _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩
  · rcases hc2 with ⟨hb_lt, hs3⟩
    dsimp [chooseEdge1, sActive0]
    congr 1; exact propext ⟨fun _ => Or.inr ⟨hb_lt, by omega⟩, fun _ => Or.inl (by omega)⟩
  · dsimp [chooseEdge1, sActive0]
    congr 1; exact propext ⟨fun h => h.elim Or.inl (fun ⟨h1, h2⟩ => Or.inr ⟨h1, by omega⟩),
      fun h => h.elim Or.inl (fun ⟨h1, h2⟩ => Or.inr ⟨h1, by omega⟩)⟩

theorem bestEdge_r (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    BestEdgeProp glob n b s .r := by
  intro _ _
  have hn := hvalid.1
  have h2pow := two_le_two_pow hn
  set mMax : Fin n := ⟨n - 1, by omega⟩
  have he0 : edge0 n .r = .x := rfl
  have he1 : edge1 n .r = .rp mMax := by dsimp [edge1, mMax]; rw [dif_pos hn]
  unfold bestEdge worstEdge
  rw [bestEdge1_r_eq n b s hvalid]
  cases hract : rActive0 n b s with
  | true =>
    have hcond : 0 < b ∨ (b < 2 ^ n - 1 ∧ S_close0 n b ≤ s) := by
      unfold rActive0 at hract; rw [decide_eq_true_eq] at hract
      exact hract.elim Or.inl (fun ⟨h1, h2⟩ => Or.inr ⟨h1, by omega⟩)
    rw [decide_eq_true hcond]; dsimp; rw [he0, he1]
    set t : Fin n := ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hract⟩
    rcases exists_max_highMemF n b t with ⟨j, _, hkj_t, hj_max⟩
    have hmem_rp := highMem_rp_of_ge glob n b s hvalid hract n mMax
      (by dsimp [mMax]; omega) (by dsimp [mMax]; have := rTarg0_lt_of_rActive0' n b s hvalid.2.1 hract; omega)
    have hkj_rp : (.k j) ∈ predPath glob n b s (.rp mMax) :=
      (hmem_rp (.k j) (by dsimp [G_bin, priority_bin]; omega)).mpr hkj_t
    apply predVal_lt_of_top_even_gt glob n b s hvalid .x (.rp mMax) (.k j) hkj_rp (prio_k_even n j)
    · intro u hu
      have hu_ge_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
        have : (G_bin n).priority .c < (G_bin n).priority (.k j) := by dsimp [G_bin, priority_bin]; omega
        omega
      rw [hmem_rp u hu_ge_c]
      exact hj_max u hu
    · intro u _; rw [predPath, predVal, pred_path_x glob n b s hvalid]; exact Finset.notMem_empty u
  | false =>
    have hract' : ¬(0 < b ∨ (b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s)) := by
      unfold rActive0 at hract; rwa [decide_eq_false_iff_not] at hract
    have hb0 : b = 0 := by omega
    subst hb0
    have hb_lt : 0 < 2 ^ n - 1 := by omega
    have hs_le : s ≤ S_close0 n 0 := by omega
    set z0 : Fin n := ⟨0, hn⟩
    have hk0 : lowestZero0 0 n = 0 := by
      have := lowestZero0_le_of_testBit_false hn (Nat.zero_testBit 0); omega
    have hh0 : hasHigherOne0 0 n 0 = false := by
      rw [← Bool.not_eq_true, hasHigherOne0_iff]
      rintro ⟨l, _, _, hbit⟩
      rw [Nat.zero_testBit] at hbit; exact Bool.false_ne_true hbit
    have hs_z0 : step (G_bin n) (predState0 glob n 0 s) (predTau0 n 0 s) (.z z0) = .x := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl]
      have hce : chooseEdge1 glob n 0 s (.z z0) = false := by
        dsimp [chooseEdge1, z0]; rw [hh0, Bool.and_false]
      rw [hce]; rfl
    have hpath_z0 : predPath glob n 0 s (.z z0) = {.z z0} := by
      rw [predPath, predVal, pred_path_step glob n 0 s hvalid (.z z0) (by nofun), hs_z0,
          pred_path_x glob n 0 s hvalid]
      rfl
    by_cases hs_eq : s = S_close0 n 0
    · have hcond : 0 < 0 ∨ (0 < 2 ^ n - 1 ∧ S_close0 n 0 ≤ s) := Or.inr ⟨hb_lt, by omega⟩
      rw [decide_eq_true hcond]; dsimp; rw [he0, he1]
      have htau0 : chooseTauEdge1 n 0 s (.g z0) = true := by
        dsimp [chooseTauEdge1, z0]
        have : 3 * (n + 2 * 0 + 1) + 2 ≤ s := by unfold S_close0 at hs_eq; omega
        rw [decide_eq_true this]; simp
      have hhit_f0 := hitsWithTop_f_z_of_tau_true glob n 0 s hvalid z0 htau0
      have hhit_rp := hitsWithTop_rp_of_f_zero glob n 0 s hvalid hhit_f0
        (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega)
        n mMax (by dsimp [mMax]; omega) (by rw [hract]; intro h; cases h)
      apply predVal_lt_of_top_even_gt glob n 0 s hvalid .x (.rp mMax) (.k z0) hhit_rp.2.1 (prio_k_even n z0)
      · intro u hu hmem
        have hu_z0 := (hhit_rp.2.2 u hu).mp hmem
        rw [hpath_z0, Finset.mem_singleton] at hu_z0
        subst hu_z0; dsimp [G_bin, priority_bin] at hu; omega
      · intro u _; rw [predPath, predVal, pred_path_x glob n 0 s hvalid]; exact Finset.notMem_empty u
    · have hcond : ¬(0 < 0 ∨ (0 < 2 ^ n - 1 ∧ S_close0 n 0 ≤ s)) := by omega
      rw [decide_eq_false hcond]; dsimp; rw [he0, he1]
      have htau0 : chooseTauEdge1 n 0 s (.g z0) = false := by
        dsimp [chooseTauEdge1, z0]
        rw [Nat.zero_testBit]
        have hnot_T : ¬(3 * (n + 2 * 0 + 1) + 2 ≤ s) := by unfold S_close0 at hs_le hs_eq; omega
        have hnot_u : ¬(0 < 0 ∧ 0 < lowestOne0 0 n ∧ 0 + 1 + s < uLim0 0 n) := by omega
        rw [decide_eq_false hnot_T, decide_eq_false hnot_u]; rfl
      have hport_g0 := hitsPortal_g_of_tau_false glob n 0 s hvalid z0 htau0
      have hs_f0 : step (G_bin n) (predState0 glob n 0 s) (predTau0 n 0 s) (.f z0) = .g z0 := rfl
      have hhit_f0 := hitsWithTop_of_step_eq glob n 0 s hvalid (.f z0) (.g z0) (by nofun) hs_f0
      have hhit_rp := hitsWithTop_rp_of_f_zero glob n 0 s hvalid hhit_f0
        (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega)
        n mMax (by dsimp [mMax]; omega) (by rw [hract]; intro h; cases h)
      have hsact : sActive0 n 0 s = false := by
        unfold sActive0; rw [decide_eq_false_iff_not]; omega
      apply predVal_lt_of_top_odd_gt glob n 0 s hvalid .x (.rp mMax) (.f z0) hhit_rp.2.1 (prio_f_odd n z0)
      · intro u hu hmem
        have hu_g0 := (hhit_rp.2.2 u hu).mp hmem
        have hu_ge_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
          dsimp [G_bin, priority_bin] at hu ⊢; omega
        rcases hport_g0 with hpc | hpr
        · have hu_c := (hpc.2 u hu_ge_c).mp hu_g0
          rw [highMem_c_of_false glob n 0 s hvalid hsact] at hu_c
          rcases hu_c with rfl | rfl <;> { dsimp [G_bin, priority_bin] at hu; omega }
        · have hu_r := (hpr.2 u hu_ge_c).mp hu_g0
          rw [highMem_r_of_false glob n 0 s hvalid hract] at hu_r
          subst hu_r; dsimp [G_bin, priority_bin] at hu; omega
      · intro u _; rw [predPath, predVal, pred_path_x glob n 0 s hvalid]; exact Finset.notMem_empty u

theorem bestEdge_s (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    BestEdgeProp glob n b s .s := by
  intro _ _
  have hn := hvalid.1
  have h2pow := two_le_two_pow hn
  set mMax : Fin n := ⟨n - 1, by omega⟩
  have he0 : edge0 n .s = .x := rfl
  have he1 : edge1 n .s = .sp mMax := by dsimp [edge1, mMax]; rw [dif_pos hn]
  unfold bestEdge worstEdge
  rw [bestEdge1_s_eq n b s hvalid]
  cases hsact : sActive0 n b s with
  | true =>
    have hcond : 0 < b ∨ (b < 2 ^ n - 1 ∧ S_close0 n b + 2 ≤ s) := by
      unfold sActive0 at hsact; rw [decide_eq_true_eq] at hsact
      exact hsact.elim Or.inl (fun ⟨h1, h2⟩ => Or.inr ⟨h1, by omega⟩)
    rw [decide_eq_true hcond]; dsimp; rw [he0, he1]
    set t : Fin n := ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hsact⟩
    rcases exists_max_highMemF n b t with ⟨j, _, hkj_t, hj_max⟩
    have hmem_sp := highMem_sp_of_ge glob n b s hvalid hsact n mMax
      (by dsimp [mMax]; omega) (by dsimp [mMax]; have := sTarg0_lt_of_sActive0' n b s hvalid.2.1 hsact; omega)
    have hkj_sp : (.k j) ∈ predPath glob n b s (.sp mMax) :=
      (hmem_sp (.k j) (by dsimp [G_bin, priority_bin]; omega)).mpr hkj_t
    apply predVal_lt_of_top_even_gt glob n b s hvalid .x (.sp mMax) (.k j) hkj_sp (prio_k_even n j)
    · intro u hu
      have hu_ge_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
        have : (G_bin n).priority .c < (G_bin n).priority (.k j) := by dsimp [G_bin, priority_bin]; omega
        omega
      rw [hmem_sp u hu_ge_c]
      exact hj_max u hu
    · intro u _; rw [predPath, predVal, pred_path_x glob n b s hvalid]; exact Finset.notMem_empty u
  | false =>
    have hsact' : ¬(0 < b ∨ (b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s)) := by
      unfold sActive0 at hsact; rwa [decide_eq_false_iff_not] at hsact
    have hb0 : b = 0 := by omega
    subst hb0
    have hb_lt : 0 < 2 ^ n - 1 := by omega
    have hs_le : s ≤ S_close0 n 0 + 2 := by omega
    set z0 : Fin n := ⟨0, hn⟩
    have hk0 : lowestZero0 0 n = 0 := by
      have := lowestZero0_le_of_testBit_false hn (Nat.zero_testBit 0); omega
    have hh0 : hasHigherOne0 0 n 0 = false := by
      rw [← Bool.not_eq_true, hasHigherOne0_iff]
      rintro ⟨l, _, _, hbit⟩
      rw [Nat.zero_testBit] at hbit; exact Bool.false_ne_true hbit
    have hs_z0 : step (G_bin n) (predState0 glob n 0 s) (predTau0 n 0 s) (.z z0) = .x := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl]
      have hce : chooseEdge1 glob n 0 s (.z z0) = false := by
        dsimp [chooseEdge1, z0]; rw [hh0, Bool.and_false]
      rw [hce]; rfl
    have hpath_z0 : predPath glob n 0 s (.z z0) = {.z z0} := by
      rw [predPath, predVal, pred_path_step glob n 0 s hvalid (.z z0) (by nofun), hs_z0,
          pred_path_x glob n 0 s hvalid]
      rfl
    by_cases hs_eq : s = S_close0 n 0 + 2
    · have hcond : 0 < 0 ∨ (0 < 2 ^ n - 1 ∧ S_close0 n 0 + 2 ≤ s) := Or.inr ⟨hb_lt, by omega⟩
      rw [decide_eq_true hcond]; dsimp; rw [he0, he1]
      have hce_hx0 : chooseEdge1 glob n 0 s (.hx z0) = false := by
        rw [chooseEdge1_hx_eq]
        have : 0 < 2 ^ n - 1 ∧ z0.val = lowestZero0 0 n ∧ S_close0 n 0 + 2 ≤ s :=
          ⟨hb_lt, by dsimp [z0]; omega, by omega⟩
        rw [decide_eq_true this]; simp
      have hce_hy0 : chooseEdge1 glob n 0 s (.hy z0) = false := by
        rw [chooseEdge1_hy_eq]
        have : 0 < 2 ^ n - 1 ∧ z0.val = lowestZero0 0 n ∧ S_close0 n 0 + 1 ≤ s :=
          ⟨hb_lt, by dsimp [z0]; omega, by omega⟩
        rw [decide_eq_true this]; simp
      have htau0 : chooseTauEdge1 n 0 s (.g z0) = true := by
        dsimp [chooseTauEdge1, z0]
        have : 3 * (n + 2 * 0 + 1) + 2 ≤ s := by unfold S_close0 at hs_eq; omega
        rw [decide_eq_true this]; simp
      have hs_hx0 : step (G_bin n) (predState0 glob n 0 s) (predTau0 n 0 s) (.hx z0) = .hy z0 := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx0]; rfl
      have hhit_hy0 := hitsWithTop_hy_z_of_ce_false_tau_true glob n 0 s hvalid z0 hce_hy0 htau0
      have hhit_hx0 := hitsWithTop_of_step_lt glob n 0 s hvalid (.hx z0) (.z z0) (.k z0) (by nofun)
        (by dsimp [G_bin, priority_bin, top_bin, shift_bin, M_bin]; have := z0.isLt; omega)
        (by rw [hs_hx0]; exact hhit_hy0)
      have hhit_sp := hitsWithTop_sp_of_hx_zero glob n 0 s hvalid hhit_hx0
        (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega)
        n mMax (by dsimp [mMax]; omega) (by rw [hsact]; intro h; cases h)
      apply predVal_lt_of_top_even_gt glob n 0 s hvalid .x (.sp mMax) (.k z0) hhit_sp.2.1 (prio_k_even n z0)
      · intro u hu hmem
        have hu_z0 := (hhit_sp.2.2 u hu).mp hmem
        rw [hpath_z0, Finset.mem_singleton] at hu_z0
        subst hu_z0; dsimp [G_bin, priority_bin] at hu; omega
      · intro u _; rw [predPath, predVal, pred_path_x glob n 0 s hvalid]; exact Finset.notMem_empty u
    · have hcond : ¬(0 < 0 ∨ (0 < 2 ^ n - 1 ∧ S_close0 n 0 + 2 ≤ s)) := by omega
      rw [decide_eq_false hcond]; dsimp; rw [he0, he1]
      have hce_hx0 : chooseEdge1 glob n 0 s (.hx z0) = true := by
        rw [chooseEdge1_hx_eq]
        have h1 : (0 : ℕ).testBit z0.val = false := Nat.zero_testBit 0
        have h2 : ¬(0 < 0 ∧ z0.val < lowestOne0 0 n ∧ z0.val + s < hyLim0 0 n s) := by omega
        have h3 : ¬(0 < 2 ^ n - 1 ∧ z0.val = lowestZero0 0 n ∧ S_close0 n 0 + 2 ≤ s) := by omega
        rw [h1, decide_eq_false h2, decide_eq_false h3]; rfl
      have hs_hx0 : step (G_bin n) (predState0 glob n 0 s) (predTau0 n 0 s) (.hx z0) = .z z0 := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_hx0]; rfl
      have hhit_hx0 := hitsWithTop_of_step_eq glob n 0 s hvalid (.hx z0) (.z z0) (by nofun) hs_hx0
      have hhit_sp := hitsWithTop_sp_of_hx_zero glob n 0 s hvalid hhit_hx0
        (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega)
        n mMax (by dsimp [mMax]; omega) (by rw [hsact]; intro h; cases h)
      have hp_hx_z : (G_bin n).priority (.hx z0) < (G_bin n).priority (.z z0) := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hz0_sp : (.z z0) ∈ predPath glob n 0 s (.sp mMax) := by
        rw [hhit_sp.2.2 (.z z0) hp_hx_z, hpath_z0]
        exact Finset.mem_singleton_self _
      apply predVal_lt_of_top_odd_gt glob n 0 s hvalid .x (.sp mMax) (.z z0) hz0_sp (prio_z_odd n z0)
      · intro u hu hmem
        have hu_z0 := (hhit_sp.2.2 u (lt_trans hp_hx_z hu)).mp hmem
        rw [hpath_z0, Finset.mem_singleton] at hu_z0
        subst hu_z0; omega
      · intro u _; rw [predPath, predVal, pred_path_x glob n 0 s hvalid]; exact Finset.notMem_empty u

lemma predVal_lt_of_highMemF_lt_of_testBit_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (t i : Fin n) (hti : t.val < i.val) (hbit : b.testBit i.val = false)
    (w₁ w₂ : V_bin n)
    (hw₁ : ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
      (u ∈ predPath glob n b s w₁ ↔ highMemF n b t u))
    (hw₂ : ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
      (u ∈ predPath glob n b s w₂ ↔ highMemF n b i u)) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := .k i)
  · rw [hw₁ (.k i) (by dsimp [G_bin, priority_bin]; omega)]
    dsimp [highMemF]
    rintro (rfl | ⟨_, h⟩)
    · omega
    · exact Bool.false_ne_true (hbit.symm.trans h)
  · rw [hw₂ (.k i) (by dsimp [G_bin, priority_bin]; omega)]
    exact Or.inl rfl
  · exact prio_k_even n i
  · intro u hu
    have hu_ge_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
      have : (G_bin n).priority .c < (G_bin n).priority (.k i) := by dsimp [G_bin, priority_bin]; omega
      omega
    rw [hw₁ u hu_ge_c, hw₂ u hu_ge_c]
    have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
      have : (G_bin n).priority .s < (G_bin n).priority (.k i) := by dsimp [G_bin, priority_bin]; omega
      omega
    rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, rfl | rfl | rfl⟩ <;>
    { have hil : i.val < l.val := by dsimp [G_bin, priority_bin] at hu; omega
      have hne_t : l ≠ t := fun h => by subst h; omega
      have hne_i : l ≠ i := fun h => by subst h; omega
      dsimp [highMemF]
      simp [hne_t, hne_i, hil, show t.val < l.val by omega] }

private lemma exists_max_highMemF_lt_aux (n b : ℕ) (t i : Fin n) :
    ∀ k (j₀ : Fin n), i.val - j₀.val ≤ k → t.val ≤ j₀.val → j₀.val < i.val →
      highMemF n b t (.k j₀) →
      ∃ j : Fin n, t.val ≤ j.val ∧ j.val < i.val ∧ highMemF n b t (.k j) ∧
        ∀ l : Fin n, j.val < l.val → l.val < i.val → b.testBit l.val = false
  | 0, j₀, hk, _, hj₀_lt, _ => by omega
  | k + 1, j₀, hk, hj₀_ge, hj₀_lt, hj₀_mem => by
    by_cases hex : ∃ m : Fin n, j₀.val < m.val ∧ m.val < i.val ∧ b.testBit m.val = true
    · rcases hex with ⟨m, hm_gt, hm_lt, hm_bit⟩
      have hm_mem : highMemF n b t (.k m) := Or.inr ⟨by omega, hm_bit⟩
      exact exists_max_highMemF_lt_aux n b t i k m (by omega) (by omega) hm_lt hm_mem
    · refine ⟨j₀, hj₀_ge, hj₀_lt, hj₀_mem, ?_⟩
      intro l hl_gt hl_lt
      cases hbit : b.testBit l.val with
      | false => rfl
      | true => exact False.elim (hex ⟨l, hl_gt, hl_lt, hbit⟩)

lemma predVal_lt_of_highMemF_lt_of_testBit_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (t i : Fin n) (hti : t.val < i.val) (hbit : b.testBit i.val = true)
    (w₁ w₂ : V_bin n)
    (hw₁ : ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
      (u ∈ predPath glob n b s w₁ ↔ highMemF n b i u))
    (hw₂ : ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
      (u ∈ predPath glob n b s w₂ ↔ highMemF n b t u)) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  rcases exists_max_highMemF_lt_aux n b t i (i.val - t.val) t le_rfl le_rfl hti (Or.inl rfl) with
    ⟨j, hj_ge, hj_lt, hkj_t, hj_max⟩
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := .k j)
  · rw [hw₁ (.k j) (by dsimp [G_bin, priority_bin]; omega)]
    dsimp [highMemF]
    rintro (rfl | ⟨h, _⟩) <;> omega
  · rw [hw₂ (.k j) (by dsimp [G_bin, priority_bin]; omega)]
    exact hkj_t
  · exact prio_k_even n j
  · intro u hu
    have hu_ge_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
      have : (G_bin n).priority .c < (G_bin n).priority (.k j) := by dsimp [G_bin, priority_bin]; omega
      omega
    rw [hw₁ u hu_ge_c, hw₂ u hu_ge_c]
    have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
      have : (G_bin n).priority .s < (G_bin n).priority (.k j) := by dsimp [G_bin, priority_bin]; omega
      omega
    rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, rfl | rfl | rfl⟩ <;>
    { have hjl : j.val < l.val := by dsimp [G_bin, priority_bin] at hu; omega
      have hne_t : l ≠ t := fun h => by subst h; omega
      dsimp [highMemF]
      by_cases hli : l.val < i.val
      · have hne_i : l ≠ i := fun h => by subst h; omega
        have hl_bit := hj_max l hjl hli
        simp [hne_t, hne_i, hl_bit, show ¬(i.val < l.val) by omega]
      · by_cases heq_i : l.val = i.val
        · have hfin : l = i := Fin.ext heq_i
          subst hfin
          simp [hti, hbit]
        · have hgt_i : i.val < l.val := by omega
          have hne_i : l ≠ i := fun h => by subst h; omega
          simp [hne_t, hne_i, hgt_i, show t.val < l.val by omega] }

lemma hitsWithTop_of_step_right (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w p q topV : V_bin n) (hp : p ≠ .x)
    (h : HitsWithTop glob n b s w p topV)
    (hs : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) p = q)
    (hprio : (G_bin n).priority p < (G_bin n).priority topV) :
    HitsWithTop glob n b s w q topV := by
  have hr := predRank0_step_lt glob n b s hvalid p hp
  rw [hs] at hr
  have hpath : predPath glob n b s p = insert p (predPath glob n b s q) := by
    rw [predPath, predVal, pred_path_step glob n b s hvalid p hp, hs]
  refine ⟨lt_trans hr h.1, h.2.1, ?_⟩
  intro u hu
  rw [h.2.2 u hu, hpath, Finset.mem_insert]
  have hne : u ≠ p := by intro rfl; omega
  simp [hne]

lemma hitsWithTop_f_step_u_of_still (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hb0 : 0 < b) (j : Fin n) (hj1 : j.val + 1 < n)
    (hj_lo : j.val + 1 < lowestOne0 b n) (hj_u : (j.val + 1) + s < uLim0 b n) :
    HitsWithTop glob n b s (.f j) (.u ⟨j.val + 1, hj1⟩) (.k j) := by
  have htau : chooseTauEdge1 n b s (.g j) = true := by
    dsimp [chooseTauEdge1]
    have hcond : 0 < b ∧ j.val < lowestOne0 b n ∧ j.val + 1 + s < uLim0 b n :=
      ⟨hb0, by omega, by omega⟩
    rw [decide_eq_true hcond]; simp
  have hhit_fz := hitsWithTop_f_z_of_tau_true glob n b s hvalid j htau
  have hh_j : hasHigherOne0 b n j.val = true := by
    rw [hasHigherOne0_iff]
    exact ⟨lowestOne0 b n, by omega, lowestOne0_lt hb0 hvalid.2.1, testBit_lowestOne0 hb0 hvalid.2.1⟩
  have hs_zj : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z j) = .u ⟨j.val + 1, hj1⟩ := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl]
    have hce_zj : chooseEdge1 glob n b s (.z j) = true := by
      dsimp [chooseEdge1]; rw [decide_eq_true hj1, hh_j]; rfl
    rw [if_pos hce_zj]; dsimp [edge1]; rw [dif_pos hj1]
  exact hitsWithTop_of_step_right glob n b s hvalid (.f j) (.z j) (.u ⟨j.val + 1, hj1⟩) (.k j)
    (by nofun) hhit_fz hs_zj (by dsimp [G_bin, priority_bin]; omega)

lemma chooseEdge1_u_of_still (glob : Bool) (n b s : ℕ) (hb0 : 0 < b) (m : Fin n)
    (hlo : m.val < lowestOne0 b n) (hu : m.val + s < uLim0 b n) :
    chooseEdge1 glob n b s (.u m) = false := by
  dsimp [chooseEdge1]
  split_ifs with hc1 hc2 hc3
  · rfl
  · rfl
  · rw [decide_eq_false_iff_not, not_not]; exact hu
  · exfalso; exact hc3 ⟨hb0, hlo⟩

lemma hitsWithTop_f_to_u_of_still (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hb0 : 0 < b) (i : Fin n) (hi0 : 0 < i.val)
    (hi_lo : i.val < lowestOne0 b n) (hi_u : i.val + s < uLim0 b n) :
    ∀ k (j : Fin n), i.val - 1 - j.val ≤ k → j.val < i.val →
      HitsWithTop glob n b s (.f j) (.u i) (.k ⟨i.val - 1, by have := i.isLt; omega⟩)
  | 0, j, hk, hj_lt => by
    have hj_eq : j = ⟨i.val - 1, by have := i.isLt; omega⟩ := Fin.ext (by dsimp; omega)
    rw [hj_eq]
    have hj1 : (i.val - 1) + 1 < n := by have := i.isLt; omega
    have hhit := hitsWithTop_f_step_u_of_still glob n b s hvalid hb0
      ⟨i.val - 1, by have := i.isLt; omega⟩ hj1 (by dsimp; omega) (by dsimp; omega)
    have hu_eq : (⟨(i.val - 1) + 1, hj1⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
    rwa [hu_eq] at hhit
  | k + 1, j, hk, hj_lt => by
    by_cases hj_eq : j.val = i.val - 1
    · exact hitsWithTop_f_to_u_of_still glob n b s hvalid hb0 i hi0 hi_lo hi_u 0 j (by omega) hj_lt
    · have hj1_lt : j.val + 1 < i.val := by omega
      have hj1_n : j.val + 1 < n := by have := i.isLt; omega
      set j1 : Fin n := ⟨j.val + 1, hj1_n⟩
      have ih := hitsWithTop_f_to_u_of_still glob n b s hvalid hb0 i hi0 hi_lo hi_u k j1
        (by dsimp [j1]; omega) hj1_lt
      have hle_hy := uLim0_le_hyLim0 b n s
      have hlt_hy : j1.val + s < hyLim0 b n s := by dsimp [j1]; omega
      have howner_u : (G_bin n).owner (.u j1) = false := by dsimp [G_bin, owner_bin, j1]
      have hce_u : chooseEdge1 glob n b s (.u j1) = false :=
        chooseEdge1_u_of_still glob n b s hb0 j1 (by dsimp [j1]; omega) (by dsimp [j1]; omega)
      have hs_u : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u j1) = .h j1 := by
        unfold step predState0; rw [if_pos howner_u, hce_u]; rfl
      have hce_h : chooseEdge1 glob n b s (.h j1) = false := by
        rw [chooseEdge1_h_eq]
        have : 0 < b ∧ j1.val < lowestOne0 b n ∧ j1.val + s < hyLim0 b n s :=
          ⟨hb0, by dsimp [j1]; omega, hlt_hy⟩
        rw [decide_eq_true this]; simp
      have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h j1) = .hx j1 := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
      have hce_hx : chooseEdge1 glob n b s (.hx j1) = false := by
        rw [chooseEdge1_hx_eq]
        have : 0 < b ∧ j1.val < lowestOne0 b n ∧ j1.val + s < hyLim0 b n s :=
          ⟨hb0, by dsimp [j1]; omega, hlt_hy⟩
        rw [decide_eq_true this]; simp
      have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx j1) = .hy j1 := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
      have hce_hy : chooseEdge1 glob n b s (.hy j1) = false := by
        rw [chooseEdge1_hy_eq]
        have : 0 < b ∧ j1.val < lowestOne0 b n ∧ j1.val + s < hyLim0 b n s :=
          ⟨hb0, by dsimp [j1]; omega, hlt_hy⟩
        rw [decide_eq_true this]; simp
      have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy j1) = .f j1 := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hy]; rfl
      set p : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hhit_hy : HitsWithTop glob n b s (.hy j1) (.u i) (.k p) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.hy j1) (.u i) (.k p) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := j1.isLt; omega
        · rw [hs_hy]; exact ih
      have hhit_hx : HitsWithTop glob n b s (.hx j1) (.u i) (.k p) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.hx j1) (.u i) (.k p) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := j1.isLt; omega
        · rw [hs_hx]; exact hhit_hy
      have hhit_h : HitsWithTop glob n b s (.h j1) (.u i) (.k p) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.h j1) (.u i) (.k p) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := j1.isLt; omega
        · rw [hs_h]; exact hhit_hx
      have hhit_u : HitsWithTop glob n b s (.u j1) (.u i) (.k p) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.u j1) (.u i) (.k p) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := j1.isLt; omega
        · rw [hs_u]; exact hhit_h
      have hh_j : hasHigherOne0 b n j.val = true := by
        rw [hasHigherOne0_iff]
        exact ⟨lowestOne0 b n, by omega, lowestOne0_lt hb0 hvalid.2.1, testBit_lowestOne0 hb0 hvalid.2.1⟩
      have hs_zj : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z j) = .u j1 := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl]
        have hce_zj : chooseEdge1 glob n b s (.z j) = true := by
          dsimp [chooseEdge1]; rw [decide_eq_true hj1_n, hh_j]; rfl
        rw [if_pos hce_zj]; dsimp [edge1, j1]; rw [dif_pos hj1_n]
      have htau_j : chooseTauEdge1 n b s (.g j) = true := by
        dsimp [chooseTauEdge1]
        have hcond : 0 < b ∧ j.val < lowestOne0 b n ∧ j.val + 1 + s < uLim0 b n :=
          ⟨hb0, by omega, by omega⟩
        rw [decide_eq_true hcond]; simp
      have hs_gj : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g j) = .k j := by
        unfold step G_bin owner_bin predTau0; rw [if_pos htau_j]; rfl
      have hs_kj : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k j) = .z j := rfl
      have hs_fj : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f j) = .g j := rfl
      have hhit_z : HitsWithTop glob n b s (.z j) (.u i) (.k p) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.z j) (.u i) (.k p) (by nofun)
        · dsimp [G_bin, priority_bin, p]; omega
        · rw [hs_zj]; exact hhit_u
      have hhit_k : HitsWithTop glob n b s (.k j) (.u i) (.k p) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.k j) (.u i) (.k p) (by nofun)
        · dsimp [G_bin, priority_bin, p]; omega
        · rw [hs_kj]; exact hhit_z
      have hhit_g : HitsWithTop glob n b s (.g j) (.u i) (.k p) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.g j) (.u i) (.k p) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := j.isLt; omega
        · rw [hs_gj]; exact hhit_k
      apply hitsWithTop_of_step_lt glob n b s hvalid (.f j) (.u i) (.k p) (by nofun)
      · dsimp [G_bin, priority_bin, p]; omega
      · rw [hs_fj]; exact hhit_g

lemma exists_hit_g_of_f_zero (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (h0_bit : b.testBit 0 = false) (hs_lt : s < S_close0 n b)
    (i : Fin n) (hi0 : 0 < i.val) (hlo : 0 < b → i.val ≤ lowestOne0 b n)
    (hnot_u : ¬(0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < uLim0 b n)) :
    ∃ m₀ : Fin n, m₀.val < i.val ∧ b.testBit m₀.val = false ∧
      chooseTauEdge1 n b s (.g m₀) = false ∧
      HitsWithTop glob n b s (.f ⟨0, hvalid.1⟩) (.g m₀) (.f m₀) := by
  have hn := hvalid.1
  set z0 : Fin n := ⟨0, hn⟩
  have hk0 : lowestZero0 b n = 0 := by
    have := lowestZero0_le_of_testBit_false hn h0_bit; omega
  cases htau0 : chooseTauEdge1 n b s (.g z0) with
  | false =>
    have hs_f0 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f z0) = .g z0 := rfl
    exact ⟨z0, hi0, h0_bit, htau0, hitsWithTop_of_step_eq glob n b s hvalid (.f z0) (.g z0) (by nofun) hs_f0⟩
  | true =>
    have hnot_T0 : ¬(3 * (n + 2 * 0 + 1) + 2 ≤ s) := by unfold S_close0 at hs_lt; omega
    have hu0 : 0 < b ∧ 0 < lowestOne0 b n ∧ 1 + s < uLim0 b n := by
      dsimp [chooseTauEdge1, z0] at htau0
      rw [h0_bit, decide_eq_false hnot_T0, Bool.false_or, Bool.false_or, decide_eq_true_eq] at htau0
      exact ⟨htau0.1, htau0.2.1, by omega⟩
    rcases hu0 with ⟨hb0, h0_lo, h1_u⟩
    have hi_le_lo := hlo hb0
    have hle_u_lo := uLim0_le_lowestOne0 b n
    have hlo_lt := lowestOne0_lt hb0 hvalid.2.1
    set m₀ : Fin n := ⟨uLim0 b n - 1 - s, by omega⟩
    have hm₀_lt_i : m₀.val < i.val := by
      by_contra hge
      exact hnot_u ⟨hb0, by dsimp [m₀] at hge; omega, by dsimp [m₀] at hge; omega⟩
    have hm₀_lt_lo : m₀.val < lowestOne0 b n := by dsimp [m₀]; omega
    have hbit_m₀ : b.testBit m₀.val = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 hm₀_lt_lo
    have htau_m₀ : chooseTauEdge1 n b s (.g m₀) = false := by
      dsimp [chooseTauEdge1]
      simp only [hbit_m₀, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨by unfold S_close0 at hs_lt; omega, by dsimp [m₀]; omega⟩
    have h1_lt : 1 < n := by omega
    set m₁ : Fin n := ⟨1, h1_lt⟩
    have hhit_u1 := hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ rfl (by dsimp [m₀]; omega)
      (m₀.val - 1) m₁ le_rfl (by dsimp [m₁]; omega) (by dsimp [m₁, m₀]; omega)
    have hh0 : hasHigherOne0 b n 0 = true := by
      rw [hasHigherOne0_iff]
      exact ⟨lowestOne0 b n, h0_lo, hlo_lt, testBit_lowestOne0 hb0 hvalid.2.1⟩
    have hs_z0 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z z0) = .u m₁ := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl]
      have hce_z0 : chooseEdge1 glob n b s (.z z0) = true := by
        dsimp [chooseEdge1, z0]; rw [decide_eq_true h1_lt, hh0]; rfl
      rw [if_pos hce_z0]; dsimp [edge1, z0, m₁]; rw [dif_pos h1_lt]
    have hs_g0 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g z0) = .k z0 := by
      unfold step G_bin owner_bin predTau0; rw [if_pos htau0]; rfl
    have hs_k0 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k z0) = .z z0 := rfl
    have hs_f0 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f z0) = .g z0 := rfl
    have hhit_z0 : HitsWithTop glob n b s (.z z0) (.g m₀) (.f m₀) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.z z0) (.g m₀) (.f m₀) (by nofun)
      · dsimp [G_bin, priority_bin, z0, m₀]; omega
      · rw [hs_z0]; exact hhit_u1
    have hhit_k0 : HitsWithTop glob n b s (.k z0) (.g m₀) (.f m₀) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.k z0) (.g m₀) (.f m₀) (by nofun)
      · dsimp [G_bin, priority_bin, z0, m₀]; omega
      · rw [hs_k0]; exact hhit_z0
    have hhit_g0 : HitsWithTop glob n b s (.g z0) (.g m₀) (.f m₀) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.g z0) (.g m₀) (.f m₀) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin, z0]; omega
      · rw [hs_g0]; exact hhit_k0
    have hhit_f0 : HitsWithTop glob n b s (.f z0) (.g m₀) (.f m₀) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.f z0) (.g m₀) (.f m₀) (by nofun)
      · dsimp [G_bin, priority_bin, z0, m₀]; omega
      · rw [hs_f0]; exact hhit_g0
    exact ⟨m₀, hm₀_lt_i, hbit_m₀, htau_m₀, hhit_f0⟩

lemma bestEdge1_rp_eq (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) (hi0 : 0 < i.val) :
    bestEdge1 n b s (.rp i) =
      if b < 2 ^ n - 1 ∧ S_close0 n b ≤ s then decide (i.val ≠ lowestZero0 b n)
      else decide ¬(0 < b ∧ i.val = lowestOne0 b n) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have h2pow := two_le_two_pow hn
  have hne0 : i.val ≠ 0 := by omega
  unfold bestEdge1 nextPair
  by_cases hc1 : b = 2 ^ n - 1 ∧ s = 9 * n - 4
  · have hnot3 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b ≤ s) := by omega
    rw [if_pos hc1, if_neg hnot3]
    dsimp [chooseEdge1]
    rw [if_neg hne0, if_neg (by omega)]
  · rw [if_neg hc1]
    by_cases hc2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
    · have hc3 : b < 2 ^ n - 1 ∧ S_close0 n b ≤ s := ⟨hc2.1, by omega⟩
      rw [if_pos hc2, if_pos hc3]
      dsimp [chooseEdge1]
      rw [if_neg hne0, if_neg (by omega), lowestOne0_add_one hc2.1]
      congr 1; exact propext ⟨fun h heq => h ⟨by omega, heq⟩, fun h ⟨_, heq⟩ => h heq⟩
    · rw [if_neg hc2]
      by_cases hc3 : b < 2 ^ n - 1 ∧ S_close0 n b ≤ s
      · rw [if_pos hc3]; dsimp [chooseEdge1]; rw [if_neg hne0, if_pos ⟨hc3.1, by omega⟩]
      · rw [if_neg hc3]; dsimp [chooseEdge1]; rw [if_neg hne0, if_neg (fun ⟨h1, h2⟩ => hc3 ⟨h1, by omega⟩)]

lemma bestEdge1_sp_eq (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) (hi0 : 0 < i.val) :
    bestEdge1 n b s (.sp i) =
      if b < 2 ^ n - 1 ∧ S_close0 n b + 2 ≤ s then decide (i.val ≠ lowestZero0 b n)
      else decide ¬(0 < b ∧ i.val = lowestOne0 b n) := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have h2pow := two_le_two_pow hn
  have hne0 : i.val ≠ 0 := by omega
  unfold bestEdge1 nextPair
  by_cases hc1 : b = 2 ^ n - 1 ∧ s = 9 * n - 4
  · have hnot3 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 2 ≤ s) := by omega
    rw [if_pos hc1, if_neg hnot3]
    dsimp [chooseEdge1]
    rw [if_neg hne0, if_neg (by omega)]
  · rw [if_neg hc1]
    by_cases hc2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
    · have hc3 : b < 2 ^ n - 1 ∧ S_close0 n b + 2 ≤ s := ⟨hc2.1, by omega⟩
      rw [if_pos hc2, if_pos hc3]
      dsimp [chooseEdge1]
      rw [if_neg hne0, if_neg (by omega), lowestOne0_add_one hc2.1]
      congr 1; exact propext ⟨fun h heq => h ⟨by omega, heq⟩, fun h ⟨_, heq⟩ => h heq⟩
    · rw [if_neg hc2]
      by_cases hc3 : b < 2 ^ n - 1 ∧ S_close0 n b + 2 ≤ s
      · rw [if_pos hc3]; dsimp [chooseEdge1]; rw [if_neg hne0, if_pos ⟨hc3.1, by omega⟩]
      · rw [if_neg hc3]; dsimp [chooseEdge1]; rw [if_neg hne0, if_neg (fun ⟨h1, h2⟩ => hc3 ⟨h1, by omega⟩)]

lemma mem_rp_ge_iff_testBit (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hi0 : 0 < i.val) (hbit_i : b.testBit i.val = false)
    (hbe : bestEdge1 n b s (.rp i) = true)
    (hnot_u : ¬(0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < uLim0 b n))
    (l : Fin n) (hil : i.val ≤ l.val)
    (u : V_bin n) (hu : u = .z l ∨ u = .f l ∨ u = .k l) :
    u ∈ predPath glob n b s (.rp ⟨i.val - 1, by have := i.isLt; omega⟩) ↔ b.testBit l.val = true := by
  have hn := hvalid.1
  set p : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
  have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    rcases hu with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin]; omega }
  have hk_le_i := lowestZero0_le_of_testBit_false i.isLt hbit_i
  rw [bestEdge1_rp_eq n b s hvalid i hi0] at hbe
  by_cases hr_ge : rActive0 n b s = true ∧ rTarg0 n b s ≤ p.val
  · rcases hr_ge with ⟨hract, ht_le⟩
    rw [highMem_rp_of_ge glob n b s hvalid hract n p (by omega) ht_le u hp_u]
    set t : Fin n := ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hract⟩
    have htl : t.val < l.val := by dsimp [t, p] at ht_le ⊢; omega
    have hne_t : l ≠ t := fun h => by subst h; omega
    rcases hu with rfl | rfl | rfl <;> { dsimp [highMemF]; simp [hne_t, htl] }
  · have hbelow : rActive0 n b s = true → p.val < rTarg0 n b s :=
      fun h => Nat.lt_of_not_ge (fun hge => hr_ge ⟨h, hge⟩)
    rw [mem_rp_below_iff_f_zero glob n b s hvalid n p (by omega) hbelow u hp_u]
    set z0 : Fin n := ⟨0, hn⟩
    have hb_lt : b < 2 ^ n - 1 := by
      by_contra hge
      have heq : b = 2 ^ n - 1 := by have := hvalid.2.1; omega
      have hbit' : b.testBit i.val = true := by rw [heq]; exact testBit_two_pow_sub_one n i.val i.isLt
      exact Bool.false_ne_true (hbit_i.symm.trans hbit')
    have hs_le : s ≤ S_close0 n b := by
      by_contra hgt
      have hs_ge1 : b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s := ⟨hb_lt, by omega⟩
      have hract : rActive0 n b s = true := by unfold rActive0; exact decide_eq_true (Or.inr hs_ge1)
      have hrtarg : rTarg0 n b s = lowestZero0 b n := by unfold rTarg0; rw [if_pos hs_ge1]
      rw [if_pos ⟨hb_lt, by omega⟩, decide_eq_true_eq] at hbe
      exact hr_ge ⟨hract, by dsimp [p]; omega⟩
    have hlo_ge : 0 < b → i.val ≤ lowestOne0 b n := by
      intro hb0
      by_contra hlt
      have hract : rActive0 n b s = true := by unfold rActive0; exact decide_eq_true (Or.inl hb0)
      have hnot_s1 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s) := by omega
      have hrtarg : rTarg0 n b s = lowestOne0 b n := by unfold rTarg0; rw [if_neg hnot_s1]
      exact hr_ge ⟨hract, by dsimp [p]; omega⟩
    have h0_bit : b.testBit 0 = false := by
      by_cases hb0 : 0 < b
      · exact testBit_of_lt_lowestOne0 hb0 hvalid.2.1 (by have := hlo_ge hb0; omega)
      · have : b = 0 := by omega
        subst this; exact Nat.zero_testBit 0
    have hk0 : lowestZero0 b n = 0 := by
      have := lowestZero0_le_of_testBit_false hn h0_bit; omega
    by_cases hs_eq : s = S_close0 n b
    · have hbot0 : isBot0 n b s z0 = true := by
        unfold isBot0; rw [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr ⟨hb_lt, by dsimp [z0]; omega, by omega⟩
      rw [highMem_f_of_isBot0 glob n b s hvalid z0 hbot0 u hp_u]
      have h0l : z0.val < l.val := by dsimp [z0]; omega
      have hne0 : l ≠ z0 := fun h => by subst h; omega
      rcases hu with rfl | rfl | rfl <;> { dsimp [highMemF]; simp [hne0, h0l] }
    · rcases exists_hit_g_of_f_zero glob n b s hvalid h0_bit (by omega) i hi0 hlo_ge hnot_u with
        ⟨m₀, hm₀_lt, _, htau_m₀, hhit_f0⟩
      have hp_fm₀_u : (G_bin n).priority (.f m₀) < (G_bin n).priority u := by
        rcases hu with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin]; omega }
      rw [hhit_f0.2.2 u hp_fm₀_u]
      have hport_g := hitsPortal_g_of_tau_false glob n b s hvalid m₀ htau_m₀
      exact mem_portal_zfk_iff_testBit glob n b s hvalid hport_g l (by omega) u hu

lemma highMem_rp_of_testBit_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hi0 : 0 < i.val) (hbit_i : b.testBit i.val = true)
    (hbe : bestEdge1 n b s (.rp i) = true) :
    ∃ t : Fin n, t.val < i.val ∧
      ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
        (u ∈ predPath glob n b s (.rp ⟨i.val - 1, by have := i.isLt; omega⟩) ↔ highMemF n b t u) := by
  have hn := hvalid.1
  set p : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
  by_cases hr_ge : rActive0 n b s = true ∧ rTarg0 n b s ≤ p.val
  · rcases hr_ge with ⟨hract, ht_le⟩
    refine ⟨⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hract⟩, by dsimp [p] at ht_le ⊢; omega, ?_⟩
    intro u hu
    exact highMem_rp_of_ge glob n b s hvalid hract n p (by omega) ht_le u hu
  · have hbelow : rActive0 n b s = true → p.val < rTarg0 n b s :=
      fun h => Nat.lt_of_not_ge (fun hge => hr_ge ⟨h, hge⟩)
    set z0 : Fin n := ⟨0, hn⟩
    refine ⟨z0, hi0, fun u hu => ?_⟩
    rw [mem_rp_below_iff_f_zero glob n b s hvalid n p (by omega) hbelow u hu]
    have hb0 : 0 < b := by
      by_contra h0; have : b = 0 := by omega
      subst this; rw [Nat.zero_testBit] at hbit_i; exact Bool.false_ne_true hbit_i
    have hlo_le : lowestOne0 b n ≤ i.val := lowestOne0_le_of_testBit_true i.isLt hbit_i
    have hract : rActive0 n b s = true := by unfold rActive0; exact decide_eq_true (Or.inl hb0)
    have hp_lt_targ := hbelow hract
    have hbot0 : isBot0 n b s z0 = true := by
      unfold isBot0; rw [Bool.or_eq_true, decide_eq_true_eq]
      unfold rTarg0 at hp_lt_targ
      split_ifs at hp_lt_targ with hs1
      · exact Or.inl (testBit_of_lt_lowestZero0 hs1.1 (by dsimp [p, z0] at hp_lt_targ ⊢; omega))
      · have hi_eq_lo : i.val = lowestOne0 b n := by dsimp [p] at hp_lt_targ; omega
        rw [bestEdge1_rp_eq n b s hvalid i hi0] at hbe
        split_ifs at hbe with hcs
        · have h0_bit : b.testBit 0 = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 (by omega)
          have hk0 : lowestZero0 b n = 0 := by
            have := lowestZero0_le_of_testBit_false hn h0_bit; omega
          exact Or.inr ⟨hcs.1, by dsimp [z0]; omega, hcs.2⟩
        · exfalso
          rw [decide_eq_true_eq] at hbe
          exact hbe ⟨hb0, hi_eq_lo⟩
    exact highMem_f_of_isBot0 glob n b s hvalid z0 hbot0 u hu

theorem bestEdge_rp (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    BestEdgeProp glob n b s (.rp i) := by
  intro _ hne
  by_cases hi0 : i.val = 0
  · exfalso; apply hne; simp [edge0, edge1, hi0]
  · have hi_pos : 0 < i.val := by omega
    set p : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
    have he0 : edge0 n (.rp i) = .f i := rfl
    have he1 : edge1 n (.rp i) = .rp p := by simp [edge1, p, hi0]
    unfold bestEdge worstEdge
    have hbe_eq := bestEdge1_rp_eq n b s hvalid i hi_pos
    cases hbe : bestEdge1 n b s (.rp i) with
    | false =>
      dsimp; rw [he0, he1]
      rw [hbe] at hbe_eq
      split_ifs at hbe_eq with hc_s
      · have hik : i.val = lowestZero0 b n := by
          have := hbe_eq.symm; rwa [decide_eq_false_iff_not, not_not] at this
        have hbit_i : b.testBit i.val = false := by rw [hik]; exact testBit_lowestZero0 hc_s.1
        have hbot_i : isBot0 n b s i = true := by
          unfold isBot0; rw [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr ⟨hc_s.1, hik, hc_s.2⟩
        have hbit0 : b.testBit 0 = true := testBit_of_lt_lowestZero0 hc_s.1 (by omega)
        set z0 : Fin n := ⟨0, hvalid.1⟩
        have hbot0 : isBot0 n b s z0 = true := by
          unfold isBot0; rw [Bool.or_eq_true]; exact Or.inl hbit0
        have hb0 : 0 < b := by
          by_contra h0; have : b = 0 := by omega
          subst this; rw [Nat.zero_testBit] at hbit0; exact Bool.false_ne_true hbit0
        have hlo0 : lowestOne0 b n = 0 := by
          have := lowestOne0_le_of_testBit_true hvalid.1 hbit0; omega
        have hrp_mem : ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
            (u ∈ predPath glob n b s (.rp p) ↔ highMemF n b z0 u) := by
          intro u hu
          have hract : rActive0 n b s = true := by unfold rActive0; exact decide_eq_true (Or.inl hb0)
          by_cases hs1 : b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s
          · have hbelow : rActive0 n b s = true → p.val < rTarg0 n b s := by
              intro _; unfold rTarg0; rw [if_pos hs1]; dsimp [p]; omega
            rw [mem_rp_below_iff_f_zero glob n b s hvalid n p (by omega) hbelow u hu]
            exact highMem_f_of_isBot0 glob n b s hvalid z0 hbot0 u hu
          · have ht_le : rTarg0 n b s ≤ p.val := by unfold rTarg0; rw [if_neg hs1]; omega
            rw [highMem_rp_of_ge glob n b s hvalid hract n p (by omega) ht_le u hu]
            have hfin : (⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hract⟩ : Fin n) = z0 := by
              apply Fin.ext; dsimp [z0]; unfold rTarg0; rw [if_neg hs1, hlo0]
            rw [hfin]
        exact predVal_lt_of_highMemF_lt_of_testBit_false glob n b s hvalid z0 i hi_pos hbit_i
          (.rp p) (.f i) hrp_mem (highMem_f_of_isBot0 glob n b s hvalid i hbot_i)
      · have hlo_eq : 0 < b ∧ i.val = lowestOne0 b n := by
          have := hbe_eq.symm; rwa [decide_eq_false_iff_not, not_not] at this
        rcases hlo_eq with ⟨hb0, hi_lo⟩
        have hbit_i : b.testBit i.val = true := by rw [hi_lo]; exact testBit_lowestOne0 hb0 hvalid.2.1
        have hbot_i : isBot0 n b s i = true := by
          unfold isBot0; rw [Bool.or_eq_true]; exact Or.inl hbit_i
        have h0_bit : b.testBit 0 = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 (by omega)
        have hb_lt : b < 2 ^ n - 1 := by
          by_contra hge
          have heq : b = 2 ^ n - 1 := by have := hvalid.2.1; omega
          have hbit' : b.testBit 0 = true := by rw [heq]; exact testBit_two_pow_sub_one n 0 hvalid.1
          exact Bool.false_ne_true (h0_bit.symm.trans hbit')
        have hs_lt : s < S_close0 n b := by omega
        set z0 : Fin n := ⟨0, hvalid.1⟩
        have hbelow : rActive0 n b s = true → p.val < rTarg0 n b s := by
          intro _
          have hnot1 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s) := by omega
          unfold rTarg0; rw [if_neg hnot1]; dsimp [p]; omega
        rcases exists_hit_g_of_f_zero glob n b s hvalid h0_bit hs_lt i hi_pos (fun _ => by omega)
          (fun ⟨_, hlt, _⟩ => by omega) with ⟨m₀, hm₀_lt, hbit_m₀, htau_m₀, hhit_f0⟩
        have hport_g := hitsPortal_g_of_tau_false glob n b s hvalid m₀ htau_m₀
        apply predVal_lt_of_setLT glob n b s hvalid
        apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .f m₀)
        · rw [mem_rp_below_iff_f_zero glob n b s hvalid n p (by omega) hbelow (.f m₀)
            (by dsimp [G_bin, priority_bin]; omega)]
          exact hhit_f0.2.1
        · rw [highMem_f_of_isBot0 glob n b s hvalid i hbot_i (.f m₀) (by dsimp [G_bin, priority_bin]; omega)]
          dsimp [highMemF]
          rintro (rfl | ⟨h, _⟩) <;> omega
        · exact prio_f_odd n m₀
        · intro u hu
          have hp_c_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
            have : (G_bin n).priority .c < (G_bin n).priority (.f m₀) := by dsimp [G_bin, priority_bin]; omega
            omega
          rw [highMem_f_of_isBot0 glob n b s hvalid i hbot_i u hp_c_u,
              mem_rp_below_iff_f_zero glob n b s hvalid n p (by omega) hbelow u hp_c_u,
              hhit_f0.2.2 u hu]
          have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
            have : (G_bin n).priority .s < (G_bin n).priority (.f m₀) := by dsimp [G_bin, priority_bin]; omega
            omega
          rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, hu_eq⟩
          rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g l (by omega) u hu_eq]
          have hF : highMemF n b i u ↔ b.testBit l.val = true := by
            have hfin : i = ⟨lowestOne0 b n, lowestOne0_lt hb0 hvalid.2.1⟩ := Fin.ext hi_lo
            rw [hfin]
            rcases hu_eq with rfl | rfl | rfl <;> exact highMemF_lowestOne0_iff n b hb0 hvalid.2.1 l
          exact hF.symm
    | true =>
      dsimp; rw [he1, he0]
      cases hbit_i : b.testBit i.val with
      | true =>
        have hbot_i : isBot0 n b s i = true := by
          unfold isBot0; rw [Bool.or_eq_true]; exact Or.inl hbit_i
        rcases highMem_rp_of_testBit_true glob n b s hvalid i hi_pos hbit_i hbe with ⟨t, hti, hrp_mem⟩
        exact predVal_lt_of_highMemF_lt_of_testBit_true glob n b s hvalid t i hti hbit_i
          (.f i) (.rp p) (highMem_f_of_isBot0 glob n b s hvalid i hbot_i) hrp_mem
      | false =>
        by_cases hu_i : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < uLim0 b n
        · rcases hu_i with ⟨hb0, hi_lo, hi_u⟩
          have hle_u_lo := uLim0_le_lowestOne0 b n
          have hlo_lt := lowestOne0_lt hb0 hvalid.2.1
          have hs_lt : s < S_close0 n b := by unfold S_close0; omega
          have hbelow : rActive0 n b s = true → p.val < rTarg0 n b s := by
            intro _
            have hnot1 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s) := by omega
            unfold rTarg0; rw [if_neg hnot1]; dsimp [p]; omega
          set z0 : Fin n := ⟨0, hvalid.1⟩
          have hhit_f0_ui := hitsWithTop_f_to_u_of_still glob n b s hvalid hb0 i hi_pos hi_lo hi_u
            (i.val - 1) z0 (by dsimp [z0]; omega) hi_pos
          have hhit_rp_ui : HitsWithTop glob n b s (.rp p) (.u i) (.k p) :=
            hitsWithTop_rp_of_f_zero glob n b s hvalid hhit_f0_ui
              (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega)
              n p (by omega) hbelow
          have hle_hy := uLim0_le_hyLim0 b n s
          have hlt_hy : i.val + s < hyLim0 b n s := by omega
          have howner_u : (G_bin n).owner (.u i) = false := by
            dsimp [G_bin, owner_bin]; rw [if_neg hi0]
          have hce_u : chooseEdge1 glob n b s (.u i) = false :=
            chooseEdge1_u_of_still glob n b s hb0 i hi_lo hi_u
          have hs_u : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u i) = .h i := by
            unfold step predState0; rw [if_pos howner_u, hce_u]; rfl
          have hce_h : chooseEdge1 glob n b s (.h i) = false := by
            rw [chooseEdge1_h_eq]
            have : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s := ⟨hb0, hi_lo, hlt_hy⟩
            rw [decide_eq_true this]; simp
          have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h i) = .hx i := by
            unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
          have hce_hx : chooseEdge1 glob n b s (.hx i) = false := by
            rw [chooseEdge1_hx_eq]
            have : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s := ⟨hb0, hi_lo, hlt_hy⟩
            rw [decide_eq_true this]; simp
          have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx i) = .hy i := by
            unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
          have hce_hy : chooseEdge1 glob n b s (.hy i) = false := by
            rw [chooseEdge1_hy_eq]
            have : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s := ⟨hb0, hi_lo, hlt_hy⟩
            rw [decide_eq_true this]; simp
          have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy i) = .f i := by
            unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hy]; rfl
          have hhit_rp_hi : HitsWithTop glob n b s (.rp p) (.h i) (.k p) :=
            hitsWithTop_of_step_right glob n b s hvalid (.rp p) (.u i) (.h i) (.k p) (by nofun)
              hhit_rp_ui hs_u (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega)
          have hhit_rp_hxi : HitsWithTop glob n b s (.rp p) (.hx i) (.k p) :=
            hitsWithTop_of_step_right glob n b s hvalid (.rp p) (.h i) (.hx i) (.k p) (by nofun)
              hhit_rp_hi hs_h (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega)
          have hhit_rp_hyi : HitsWithTop glob n b s (.rp p) (.hy i) (.k p) :=
            hitsWithTop_of_step_right glob n b s hvalid (.rp p) (.hx i) (.hy i) (.k p) (by nofun)
              hhit_rp_hxi hs_hx (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega)
          have hhit_rp_fi : HitsWithTop glob n b s (.rp p) (.f i) (.k p) :=
            hitsWithTop_of_step_right glob n b s hvalid (.rp p) (.hy i) (.f i) (.k p) (by nofun)
              hhit_rp_hyi hs_hy (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega)
          exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid hhit_rp_fi (prio_k_even n p)
        · have hb_lt : b < 2 ^ n - 1 := by
            by_contra hge
            have heq : b = 2 ^ n - 1 := by have := hvalid.2.1; omega
            have hbit' : b.testBit i.val = true := by rw [heq]; exact testBit_two_pow_sub_one n i.val i.isLt
            exact Bool.false_ne_true (hbit_i.symm.trans hbit')
          have hk_le_i := lowestZero0_le_of_testBit_false i.isLt hbit_i
          have hnot_Ti : ¬(3 * (n + 2 * i.val + 1) + 2 ≤ s) := by
            intro hTi
            by_cases hik : i.val = lowestZero0 b n
            · have hs_ge : S_close0 n b ≤ s := by unfold S_close0; omega
              rw [hbe, if_pos ⟨hb_lt, hs_ge⟩] at hbe_eq
              have := hbe_eq.symm; rw [decide_eq_true_eq] at this; exact this hik
            · have hmax := maxStep0_of_lt hb_lt
              have hs_max := hvalid.2.2
              have := i.isLt
              unfold S_close0 at hmax
              omega
          have htau_gi : chooseTauEdge1 n b s (.g i) = false := by
            dsimp [chooseTauEdge1]
            simp only [hbit_i, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
            exact ⟨hnot_Ti, fun ⟨h1, h2, h3⟩ => hu_i ⟨h1, h2, by omega⟩⟩
          have hport_gi := hitsPortal_g_of_tau_false glob n b s hvalid i htau_gi
          have hs_fi : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f i) = .g i := rfl
          have hpath_fi : predPath glob n b s (.f i) = insert (.f i) (predPath glob n b s (.g i)) := by
            rw [predPath, predVal, pred_path_step glob n b s hvalid (.f i) (by nofun), hs_fi]
          apply predVal_lt_of_setLT glob n b s hvalid
          apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .f i)
          · rw [hpath_fi]; exact Finset.mem_insert_self _ _
          · rw [mem_rp_ge_iff_testBit glob n b s hvalid i hi_pos hbit_i hbe hu_i i le_rfl (.f i) (Or.inr (Or.inl rfl)),
                hbit_i]
            decide
          · exact prio_f_odd n i
          · intro u hu
            have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
              have : (G_bin n).priority .s < (G_bin n).priority (.f i) := by dsimp [G_bin, priority_bin]; omega
              omega
            rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, hu_eq⟩
            have hil : i.val ≤ l.val := by
              rcases hu_eq with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin] at hu; omega }
            have hne_fi : u ≠ .f i := by intro rfl; omega
            rw [mem_rp_ge_iff_testBit glob n b s hvalid i hi_pos hbit_i hbe hu_i l hil u hu_eq,
                hpath_fi, Finset.mem_insert, or_iff_right hne_fi]
            have hkl : b < 2 ^ n - 1 → S_close0 n b + 1 ≤ s → lowestZero0 b n < l.val := by
              intro _ hs1
              rw [hbe, if_pos ⟨hb_lt, by omega⟩] at hbe_eq
              have hne_k : i.val ≠ lowestZero0 b n := by
                have := hbe_eq.symm; rwa [decide_eq_true_eq] at this
              omega
            rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_gi l hkl u hu_eq]

lemma highMem_hx_of_chooseEdge1_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin n) (hce : chooseEdge1 glob n b s (.hx m) = true)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.hx m) ↔ highMemZ n b m u := by
  have hs : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .z m := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce]; rfl
  have hp : (G_bin n).priority (.hx m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  rw [mem_path_step_high glob n b s hvalid (.hx m) u (by nofun) hp hu, hs]
  have hstill : ∀ hi1 : m.val + 1 < n, uStillH0 n b s ⟨m.val + 1, hi1⟩ = false := by
    intro hi1
    unfold uStillH0; rw [decide_eq_false_iff_not]
    rintro ⟨hb0, hlo, hu_lt⟩
    dsimp at hlo hu_lt
    have hle_hy := uLim0_le_hyLim0 b n s
    have hhy : 0 < b ∧ m.val < lowestOne0 b n ∧ m.val + s < hyLim0 b n s :=
      ⟨hb0, by omega, by omega⟩
    rw [chooseEdge1_hx_eq, decide_eq_true hhy] at hce
    simp at hce
  exact highMem_z glob n b s hvalid m hstill u hu

lemma hitsWithTop_hx_f_of_chooseEdge1_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin n) (hce : chooseEdge1 glob n b s (.hx m) = false) :
    (∀ {q d : V_bin n}, HitsWithTop glob n b s (.f m) q d →
      (G_bin n).priority (.hx m) < (G_bin n).priority d →
      HitsWithTop glob n b s (.hx m) q d) ∧
    (∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
      (u ∈ predPath glob n b s (.hx m) ↔ u ∈ predPath glob n b s (.f m))) := by
  have hce_hy : chooseEdge1 glob n b s (.hy m) = false := by
    rw [chooseEdge1_hx_eq] at hce
    rw [chooseEdge1_hy_eq]
    cases h1 : b.testBit m.val
    · cases h2 : decide (0 < b ∧ m.val < lowestOne0 b n ∧ m.val + s < hyLim0 b n s)
      · simp only [h1, h2, Bool.not_false, Bool.true_and, Bool.not_eq_false', decide_eq_true_eq] at hce ⊢
        exact ⟨hce.1, hce.2.1, by omega⟩
      · simp
    · simp
  have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce]; rfl
  have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hy]; rfl
  refine ⟨fun {q d} hf hprio => ?_, fun u hu => ?_⟩
  · have hhit_hy : HitsWithTop glob n b s (.hy m) q d := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.hy m) q d (by nofun)
      · dsimp [G_bin, priority_bin] at hprio ⊢; omega
      · rw [hs_hy]; exact hf
    apply hitsWithTop_of_step_lt glob n b s hvalid (.hx m) q d (by nofun) hprio
    rw [hs_hx]; exact hhit_hy
  · have hp_hx : (G_bin n).priority (.hx m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    have hp_hy : (G_bin n).priority (.hy m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    rw [mem_path_step_high glob n b s hvalid (.hx m) u (by nofun) hp_hx hu, hs_hx,
        mem_path_step_high glob n b s hvalid (.hy m) u (by nofun) hp_hy hu, hs_hy]

lemma highMem_hx_of_closed (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin n)
    (hclosed : b.testBit m.val = true ∨ (b < 2 ^ n - 1 ∧ m.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s))
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.hx m) ↔ highMemF n b m u := by
  have hbot : isBot0 n b s m = true := by
    unfold isBot0; rw [Bool.or_eq_true, decide_eq_true_eq]
    rcases hclosed with hbit | ⟨h1, h2, h3⟩
    · exact Or.inl hbit
    · exact Or.inr ⟨h1, h2, by omega⟩
  have hce_hx : chooseEdge1 glob n b s (.hx m) = false := by
    rw [chooseEdge1_hx_eq]
    rcases hclosed with hbit | h2
    · simp [hbit]
    · rw [decide_eq_true h2]; simp
  rw [(hitsWithTop_hx_f_of_chooseEdge1_false glob n b s hvalid m hce_hx).2 u hu]
  exact highMem_f_of_isBot0 glob n b s hvalid m hbot u hu

lemma mem_sp_ge_iff_testBit (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hi0 : 0 < i.val)
    (hnot_u : ¬(0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < uLim0 b n))
    (l : Fin n) (hil : i.val ≤ l.val)
    (u : V_bin n) (hu : u = .z l ∨ u = .f l ∨ u = .k l) :
    u ∈ predPath glob n b s (.sp ⟨i.val - 1, by have := i.isLt; omega⟩) ↔ b.testBit l.val = true := by
  have hn := hvalid.1
  set p : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
  have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    rcases hu with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin]; omega }
  by_cases hs_ge : sActive0 n b s = true ∧ sTarg0 n b s ≤ p.val
  · rcases hs_ge with ⟨hsact, ht_le⟩
    rw [highMem_sp_of_ge glob n b s hvalid hsact n p (by omega) ht_le u hp_u]
    set t : Fin n := ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hsact⟩
    have htl : t.val < l.val := by dsimp [t, p] at ht_le ⊢; omega
    have hne_t : l ≠ t := fun h => by subst h; omega
    rcases hu with rfl | rfl | rfl <;> { dsimp [highMemF]; simp [hne_t, htl] }
  · have hbelow : sActive0 n b s = true → p.val < sTarg0 n b s :=
      fun h => Nat.lt_of_not_ge (fun hge => hs_ge ⟨h, hge⟩)
    rw [mem_sp_below_iff_hx_zero glob n b s hvalid n p (by omega) hbelow u hp_u]
    set z0 : Fin n := ⟨0, hn⟩
    have h0l : z0.val < l.val := by dsimp [z0]; omega
    have hne0 : l ≠ z0 := fun h => by subst h; omega
    cases hce0 : chooseEdge1 glob n b s (.hx z0) with
    | true =>
      rw [highMem_hx_of_chooseEdge1_true glob n b s hvalid z0 hce0 u hp_u]
      rcases hu with rfl | rfl | rfl <;> { dsimp [highMemZ]; simp [hne0, h0l] }
    | false =>
      rw [(hitsWithTop_hx_f_of_chooseEdge1_false glob n b s hvalid z0 hce0).2 u hp_u]
      cases hbot0 : isBot0 n b s z0 with
      | true =>
        rw [highMem_f_of_isBot0 glob n b s hvalid z0 hbot0 u hp_u]
        rcases hu with rfl | rfl | rfl <;> { dsimp [highMemF]; simp [hne0, h0l] }
      | false =>
        have hbit0 : b.testBit 0 = false := by
          unfold isBot0 at hbot0; rw [Bool.or_eq_false_iff] at hbot0; exact hbot0.1
        have hnot_s2 : ¬(b < 2 ^ n - 1 ∧ z0.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) := by
          rintro ⟨h1, h2, h3⟩
          unfold isBot0 at hbot0; rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hbot0
          exact hbot0.2 ⟨h1, h2, by omega⟩
        have hhy0 : 0 < b ∧ z0.val < lowestOne0 b n ∧ z0.val + s < hyLim0 b n s := by
          rw [chooseEdge1_hx_eq] at hce0
          rw [hbit0, decide_eq_false hnot_s2] at hce0
          simpa using hce0
        have hle_hy := hyLim0_le_n b n s
        have hs_lt : s < S_close0 n b := by
          unfold S_close0; dsimp [z0] at hhy0; omega
        have hlo_ge : 0 < b → i.val ≤ lowestOne0 b n := by
          intro hb0
          have hsact : sActive0 n b s = true := by unfold sActive0; exact decide_eq_true (Or.inl hb0)
          have hp_lt := hbelow hsact
          have hnot_s3 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s) := by omega
          unfold sTarg0 at hp_lt; rw [if_neg hnot_s3] at hp_lt
          dsimp [p] at hp_lt; omega
        rcases exists_hit_g_of_f_zero glob n b s hvalid hbit0 hs_lt i hi0 hlo_ge hnot_u with
          ⟨m₀, hm₀_lt, _, htau_m₀, hhit_f0⟩
        have hp_fm₀_u : (G_bin n).priority (.f m₀) < (G_bin n).priority u := by
          rcases hu with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin]; omega }
        rw [hhit_f0.2.2 u hp_fm₀_u]
        have hport_g := hitsPortal_g_of_tau_false glob n b s hvalid m₀ htau_m₀
        exact mem_portal_zfk_iff_testBit glob n b s hvalid hport_g l (by omega) u hu

lemma highMem_sp_of_testBit_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (i : Fin n) (hi0 : 0 < i.val) (hbit_i : b.testBit i.val = true)
    (hbe : bestEdge1 n b s (.sp i) = true) :
    ∃ t : Fin n, t.val < i.val ∧
      ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
        (u ∈ predPath glob n b s (.sp ⟨i.val - 1, by have := i.isLt; omega⟩) ↔ highMemF n b t u) := by
  have hn := hvalid.1
  set p : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
  by_cases hs_ge : sActive0 n b s = true ∧ sTarg0 n b s ≤ p.val
  · rcases hs_ge with ⟨hsact, ht_le⟩
    refine ⟨⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hsact⟩, by dsimp [p] at ht_le ⊢; omega, ?_⟩
    intro u hu
    exact highMem_sp_of_ge glob n b s hvalid hsact n p (by omega) ht_le u hu
  · have hbelow : sActive0 n b s = true → p.val < sTarg0 n b s :=
      fun h => Nat.lt_of_not_ge (fun hge => hs_ge ⟨h, hge⟩)
    set z0 : Fin n := ⟨0, hn⟩
    refine ⟨z0, hi0, fun u hu => ?_⟩
    rw [mem_sp_below_iff_hx_zero glob n b s hvalid n p (by omega) hbelow u hu]
    have hb0 : 0 < b := by
      by_contra h0; have : b = 0 := by omega
      subst this; rw [Nat.zero_testBit] at hbit_i; exact Bool.false_ne_true hbit_i
    have hlo_le : lowestOne0 b n ≤ i.val := lowestOne0_le_of_testBit_true i.isLt hbit_i
    have hsact : sActive0 n b s = true := by unfold sActive0; exact decide_eq_true (Or.inl hb0)
    have hp_lt_targ := hbelow hsact
    have hclosed0 : b.testBit z0.val = true ∨ (b < 2 ^ n - 1 ∧ z0.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) := by
      unfold sTarg0 at hp_lt_targ
      split_ifs at hp_lt_targ with hs3
      · exact Or.inl (testBit_of_lt_lowestZero0 hs3.1 (by dsimp [p, z0] at hp_lt_targ ⊢; omega))
      · have hi_eq_lo : i.val = lowestOne0 b n := by dsimp [p] at hp_lt_targ; omega
        rw [bestEdge1_sp_eq n b s hvalid i hi0] at hbe
        split_ifs at hbe with hcs
        · have h0_bit : b.testBit 0 = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 (by omega)
          have hk0 : lowestZero0 b n = 0 := by
            have := lowestZero0_le_of_testBit_false hn h0_bit; omega
          exact Or.inr ⟨hcs.1, by dsimp [z0]; omega, hcs.2⟩
        · exfalso
          rw [decide_eq_true_eq] at hbe
          exact hbe ⟨hb0, hi_eq_lo⟩
    exact highMem_hx_of_closed glob n b s hvalid z0 hclosed0 u hu

theorem bestEdge_sp (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    BestEdgeProp glob n b s (.sp i) := by
  intro _ hne
  by_cases hi0 : i.val = 0
  · exfalso; apply hne; simp [edge0, edge1, hi0]
  · have hi_pos : 0 < i.val := by omega
    set p : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
    have he0 : edge0 n (.sp i) = .hx i := rfl
    have he1 : edge1 n (.sp i) = .sp p := by simp [edge1, p, hi0]
    unfold bestEdge worstEdge
    have hbe_eq := bestEdge1_sp_eq n b s hvalid i hi_pos
    cases hbe : bestEdge1 n b s (.sp i) with
    | false =>
      dsimp; rw [he0, he1]
      rw [hbe] at hbe_eq
      split_ifs at hbe_eq with hc_s
      · have hik : i.val = lowestZero0 b n := by
          have := hbe_eq.symm; rwa [decide_eq_false_iff_not, not_not] at this
        have hbit_i : b.testBit i.val = false := by rw [hik]; exact testBit_lowestZero0 hc_s.1
        have hclosed_i : b.testBit i.val = true ∨ (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) :=
          Or.inr ⟨hc_s.1, hik, hc_s.2⟩
        have hbit0 : b.testBit 0 = true := testBit_of_lt_lowestZero0 hc_s.1 (by omega)
        set z0 : Fin n := ⟨0, hvalid.1⟩
        have hb0 : 0 < b := by
          by_contra h0; have : b = 0 := by omega
          subst this; rw [Nat.zero_testBit] at hbit0; exact Bool.false_ne_true hbit0
        have hlo0 : lowestOne0 b n = 0 := by
          have := lowestOne0_le_of_testBit_true hvalid.1 hbit0; omega
        have hsp_mem : ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
            (u ∈ predPath glob n b s (.sp p) ↔ highMemF n b z0 u) := by
          intro u hu
          have hsact : sActive0 n b s = true := by unfold sActive0; exact decide_eq_true (Or.inl hb0)
          by_cases hs3 : b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s
          · have hbelow : sActive0 n b s = true → p.val < sTarg0 n b s := by
              intro _; unfold sTarg0; rw [if_pos hs3]; dsimp [p]; omega
            rw [mem_sp_below_iff_hx_zero glob n b s hvalid n p (by omega) hbelow u hu]
            exact highMem_hx_of_closed glob n b s hvalid z0 (Or.inl hbit0) u hu
          · have ht_le : sTarg0 n b s ≤ p.val := by unfold sTarg0; rw [if_neg hs3]; omega
            rw [highMem_sp_of_ge glob n b s hvalid hsact n p (by omega) ht_le u hu]
            have hfin : (⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hsact⟩ : Fin n) = z0 := by
              apply Fin.ext; dsimp [z0]; unfold sTarg0; rw [if_neg hs3, hlo0]
            rw [hfin]
        exact predVal_lt_of_highMemF_lt_of_testBit_false glob n b s hvalid z0 i hi_pos hbit_i
          (.sp p) (.hx i) hsp_mem (highMem_hx_of_closed glob n b s hvalid i hclosed_i)
      · have hlo_eq : 0 < b ∧ i.val = lowestOne0 b n := by
          have := hbe_eq.symm; rwa [decide_eq_false_iff_not, not_not] at this
        rcases hlo_eq with ⟨hb0, hi_lo⟩
        have hbit_i : b.testBit i.val = true := by rw [hi_lo]; exact testBit_lowestOne0 hb0 hvalid.2.1
        have hclosed_i : b.testBit i.val = true ∨ (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) :=
          Or.inl hbit_i
        have h0_bit : b.testBit 0 = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 (by omega)
        have hb_lt : b < 2 ^ n - 1 := by
          by_contra hge
          have heq : b = 2 ^ n - 1 := by have := hvalid.2.1; omega
          have hbit' : b.testBit 0 = true := by rw [heq]; exact testBit_two_pow_sub_one n 0 hvalid.1
          exact Bool.false_ne_true (h0_bit.symm.trans hbit')
        set z0 : Fin n := ⟨0, hvalid.1⟩
        have hbelow : sActive0 n b s = true → p.val < sTarg0 n b s := by
          intro _
          have hnot3 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s) := by omega
          unfold sTarg0; rw [if_neg hnot3]; dsimp [p]; omega
        cases hce0 : chooseEdge1 glob n b s (.hx z0) with
        | true =>
          apply predVal_lt_of_setLT glob n b s hvalid
          apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .z z0)
          · rw [mem_sp_below_iff_hx_zero glob n b s hvalid n p (by omega) hbelow (.z z0)
              (by dsimp [G_bin, priority_bin]; omega),
              highMem_hx_of_chooseEdge1_true glob n b s hvalid z0 hce0 (.z z0)
              (by dsimp [G_bin, priority_bin]; omega)]
            exact Or.inl rfl
          · rw [highMem_hx_of_closed glob n b s hvalid i hclosed_i (.z z0)
              (by dsimp [G_bin, priority_bin]; omega)]
            dsimp [highMemF, z0]
            rintro (h | ⟨h, _⟩)
            · have := congrArg Fin.val h; dsimp at this; omega
            · omega
          · exact prio_z_odd n z0
          · intro u hu
            have hp_c_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
              have : (G_bin n).priority .c < (G_bin n).priority (.z z0) := by dsimp [G_bin, priority_bin]; omega
              omega
            rw [highMem_hx_of_closed glob n b s hvalid i hclosed_i u hp_c_u,
                mem_sp_below_iff_hx_zero glob n b s hvalid n p (by omega) hbelow u hp_c_u,
                highMem_hx_of_chooseEdge1_true glob n b s hvalid z0 hce0 u hp_c_u]
            have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
              have : (G_bin n).priority .s < (G_bin n).priority (.z z0) := by dsimp [G_bin, priority_bin]; omega
              omega
            rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, hu_eq⟩
            have hF : highMemF n b i u ↔ b.testBit l.val = true := by
              have hfin : i = ⟨lowestOne0 b n, lowestOne0_lt hb0 hvalid.2.1⟩ := Fin.ext hi_lo
              rw [hfin]
              rcases hu_eq with rfl | rfl | rfl <;> exact highMemF_lowestOne0_iff n b hb0 hvalid.2.1 l
            rw [hF]
            by_cases hl0 : l.val = 0
            · have hl_eq : l = z0 := Fin.ext hl0
              subst hl_eq
              have hne_z0 : u ≠ .z z0 := by intro rfl; omega
              rcases hu_eq with rfl | rfl | rfl
              · exact False.elim (hne_z0 rfl)
              · dsimp [highMemZ, z0]; simp [h0_bit]
              · dsimp [highMemZ, z0]; simp [h0_bit]
            · have h0l : z0.val < l.val := by dsimp [z0]; omega
              have hne0 : l ≠ z0 := fun h => by subst h; omega
              rcases hu_eq with rfl | rfl | rfl <;> { dsimp [highMemZ]; simp [hne0, h0l] }
        | false =>
          have hnot_s2 : ¬(b < 2 ^ n - 1 ∧ z0.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) :=
            fun ⟨h1, _, h3⟩ => hc_s ⟨h1, h3⟩
          have hhy0 : 0 < b ∧ z0.val < lowestOne0 b n ∧ z0.val + s < hyLim0 b n s := by
            rw [chooseEdge1_hx_eq] at hce0
            rw [h0_bit, decide_eq_false hnot_s2] at hce0
            simpa using hce0
          have hle_hy := hyLim0_le_n b n s
          have hs_lt : s < S_close0 n b := by unfold S_close0; dsimp [z0] at hhy0; omega
          rcases exists_hit_g_of_f_zero glob n b s hvalid h0_bit hs_lt i hi_pos (fun _ => by omega)
            (fun ⟨_, hlt, _⟩ => by omega) with ⟨m₀, hm₀_lt, hbit_m₀, htau_m₀, hhit_f0⟩
          have hport_g := hitsPortal_g_of_tau_false glob n b s hvalid m₀ htau_m₀
          apply predVal_lt_of_setLT glob n b s hvalid
          apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .f m₀)
          · rw [mem_sp_below_iff_hx_zero glob n b s hvalid n p (by omega) hbelow (.f m₀)
              (by dsimp [G_bin, priority_bin]; omega),
              (hitsWithTop_hx_f_of_chooseEdge1_false glob n b s hvalid z0 hce0).2 (.f m₀)
              (by dsimp [G_bin, priority_bin]; omega)]
            exact hhit_f0.2.1
          · rw [highMem_hx_of_closed glob n b s hvalid i hclosed_i (.f m₀)
              (by dsimp [G_bin, priority_bin]; omega)]
            dsimp [highMemF]
            rintro (rfl | ⟨h, _⟩) <;> omega
          · exact prio_f_odd n m₀
          · intro u hu
            have hp_c_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
              have : (G_bin n).priority .c < (G_bin n).priority (.f m₀) := by dsimp [G_bin, priority_bin]; omega
              omega
            rw [highMem_hx_of_closed glob n b s hvalid i hclosed_i u hp_c_u,
                mem_sp_below_iff_hx_zero glob n b s hvalid n p (by omega) hbelow u hp_c_u,
                (hitsWithTop_hx_f_of_chooseEdge1_false glob n b s hvalid z0 hce0).2 u hp_c_u,
                hhit_f0.2.2 u hu]
            have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
              have : (G_bin n).priority .s < (G_bin n).priority (.f m₀) := by dsimp [G_bin, priority_bin]; omega
              omega
            rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, hu_eq⟩
            rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g l (by omega) u hu_eq]
            have hF : highMemF n b i u ↔ b.testBit l.val = true := by
              have hfin : i = ⟨lowestOne0 b n, lowestOne0_lt hb0 hvalid.2.1⟩ := Fin.ext hi_lo
              rw [hfin]
              rcases hu_eq with rfl | rfl | rfl <;> exact highMemF_lowestOne0_iff n b hb0 hvalid.2.1 l
            exact hF.symm
    | true =>
      dsimp; rw [he1, he0]
      cases hbit_i : b.testBit i.val with
      | true =>
        have hclosed_i : b.testBit i.val = true ∨ (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) :=
          Or.inl hbit_i
        rcases highMem_sp_of_testBit_true glob n b s hvalid i hi_pos hbit_i hbe with ⟨t, hti, hsp_mem⟩
        exact predVal_lt_of_highMemF_lt_of_testBit_true glob n b s hvalid t i hti hbit_i
          (.hx i) (.sp p) (highMem_hx_of_closed glob n b s hvalid i hclosed_i) hsp_mem
      | false =>
        by_cases hu_i : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < uLim0 b n
        · rcases hu_i with ⟨hb0, hi_lo, hi_u⟩
          have hle_u_lo := uLim0_le_lowestOne0 b n
          have hlo_lt := lowestOne0_lt hb0 hvalid.2.1
          have hs_lt : s < S_close0 n b := by unfold S_close0; omega
          have hbelow : sActive0 n b s = true → p.val < sTarg0 n b s := by
            intro _
            have hnot3 : ¬(b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s) := by omega
            unfold sTarg0; rw [if_neg hnot3]; dsimp [p]; omega
          set z0 : Fin n := ⟨0, hvalid.1⟩
          have hle_hy := uLim0_le_hyLim0 b n s
          have hce0 : chooseEdge1 glob n b s (.hx z0) = false := by
            rw [chooseEdge1_hx_eq]
            have h0_hy : 0 < b ∧ z0.val < lowestOne0 b n ∧ z0.val + s < hyLim0 b n s :=
              ⟨hb0, by dsimp [z0]; omega, by dsimp [z0]; omega⟩
            rw [decide_eq_true h0_hy]; simp
          have hhit_f0_ui := hitsWithTop_f_to_u_of_still glob n b s hvalid hb0 i hi_pos hi_lo hi_u
            (i.val - 1) z0 (by dsimp [z0]; omega) hi_pos
          have hhit_hx0_ui : HitsWithTop glob n b s (.hx z0) (.u i) (.k p) :=
            (hitsWithTop_hx_f_of_chooseEdge1_false glob n b s hvalid z0 hce0).1 hhit_f0_ui
              (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin, z0]; omega)
          have hhit_sp_ui : HitsWithTop glob n b s (.sp p) (.u i) (.k p) :=
            hitsWithTop_sp_of_hx_zero glob n b s hvalid hhit_hx0_ui
              (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega)
              n p (by omega) hbelow
          have hlt_hy : i.val + s < hyLim0 b n s := by omega
          have howner_u : (G_bin n).owner (.u i) = false := by
            dsimp [G_bin, owner_bin]; rw [if_neg hi0]
          have hce_u : chooseEdge1 glob n b s (.u i) = false :=
            chooseEdge1_u_of_still glob n b s hb0 i hi_lo hi_u
          have hs_u : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u i) = .h i := by
            unfold step predState0; rw [if_pos howner_u, hce_u]; rfl
          have hce_h : chooseEdge1 glob n b s (.h i) = false := by
            rw [chooseEdge1_h_eq]
            have : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s := ⟨hb0, hi_lo, hlt_hy⟩
            rw [decide_eq_true this]; simp
          have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h i) = .hx i := by
            unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
          have hhit_sp_hi : HitsWithTop glob n b s (.sp p) (.h i) (.k p) :=
            hitsWithTop_of_step_right glob n b s hvalid (.sp p) (.u i) (.h i) (.k p) (by nofun)
              hhit_sp_ui hs_u (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega)
          have hhit_sp_hxi : HitsWithTop glob n b s (.sp p) (.hx i) (.k p) :=
            hitsWithTop_of_step_right glob n b s hvalid (.sp p) (.h i) (.hx i) (.k p) (by nofun)
              hhit_sp_hi hs_h (by dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; have := i.isLt; omega)
          exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid hhit_sp_hxi (prio_k_even n p)
        · cases hce_i : chooseEdge1 glob n b s (.hx i) with
          | true =>
            apply predVal_lt_of_setLT glob n b s hvalid
            apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .z i)
            · rw [highMem_hx_of_chooseEdge1_true glob n b s hvalid i hce_i (.z i)
                (by dsimp [G_bin, priority_bin]; omega)]
              exact Or.inl rfl
            · rw [mem_sp_ge_iff_testBit glob n b s hvalid i hi_pos hu_i i le_rfl (.z i) (Or.inl rfl), hbit_i]
              decide
            · exact prio_z_odd n i
            · intro u hu
              have hp_c_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
                have : (G_bin n).priority .c < (G_bin n).priority (.z i) := by dsimp [G_bin, priority_bin]; omega
                omega
              have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
                have : (G_bin n).priority .s < (G_bin n).priority (.z i) := by dsimp [G_bin, priority_bin]; omega
                omega
              rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, hu_eq⟩
              have hil : i.val ≤ l.val := by
                rcases hu_eq with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin] at hu; omega }
              rw [mem_sp_ge_iff_testBit glob n b s hvalid i hi_pos hu_i l hil u hu_eq,
                  highMem_hx_of_chooseEdge1_true glob n b s hvalid i hce_i u hp_c_u]
              by_cases hli : l.val = i.val
              · have hl_eq : i = l := (Fin.ext hli).symm
                subst hl_eq
                have hne_zi : u ≠ .z i := by intro rfl; omega
                rcases hu_eq with rfl | rfl | rfl
                · exact False.elim (hne_zi rfl)
                · dsimp [highMemZ]; simp [hbit_i]
                · dsimp [highMemZ]; simp [hbit_i]
              · have hil_lt : i.val < l.val := by omega
                have hne_i : l ≠ i := fun h => by subst h; omega
                rcases hu_eq with rfl | rfl | rfl <;> { dsimp [highMemZ]; simp [hne_i, hil_lt] }
          | false =>
            have hnot_s2 : ¬(b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b + 2 ≤ s) := by
              rintro ⟨h1, h2, h3⟩
              rw [hbe, if_pos ⟨h1, h3⟩] at hbe_eq
              have := hbe_eq.symm; rw [decide_eq_true_eq] at this; exact this h2
            have hhy_i : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s := by
              rw [chooseEdge1_hx_eq] at hce_i
              rw [hbit_i, decide_eq_false hnot_s2] at hce_i
              simpa using hce_i
            have hle_hy := hyLim0_le_n b n s
            have hs_lt : s < S_close0 n b := by unfold S_close0; omega
            have htau_gi : chooseTauEdge1 n b s (.g i) = false := by
              dsimp [chooseTauEdge1]
              simp only [hbit_i, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
              exact ⟨by unfold S_close0 at hs_lt; omega, fun ⟨h1, h2, h3⟩ => hu_i ⟨h1, h2, by omega⟩⟩
            have hport_gi := hitsPortal_g_of_tau_false glob n b s hvalid i htau_gi
            have hs_fi : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f i) = .g i := rfl
            have hpath_fi : predPath glob n b s (.f i) = insert (.f i) (predPath glob n b s (.g i)) := by
              rw [predPath, predVal, pred_path_step glob n b s hvalid (.f i) (by nofun), hs_fi]
            apply predVal_lt_of_setLT glob n b s hvalid
            apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .f i)
            · rw [(hitsWithTop_hx_f_of_chooseEdge1_false glob n b s hvalid i hce_i).2 (.f i)
                (by dsimp [G_bin, priority_bin]; omega), hpath_fi]
              exact Finset.mem_insert_self _ _
            · rw [mem_sp_ge_iff_testBit glob n b s hvalid i hi_pos hu_i i le_rfl (.f i) (Or.inr (Or.inl rfl)),
                  hbit_i]
              decide
            · exact prio_f_odd n i
            · intro u hu
              have hp_c_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
                have : (G_bin n).priority .c < (G_bin n).priority (.f i) := by dsimp [G_bin, priority_bin]; omega
                omega
              have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
                have : (G_bin n).priority .s < (G_bin n).priority (.f i) := by dsimp [G_bin, priority_bin]; omega
                omega
              rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨l, hu_eq⟩
              have hil : i.val ≤ l.val := by
                rcases hu_eq with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin] at hu; omega }
              have hne_fi : u ≠ .f i := by intro rfl; omega
              rw [mem_sp_ge_iff_testBit glob n b s hvalid i hi_pos hu_i l hil u hu_eq,
                  (hitsWithTop_hx_f_of_chooseEdge1_false glob n b s hvalid i hce_i).2 u hp_c_u,
                  hpath_fi, Finset.mem_insert, or_iff_right hne_fi,
                  mem_portal_zfk_iff_testBit glob n b s hvalid hport_gi l (by omega) u hu_eq]

end FriedmannParity
