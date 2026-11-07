import Definitions.Def_friedmann_payoff
import Solutions.Sol_friedmann_parity_transport
import Solutions.Sol_friedmann_parity_improvement

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FriedmannParity

open scoped BigOperators

section SinkPayoffReduction

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Part 1: Optimal Counterstrategies and Two-Strategy Order Transport in 1-Sink Games -/

lemma exists_disc_sink_counterstrategy {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    ∃ ϱ : V → V,
      Legal G true ϱ ∧
      (∀ u, (playValue G σ ϱ u).cyclePriority = 1) ∧
      (∀ u, (playValue G σ ϱ u).path = (value G σ u).path) ∧
      (∀ u, FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ u =
        FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ ϱ u) ∧
      (∀ u τ, Legal G true τ →
        FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ ϱ u ≤
          FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ u) := by
  let H := FriedmannDiscounted.induced G
  have hG := isSinkGame_wellFormed hSink
  have hH := isSinkGame_wellFormed_induced hSink
  have hcp_val : ∀ u, (value G σ u).cyclePriority = 1 :=
    hSink.2.2.2.2.2.2 σ hσ hAbove
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ_star, hτ_star⟩
  have hval_eq : ∀ u, value G σ u = playValue G σ τ_star u :=
    value_eq_playValue_of_optimalCounterstrategy hG hτ_star
  have hcp_star : ∀ u, (playValue G σ τ_star u).cyclePriority = 1 := by
    intro u
    rw [← hval_eq u]
    exact hcp_val u
  rcases exists_disc_optimalCounterstrategy hH σ with ⟨ϱ, hϱ_leg, hϱ_min, hϱ_val⟩
  have hcp_ϱ : ∀ u, (playValue G σ ϱ u).cyclePriority = 1 := by
    intro u
    have hle_u : ValueLE G (playValue G σ τ_star u) (playValue G σ ϱ u) :=
      hτ_star.2 u ϱ hϱ_leg
    have hrew_ge : reward 1 ≤ reward (playValue G σ ϱ u).cyclePriority := by
      have h := reward_cyclePriority_le_of_valueLE hle_u
      rwa [hcp_star u] at h
    by_contra hne_one
    have hcl_ne : cycleLeader G σ ϱ u ≠ sink := by
      intro hcl
      apply hne_one
      rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl, isSinkGame_priority_sink hSink]
    have hneg := discounted_playValue_lt_zero_of_cyclePriority_eq_one hSink (hcp_star u)
    have hpos := zero_lt_discounted_playValue_of_cycleLeader_ne_sink hSink hrew_ge hcl_ne
    have hmin_u := hϱ_min u τ_star hτ_star.1
    linarith
  have hpath_eq : ∀ u, (playValue G σ ϱ u).path = (value G σ u).path := by
    intro u
    rw [hval_eq u]
    have hle_u : ValueLE G (playValue G σ τ_star u) (playValue G σ ϱ u) :=
      hτ_star.2 u ϱ hϱ_leg
    rcases hle_u with heq | hlt
    · rw [heq]
    · exfalso
      rw [valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_star u) (hcp_ϱ u)] at hlt
      have hlt_disc := discounted_playValue_lt_of_setLT hSink (hcp_star u) (hcp_ϱ u) hlt
      have hmin_u := hϱ_min u τ_star hτ_star.1
      linarith
  exact ⟨ϱ, hϱ_leg, hcp_ϱ, hpath_eq, hϱ_val, hϱ_min⟩

lemma sink_discounted_order_le {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v))
    (v w : V) :
    ValueLE G (value G σ v) (value G σ w) ↔
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v ≤
        FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ w := by
  have hG := isSinkGame_wellFormed hSink
  rw [valueLE_iff_not_valueLT hG.2, sink_discounted_order G ι sink hSink σ hσ hAbove w v, not_lt]

lemma sink_discounted_order_two_lt {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ σ₂ : V → V}
    (hσ₁ : Legal G false σ₁) (hAbove₁ : ∀ v, ValueLE G (value G ι v) (value G σ₁ v))
    (hσ₂ : Legal G false σ₂) (hAbove₂ : ∀ v, ValueLE G (value G ι v) (value G σ₂ v))
    (v₁ v₂ : V)
    (hlt : ValueLT G (value G σ₁ v₁) (value G σ₂ v₂)) :
    FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ₁ v₁ <
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ₂ v₂ := by
  have hG := isSinkGame_wellFormed hSink
  rcases exists_optimalCounterstrategy G hG σ₁ with ⟨τ₁, hτ₁⟩
  rcases exists_optimalCounterstrategy G hG σ₂ with ⟨τ₂, hτ₂⟩
  have hval₁ := value_eq_playValue_of_optimalCounterstrategy hG hτ₁ v₁
  have hval₂ := value_eq_playValue_of_optimalCounterstrategy hG hτ₂ v₂
  have hcp₁ : (playValue G σ₁ τ₁ v₁).cyclePriority = 1 := by
    rw [← hval₁]
    exact hSink.2.2.2.2.2.2 σ₁ hσ₁ hAbove₁ v₁
  have hcp₂ : (playValue G σ₂ τ₂ v₂).cyclePriority = 1 := by
    rw [← hval₂]
    exact hSink.2.2.2.2.2.2 σ₂ hσ₂ hAbove₂ v₂
  rw [hval₁, hval₂, valueLT_iff_setLT_of_cyclePriority_eq_one hSink hcp₁ hcp₂,
      ← hval₁, ← hval₂] at hlt
  rcases exists_disc_sink_counterstrategy hSink hσ₁ hAbove₁ with
    ⟨ϱ₁, _, hcp_ϱ₁, hpath₁, hval_disc₁, _⟩
  rcases exists_disc_sink_counterstrategy hSink hσ₂ hAbove₂ with
    ⟨ϱ₂, _, hcp_ϱ₂, hpath₂, hval_disc₂, _⟩
  rw [← hpath₁ v₁, ← hpath₂ v₂] at hlt
  rw [hval_disc₁ v₁, hval_disc₂ v₂]
  exact discounted_playValue_lt_of_setLT hSink (hcp_ϱ₁ v₁) (hcp_ϱ₂ v₂) hlt

lemma sink_discounted_order_two_le {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ σ₂ : V → V}
    (hσ₁ : Legal G false σ₁) (hAbove₁ : ∀ v, ValueLE G (value G ι v) (value G σ₁ v))
    (hσ₂ : Legal G false σ₂) (hAbove₂ : ∀ v, ValueLE G (value G ι v) (value G σ₂ v))
    (v₁ v₂ : V)
    (hle : FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ₁ v₁ ≤
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ₂ v₂) :
    ValueLE G (value G σ₁ v₁) (value G σ₂ v₂) := by
  have hG := isSinkGame_wellFormed hSink
  rw [valueLE_iff_not_valueLT hG.2]
  intro hlt
  have hlt_disc := sink_discounted_order_two_lt hSink hσ₂ hAbove₂ hσ₁ hAbove₁ v₂ v₁ hlt
  linarith

/-! ### Part 2: Policy Iteration Predicates (`Improving`, `Improvable`, `Allowed`, `Improvement`, `LocalStep`) -/

lemma value_above_of_allowed {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ ρ : V → V}
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v))
    (hal : Allowed G σ ρ) (v : V) :
    ValueLE G (value G ι v) (value G ρ v) :=
  valueLE_trans (isSinkGame_wellFormed hSink).2 (hAbove v)
    (value_le_of_allowed (isSinkGame_wellFormed hSink) hal v)

lemma improving_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v))
    (v w : V) :
    Improving G σ v w ↔
      FriedmannScalar.Improving (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v w := by
  unfold Improving FriedmannScalar.Improving
  rw [sink_discounted_order G ι sink hSink σ hσ hAbove (σ v) w]
  rfl

lemma improvable_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    Improvable G σ ↔
      FriedmannScalar.Improvable (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ := by
  unfold Improvable FriedmannScalar.Improvable
  constructor
  · rintro ⟨v, w, h⟩
    exact ⟨v, w, (improving_induced_iff hSink hσ hAbove v w).mp h⟩
  · rintro ⟨v, w, h⟩
    exact ⟨v, w, (improving_induced_iff hSink hσ hAbove v w).mpr h⟩

lemma allowed_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ ρ : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    Allowed G σ ρ ↔
      FriedmannScalar.Allowed (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ ρ := by
  unfold Allowed FriedmannScalar.Allowed
  constructor
  · rintro ⟨hρ, hal⟩
    refine ⟨hρ, fun v hv => ?_⟩
    exact (sink_discounted_order_le hSink hσ hAbove (σ v) (ρ v)).mp (hal v hv)
  · rintro ⟨hρ, hal⟩
    refine ⟨hρ, fun v hv => ?_⟩
    exact (sink_discounted_order_le hSink hσ hAbove (σ v) (ρ v)).mpr (hal v hv)

lemma improvement_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ σ' : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    Improvement G σ σ' ↔
      FriedmannScalar.Improvement
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ σ' := by
  unfold Improvement FriedmannScalar.Improvement
  rw [allowed_induced_iff hSink hσ hAbove, improvable_induced_iff hSink hσ hAbove]
  constructor
  · rintro ⟨hal, himp⟩
    refine ⟨hal, fun h => ?_⟩
    rcases himp h with ⟨v, hv, hlt⟩
    exact ⟨v, hv, (sink_discounted_order G ι sink hSink σ hσ hAbove (σ v) (σ' v)).mp hlt⟩
  · rintro ⟨hal, himp⟩
    refine ⟨hal, fun h => ?_⟩
    rcases himp h with ⟨v, hv, hlt⟩
    exact ⟨v, hv, (sink_discounted_order G ι sink hSink σ hσ hAbove (σ v) (σ' v)).mpr hlt⟩

lemma localStep_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ σ' : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    LocalStep G σ σ' ↔
      FriedmannScalar.LocalStep
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ σ' := by
  unfold LocalStep FriedmannScalar.LocalStep
  rw [improvement_induced_iff hSink hσ hAbove]
  constructor
  · rintro ⟨himp, hloc⟩
    refine ⟨himp, fun v w hv hvw => ?_⟩
    exact (sink_discounted_order_le hSink hσ hAbove w (σ' v)).mp (hloc v w hv hvw)
  · rintro ⟨himp, hloc⟩
    refine ⟨himp, fun v w hv hvw => ?_⟩
    exact (sink_discounted_order_le hSink hσ hAbove w (σ' v)).mpr (hloc v w hv hvw)

/-! ### Part 3: Equivalence of `GlobalStep` -/

lemma discounted_value_le_of_step_le {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (ρ σ' : V → V)
    (hstep : ∀ u, H.arena.owner u = false →
      FriedmannScalar.value (FriedmannDiscounted.model H) σ' (ρ u) ≤
        FriedmannScalar.value (FriedmannDiscounted.model H) σ' (σ' u))
    (v : V) :
    FriedmannScalar.value (FriedmannDiscounted.model H) ρ v ≤
      FriedmannScalar.value (FriedmannDiscounted.model H) σ' v := by
  rcases exists_disc_optimalCounterstrategy hH σ' with ⟨ϱ, hϱ_leg, _, hϱ_val⟩
  rcases exists_disc_optimalCounterstrategy hH ρ with ⟨ϱ_ρ, _, hϱ_ρ_min, hϱ_ρ_val⟩
  have hle_ρ : FriedmannScalar.value (FriedmannDiscounted.model H) ρ v ≤
      FriedmannDiscounted.playValue H ρ ϱ v := by
    rw [hϱ_ρ_val v]
    exact hϱ_ρ_min v ϱ hϱ_leg
  suffices h : FriedmannDiscounted.playValue H ρ ϱ v ≤
      FriedmannDiscounted.playValue H σ' ϱ v by
    rw [hϱ_val v]
    exact le_trans hle_ρ h
  let f : V → ℚ := fun u =>
    FriedmannDiscounted.playValue H ρ ϱ u - FriedmannDiscounted.playValue H σ' ϱ u
  have hβ0 : 0 < H.discount := hH.2.1
  have hβ1 : H.discount < 1 := hH.2.2
  have hf_step : ∀ u, f u ≤ H.discount * f (step H.arena ρ ϱ u) := by
    intro u
    have h1 := discounted_playValue_step hH ρ ϱ u
    have h2 := discounted_playValue_step hH σ' ϱ u
    have hstep_u : FriedmannDiscounted.playValue H σ' ϱ (step H.arena ρ ϱ u) ≤
        FriedmannDiscounted.playValue H σ' ϱ (step H.arena σ' ϱ u) := by
      unfold step
      split_ifs with hu
      · rw [← hϱ_val (ρ u), ← hϱ_val (σ' u)]
        exact hstep u hu
      · exact le_rfl
    dsimp only [f]
    nlinarith
  have hne : (Finset.univ : Finset V).Nonempty := ⟨v, Finset.mem_univ v⟩
  set M_sup := Finset.univ.sup' hne f
  have hle_M : ∀ u, f u ≤ M_sup :=
    fun u => Finset.le_sup' f (Finset.mem_univ u)
  obtain ⟨u₀, _, hu₀⟩ := Finset.exists_mem_eq_sup' hne f
  have hM_step : M_sup ≤ H.discount * M_sup := by
    calc M_sup = f u₀ := hu₀
      _ ≤ H.discount * f (step H.arena ρ ϱ u₀) := hf_step u₀
      _ ≤ H.discount * M_sup := mul_le_mul_of_nonneg_left (hle_M _) (le_of_lt hβ0)
  have hM_nonpos : M_sup ≤ 0 := by nlinarith
  have hv := hle_M v
  dsimp only [f] at hv
  linarith

lemma owner_false_sink_apply_eq_sink {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {π : V → V}
    (hπ : Legal G false π) (hAbove : ∀ v, ValueLE G (value G ι v) (value G π v))
    (hsink_owner : G.owner sink = false) :
    π sink = sink := by
  have hG := isSinkGame_wellFormed hSink
  rcases exists_optimalCounterstrategy G hG π with ⟨τ, hτ⟩
  have hcp : (playValue G π τ sink).cyclePriority = 1 := by
    rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ sink]
    exact hSink.2.2.2.2.2.2 π hπ hAbove sink
  have hstep := step_sink_eq_sink_of_cyclePriority_eq_one hSink hcp
  unfold step at hstep
  rw [if_pos hsink_owner] at hstep
  exact hstep

lemma value_step_le_of_globalStep_parity {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ σ' : V → V}
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v))
    (hglob : GlobalStep G σ σ')
    {v w : V} (hv : G.owner v = false) (hvw : G.edge v w)
    (hal_vw : ValueLE G (value G σ (σ v)) (value G σ w)) :
    ValueLE G (value G σ' w) (value G σ' (σ' v)) := by
  have hG := isSinkGame_wellFormed hSink
  rw [valueLE_iff_not_valueLT hG.2]
  intro hlt
  let ρ : V → V := Function.update σ' v w
  have hρ_leg : Legal G false ρ := by
    intro u hu
    dsimp only [ρ]
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self]
      exact hvw
    · rw [Function.update_of_ne huv]
      exact hglob.1.1.1 u hu
  have hρ_al_σ : Allowed G σ ρ := by
    refine ⟨hρ_leg, fun u hu => ?_⟩
    dsimp only [ρ]
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self]
      exact hal_vw
    · rw [Function.update_of_ne huv]
      exact hglob.1.1.2 u hu
  have hρ_al_σ' : Allowed G σ' ρ := by
    refine ⟨hρ_leg, fun u hu => ?_⟩
    dsimp only [ρ]
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self]
      exact Or.inr hlt
    · rw [Function.update_of_ne huv]
      exact valueLE_refl G _
  have hAbove_σ' : ∀ u, ValueLE G (value G ι u) (value G σ' u) :=
    value_above_of_allowed hSink hAbove hglob.1.1
  have hAbove_ρ : ∀ u, ValueLE G (value G ι u) (value G ρ u) :=
    value_above_of_allowed hSink hAbove hρ_al_σ
  have hle_σ'_ρ : ∀ u, ValueLE G (value G σ' u) (value G ρ u) :=
    value_le_of_allowed hG hρ_al_σ'
  have hcp_σ' : ∀ u, (value G σ' u).cyclePriority = 1 :=
    hSink.2.2.2.2.2.2 σ' hglob.1.1.1 hAbove_σ'
  have hpv : G.priority v ≠ (value G σ' (σ' v)).cyclePriority := by
    rw [hcp_σ' (σ' v), ne_eq, isSinkGame_priority_eq_one_iff hSink v]
    rintro rfl
    have h1 := owner_false_sink_apply_eq_sink hSink hglob.1.1.1 hAbove_σ' hv
    have h2 := owner_false_sink_apply_eq_sink hSink hρ_leg hAbove_ρ hv
    dsimp only [ρ] at h2
    rw [Function.update_self] at h2
    rw [h1, h2] at hlt
    exact valueLT_irrefl hG.2 _ hlt
  have hlt_ρ : ValueLT G (value G σ' (σ' v)) (value G σ' (ρ v)) := by
    dsimp only [ρ]
    rw [Function.update_self]
    exact hlt
  have hlt_v : ValueLT G (value G σ' v) (value G ρ v) :=
    value_lt_of_improving_of_priority_ne_cyclePriority hG hle_σ'_ρ hv hlt_ρ hpv
  have hle_v : ValueLE G (value G ρ v) (value G σ' v) :=
    hglob.2 ρ hρ_al_σ v
  exact (valueLE_iff_not_valueLT hG.2 _ _).mp hle_v hlt_v

lemma globalStep_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ σ' : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    GlobalStep G σ σ' ↔
      FriedmannScalar.GlobalStep
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ σ' := by
  let H := FriedmannDiscounted.induced G
  let M := FriedmannDiscounted.model H
  have hH := isSinkGame_wellFormed_induced hSink
  constructor
  · intro hglob
    have himp_M : FriedmannScalar.Improvement M σ σ' :=
      (improvement_induced_iff hSink hσ hAbove).mp hglob.1
    have hAbove_σ' : ∀ u, ValueLE G (value G ι u) (value G σ' u) :=
      value_above_of_allowed hSink hAbove hglob.1.1
    refine ⟨himp_M, fun ρ hρ_M v => ?_⟩
    have hρ : Allowed G σ ρ := (allowed_induced_iff hSink hσ hAbove).mpr hρ_M
    apply discounted_value_le_of_step_le hH ρ σ' _ v
    intro u hu
    have hle_G : ValueLE G (value G σ' (ρ u)) (value G σ' (σ' u)) :=
      value_step_le_of_globalStep_parity hSink hAbove hglob hu (hρ.1 u hu) (hρ.2 u hu)
    exact (sink_discounted_order_le hSink hglob.1.1.1 hAbove_σ' (ρ u) (σ' u)).mp hle_G
  · rintro ⟨himp_M, hglob_M⟩
    have himp_G : Improvement G σ σ' :=
      (improvement_induced_iff hSink hσ hAbove).mpr himp_M
    have hAbove_σ' : ∀ u, ValueLE G (value G ι u) (value G σ' u) :=
      value_above_of_allowed hSink hAbove himp_G.1
    refine ⟨himp_G, fun ρ hρ_G v => ?_⟩
    have hAbove_ρ : ∀ u, ValueLE G (value G ι u) (value G ρ u) :=
      value_above_of_allowed hSink hAbove hρ_G
    have hρ_M : FriedmannScalar.Allowed M σ ρ :=
      (allowed_induced_iff hSink hσ hAbove).mp hρ_G
    exact sink_discounted_order_two_le hSink hρ_G.1 hAbove_ρ himp_G.1.1 hAbove_σ' v v
      (hglob_M ρ hρ_M v)

lemma rule_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) {σ σ' : V → V}
    (hσ : Legal G false σ) (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) :
    (if global then GlobalStep G else LocalStep G) σ σ' ↔
      FriedmannScalar.rule
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) global σ σ' := by
  unfold FriedmannScalar.rule
  cases global
  · exact localStep_induced_iff hSink hσ hAbove
  · exact globalStep_induced_iff hSink hσ hAbove

/-! ### Part 4: Equivalence of `CompleteRun`, `HardInstance`, and Exponential Reduction -/

lemma allowed_of_rule_parity {G : Game V} (global : Bool) {σ σ' : V → V}
    (h : (if global then GlobalStep G else LocalStep G) σ σ') :
    Allowed G σ σ' := by
  cases global
  · exact h.1.1
  · exact h.1.1

lemma allowed_of_rule_scalar {M : FriedmannScalar.Model V} (global : Bool) {σ σ' : V → V}
    (h : FriedmannScalar.rule M global σ σ') :
    FriedmannScalar.Allowed M σ σ' := by
  unfold FriedmannScalar.rule at h
  cases global
  · exact h.1.1
  · exact h.1.1

lemma value_above_of_completeRun_parity {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) {T : ℕ} {run : ℕ → (V → V)}
    (hrun : CompleteRun G (if global then GlobalStep G else LocalStep G) ι T run) :
    ∀ t ≤ T, ∀ v, ValueLE G (value G ι v) (value G (run t) v) := by
  intro t
  induction t with
  | zero =>
    intro _ v
    rw [hrun.1]
    exact valueLE_refl G _
  | succ t ih =>
    intro ht v
    have hAbove_t := ih (le_of_lt ht)
    have hstep := (hrun.2.2.1 t ht).2
    have hal := allowed_of_rule_parity global hstep
    exact value_above_of_allowed hSink hAbove_t hal v

lemma value_above_of_completeRun_induced {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) {T : ℕ} {run : ℕ → (V → V)}
    (hrun : FriedmannScalar.CompleteRun
      (FriedmannDiscounted.model (FriedmannDiscounted.induced G))
      (FriedmannScalar.rule (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) global)
      ι T run) :
    ∀ t ≤ T, ∀ v, ValueLE G (value G ι v) (value G (run t) v) := by
  intro t
  induction t with
  | zero =>
    intro _ v
    rw [hrun.1]
    exact valueLE_refl G _
  | succ t ih =>
    intro ht v
    have hAbove_t := ih (le_of_lt ht)
    have hleg_t : Legal G false (run t) := hrun.2.1 t (le_of_lt ht)
    have hstep := (hrun.2.2.1 t ht).2
    have hal_M := allowed_of_rule_scalar global hstep
    have hal_G : Allowed G (run t) (run (t + 1)) :=
      (allowed_induced_iff hSink hleg_t hAbove_t).mpr hal_M
    exact value_above_of_allowed hSink hAbove_t hal_G v

lemma completeRun_induced_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) (T : ℕ) (run : ℕ → (V → V)) :
    CompleteRun G (if global then GlobalStep G else LocalStep G) ι T run ↔
      FriedmannScalar.CompleteRun
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G))
        (FriedmannScalar.rule (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) global)
        ι T run := by
  constructor
  · intro hrun
    have hAbove := value_above_of_completeRun_parity hSink global hrun
    rcases hrun with ⟨h0, hleg, hstep, hterm⟩
    refine ⟨h0, hleg, ?_, ?_⟩
    · intro t ht
      have hleg_t := hleg t (le_of_lt ht)
      have hAbove_t := hAbove t (le_of_lt ht)
      rw [← improvable_induced_iff hSink hleg_t hAbove_t,
          ← rule_induced_iff hSink global hleg_t hAbove_t]
      exact hstep t ht
    · have hleg_T := hleg T le_rfl
      have hAbove_T := hAbove T le_rfl
      rw [← improvable_induced_iff hSink hleg_T hAbove_T]
      exact hterm
  · intro hrun
    have hAbove := value_above_of_completeRun_induced hSink global hrun
    rcases hrun with ⟨h0, hleg, hstep, hterm⟩
    refine ⟨h0, hleg, ?_, ?_⟩
    · intro t ht
      have hleg_t : Legal G false (run t) := hleg t (le_of_lt ht)
      have hAbove_t := hAbove t (le_of_lt ht)
      rw [improvable_induced_iff hSink hleg_t hAbove_t,
          rule_induced_iff hSink global hleg_t hAbove_t]
      exact hstep t ht
    · have hleg_T : Legal G false (run T) := hleg T le_rfl
      have hAbove_T := hAbove T le_rfl
      rw [improvable_induced_iff hSink hleg_T hAbove_T]
      exact hterm

theorem hardInstance_induced_of_isSinkGame {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (global : Bool) (iterations : ℕ)
    (hHard : HardInstance G ι (if global then GlobalStep G else LocalStep G) iterations) :
    FriedmannDiscounted.WellFormed (FriedmannDiscounted.induced G) ∧
      FriedmannScalar.HardInstance
        (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) ι
        (FriedmannScalar.rule (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) global)
        iterations := by
  refine ⟨isSinkGame_wellFormed_induced hSink, ?_⟩
  rcases hHard with ⟨_, hι, ⟨T₀, run₀, hrun₀⟩, hbound⟩
  refine ⟨hι, ⟨T₀, run₀, (completeRun_induced_iff hSink global T₀ run₀).mp hrun₀⟩, ?_⟩
  intro T run hrun
  exact hbound T run ((completeRun_induced_iff hSink global T run).mpr hrun)

theorem exponential_payoff_of_sink_family
    (hFamily : ∃ C : ℕ, 0 < C ∧ ∀ global : Bool, ∀ n : ℕ, 0 < n →
      ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N, ∃ sink : Fin N,
        edgeCount G ≤ C * n ∧
        IsSinkGame G ι sink ∧
        HardInstance G ι (if global then GlobalStep G else LocalStep G) (2 ^ n)) :
    FriedmannDiscounted.Exponential ∧
      FriedmannDiscounted.ExponentialMeanViaReduction := by
  rcases hFamily with ⟨C, hC, hExp⟩
  constructor
  · refine ⟨C, hC, ?_⟩
    intro global n hn
    rcases hExp global n hn with ⟨N, G, ι, sink, hedge, hSink, hHard⟩
    have hind := hardInstance_induced_of_isSinkGame hSink global (2 ^ n) hHard
    exact ⟨N, FriedmannDiscounted.induced G, ι, hind.1, hedge, hind.2⟩
  · refine ⟨C, hC, ?_⟩
    intro global n hn
    rcases hExp global n hn with ⟨N, G, ι, sink, hedge, hSink, hHard⟩
    have hind := hardInstance_induced_of_isSinkGame hSink global (2 ^ n) hHard
    exact ⟨N, G, ι, hSink.1, hedge, hind.1, hind.2⟩

end SinkPayoffReduction

end FriedmannParity
