import Solutions.Sol_friedmann_parity_binary_arena
import Solutions.Sol_friedmann_parity_binary_sink

set_option autoImplicit false
set_option linter.unusedVariables false

namespace FriedmannParity

/-! ### Part 1: Bit and Step Index Helpers (0-based) -/

def lowestZero0 (b n : ℕ) : ℕ :=
  ((List.range n).find? (fun i => !b.testBit i)).getD n

def lowestOne0 (b n : ℕ) : ℕ :=
  ((List.range n).find? (fun i => b.testBit i)).getD n

def hasHigherOne0 (b n i : ℕ) : Bool :=
  (List.range n).any (fun j => decide (i < j) && b.testBit j)

lemma hasHigherOne0_iff (b n i : ℕ) :
    hasHigherOne0 b n i = true ↔ ∃ j, i < j ∧ j < n ∧ b.testBit j = true := by
  unfold hasHigherOne0
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hcond⟩
    rw [List.mem_range] at hj
    rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact ⟨j, hcond.1, hj, hcond.2⟩
  · rintro ⟨j, hij, hjn, hbit⟩
    refine ⟨j, List.mem_range.mpr hjn, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hij, hbit⟩

lemma hasHigherOne0_eq_false_iff (b n i : ℕ) :
    hasHigherOne0 b n i = false ↔ ∀ j, i < j → j < n → b.testBit j = false := by
  constructor
  · intro h j hij hjn
    by_contra hbit
    have htrue : b.testBit j = true := Bool.eq_true_of_not_eq_false hbit
    have hhi : hasHigherOne0 b n i = true := (hasHigherOne0_iff b n i).mpr ⟨j, hij, hjn, htrue⟩
    rw [h] at hhi
    contradiction
  · intro hall
    by_contra hne
    have htrue : hasHigherOne0 b n i = true := Bool.eq_true_of_not_eq_false hne
    rcases (hasHigherOne0_iff b n i).mp htrue with ⟨j, hij, hjn, hbit⟩
    have hfalse := hall j hij hjn
    rw [hbit] at hfalse
    contradiction

lemma find?_range_some_spec {p : ℕ → Bool} :
    ∀ {n k : ℕ}, (List.range n).find? p = some k →
      k < n ∧ p k = true ∧ ∀ i < k, p i = false
  | 0, k, h => by simp at h
  | n + 1, k, h => by
    rw [List.range_succ, List.find?_append] at h
    cases hfind : (List.range n).find? p with
    | some k' =>
      rw [hfind, Option.some_or] at h
      injection h with hk
      subst hk
      rcases find?_range_some_spec hfind with ⟨hlt, hpk, hall⟩
      exact ⟨Nat.lt_succ_of_lt hlt, hpk, hall⟩
    | none =>
      rw [hfind, Option.none_or] at h
      simp only [List.find?_cons, List.find?_nil] at h
      cases hpn : p n with
      | true =>
        rw [hpn] at h
        injection h with hk
        subst hk
        have hall : ∀ i < n, p i = false := by
          intro i hi
          exact Bool.eq_false_iff.mpr (List.find?_eq_none.mp hfind i (List.mem_range.mpr hi))
        exact ⟨Nat.lt_succ_self n, hpn, hall⟩
      | false =>
        rw [hpn] at h
        contradiction

lemma find_range_getD_le (p : ℕ → Bool) (n : ℕ) :
    ((List.range n).find? p).getD n ≤ n := by
  cases h : (List.range n).find? p with
  | none => simp
  | some k =>
    simp only [Option.getD_some]
    exact le_of_lt (find?_range_some_spec h).1

lemma find_range_getD_spec {p : ℕ → Bool} {n : ℕ} (hex : ∃ i < n, p i = true) :
    let k := ((List.range n).find? p).getD n
    k < n ∧ p k = true ∧ ∀ i < k, p i = false := by
  rcases hex with ⟨i, hi, hpi⟩
  cases h : (List.range n).find? p with
  | none =>
    exfalso
    exact List.find?_eq_none.mp h i (List.mem_range.mpr hi) hpi
  | some k =>
    dsimp only
    rw [Option.getD_some]
    exact find?_range_some_spec h

lemma find_range_getD_le_of_true {p : ℕ → Bool} {n i : ℕ} (hi : i < n) (hpi : p i = true) :
    ((List.range n).find? p).getD n ≤ i := by
  rcases find_range_getD_spec ⟨i, hi, hpi⟩ with ⟨_, _, hall⟩
  by_contra hlt
  have hfalse := hall i (by omega)
  rw [hpi] at hfalse
  contradiction

lemma testBit_zero_eq (b : ℕ) : b.testBit 0 = decide (b % 2 = 1) := by
  rw [Nat.testBit_zero]

lemma exists_testBit_false_of_lt_two_pow_sub_one :
    ∀ (n b : ℕ), b < 2 ^ n - 1 → ∃ i < n, b.testBit i = false
  | 0, b, h => by simp at h
  | n + 1, b, h => by
    cases h0 : b.testBit 0 with
    | false => exact ⟨0, Nat.zero_lt_succ n, h0⟩
    | true =>
      rw [testBit_zero_eq, decide_eq_true_eq] at h0
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      have hdiv : b / 2 < 2 ^ n - 1 := by omega
      rcases exists_testBit_false_of_lt_two_pow_sub_one n (b / 2) hdiv with ⟨i, hi, hbit⟩
      refine ⟨i + 1, Nat.succ_lt_succ hi, ?_⟩
      rw [Nat.testBit_succ]
      exact hbit

lemma exists_testBit_true_of_pos_of_lt_two_pow :
    ∀ (n b : ℕ), 0 < b → b < 2 ^ n → ∃ i < n, b.testBit i = true
  | 0, b, hb0, hbn => by simp at hbn; omega
  | n + 1, b, hb0, hbn => by
    cases h0 : b.testBit 0 with
    | true => exact ⟨0, Nat.zero_lt_succ n, h0⟩
    | false =>
      rw [testBit_zero_eq, decide_eq_false_iff_not] at h0
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      have hdiv0 : 0 < b / 2 := by omega
      have hdivn : b / 2 < 2 ^ n := by omega
      rcases exists_testBit_true_of_pos_of_lt_two_pow n (b / 2) hdiv0 hdivn with ⟨i, hi, hbit⟩
      refine ⟨i + 1, Nat.succ_lt_succ hi, ?_⟩
      rw [Nat.testBit_succ]
      exact hbit

lemma lowestZero0_le (b n : ℕ) : lowestZero0 b n ≤ n :=
  find_range_getD_le _ n

lemma lowestOne0_le (b n : ℕ) : lowestOne0 b n ≤ n :=
  find_range_getD_le _ n

lemma lowestZero0_spec {b n : ℕ} (hb : b < 2 ^ n - 1) :
    lowestZero0 b n < n ∧
    b.testBit (lowestZero0 b n) = false ∧
    ∀ i < lowestZero0 b n, b.testBit i = true := by
  unfold lowestZero0
  rcases exists_testBit_false_of_lt_two_pow_sub_one n b hb with ⟨i, hi, hbit⟩
  have hex : ∃ i < n, (!b.testBit i) = true := ⟨i, hi, by simp [hbit]⟩
  rcases find_range_getD_spec hex with ⟨hlt, hpk, hall⟩
  refine ⟨hlt, by simpa using hpk, ?_⟩
  intro j hj
  have hj' := hall j hj
  simpa using hj'

lemma lowestZero0_lt {b n : ℕ} (hb : b < 2 ^ n - 1) : lowestZero0 b n < n :=
  (lowestZero0_spec hb).1

lemma testBit_lowestZero0 {b n : ℕ} (hb : b < 2 ^ n - 1) :
    b.testBit (lowestZero0 b n) = false :=
  (lowestZero0_spec hb).2.1

lemma testBit_of_lt_lowestZero0 {b n i : ℕ} (hb : b < 2 ^ n - 1) (hi : i < lowestZero0 b n) :
    b.testBit i = true :=
  (lowestZero0_spec hb).2.2 i hi

lemma lowestZero0_le_of_testBit_false {b n i : ℕ} (hi : i < n) (hbit : b.testBit i = false) :
    lowestZero0 b n ≤ i :=
  find_range_getD_le_of_true hi (by simp [hbit])

lemma lowestOne0_spec {b n : ℕ} (hb0 : 0 < b) (hbn : b < 2 ^ n) :
    lowestOne0 b n < n ∧
    b.testBit (lowestOne0 b n) = true ∧
    ∀ i < lowestOne0 b n, b.testBit i = false := by
  unfold lowestOne0
  exact find_range_getD_spec (exists_testBit_true_of_pos_of_lt_two_pow n b hb0 hbn)

lemma lowestOne0_lt {b n : ℕ} (hb0 : 0 < b) (hbn : b < 2 ^ n) : lowestOne0 b n < n :=
  (lowestOne0_spec hb0 hbn).1

lemma testBit_lowestOne0 {b n : ℕ} (hb0 : 0 < b) (hbn : b < 2 ^ n) :
    b.testBit (lowestOne0 b n) = true :=
  (lowestOne0_spec hb0 hbn).2.1

lemma testBit_of_lt_lowestOne0 {b n i : ℕ} (hb0 : 0 < b) (hbn : b < 2 ^ n) (hi : i < lowestOne0 b n) :
    b.testBit i = false :=
  (lowestOne0_spec hb0 hbn).2.2 i hi

lemma lowestOne0_le_of_testBit_true {b n i : ℕ} (hi : i < n) (hbit : b.testBit i = true) :
    lowestOne0 b n ≤ i :=
  find_range_getD_le_of_true hi hbit

def S_close0 (n b : ℕ) : ℕ :=
  3 * (n + 2 * lowestZero0 b n + 1) + 2

def maxStep0 (n b : ℕ) : ℕ :=
  if b < 2 ^ n - 1 then 3 * n + 6 * (lowestZero0 b n + 1) + 3 else 9 * n - 3

lemma maxStep0_of_lt {n b : ℕ} (hb : b < 2 ^ n - 1) :
    maxStep0 n b = S_close0 n b + 4 := by
  unfold maxStep0 S_close0
  rw [if_pos hb]
  omega

def ValidState (n b s : ℕ) : Prop :=
  0 < n ∧ b < 2 ^ n ∧ s < maxStep0 n b

def topFlip0 (b n : ℕ) : Bool :=
  decide (0 < b ∧ b = 2 ^ lowestOne0 b n)

def uLim0 (b n : ℕ) : ℕ :=
  if topFlip0 b n then lowestOne0 b n - 1 else lowestOne0 b n

def hyLim0 (b n s : ℕ) : ℕ :=
  if topFlip0 b n ∧ 1 ≤ s then lowestOne0 b n - 1 else lowestOne0 b n

def d3Cut0 (b n : ℕ) : ℕ :=
  if topFlip0 b n then lowestOne0 b n else lowestOne0 b n + 1

def rActive0 (n b s : ℕ) : Bool :=
  decide (0 < b ∨ (b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s))

def rTarg0 (n b s : ℕ) : ℕ :=
  if b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s then lowestZero0 b n else lowestOne0 b n

def sActive0 (n b s : ℕ) : Bool :=
  decide (0 < b ∨ (b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s))

def sTarg0 (n b s : ℕ) : ℕ :=
  if b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s then lowestZero0 b n else lowestOne0 b n

/-! ### Part 2: Strategy `predState0` and Counterstrategy `predTau0` -/

def chooseEdge1 (glob : Bool) (n b s : ℕ) : V_bin n → Bool
  | .x | .r_2_odd | .r_a | .c_odd | .c | .b _ | .g _ | .f _ | .k _ => false
  | .a j =>
      if b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) then false
      else
        let s_a := if b < 2 ^ n - 1 ∧ glob = true then min s (S_close0 n b) else s
        decide (1 ≤ j.val ∧ j.val < 3 * (3 * n - 1) - 1 ∧ j.val ≤ s_a + 1)
  | .l1 m =>
      if m.val = 0 then false
      else if b < 2 ^ n - 1 ∧ glob = false ∧ s = S_close0 n b + 2 then true
      else if b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 then false
      else
        let s_eff := if b < 2 ^ n - 1 ∧ glob = true ∧ s = S_close0 n b + 2 then S_close0 n b + 1 else s
        decide (3 * m.val ≤ s_eff + 1)
  | .l3 m =>
      if b < 2 ^ n - 1 ∧ glob = false ∧ s = S_close0 n b + 2 then true
      else if b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 then false
      else
        let s_eff := if b < 2 ^ n - 1 ∧ glob = true ∧ s = S_close0 n b + 2 then S_close0 n b + 1 else s
        if m.val = 0 then decide (1 ≤ s_eff) else decide (3 * m.val ≤ s_eff)
  | .l2 m =>
      if b < 2 ^ n - 1 ∧ glob = false ∧ s = S_close0 n b + 2 then true
      else if b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 then false
      else
        let s_eff := if b < 2 ^ n - 1 ∧ glob = true ∧ s = S_close0 n b + 2 then S_close0 n b + 1 else s
        if m.val = 0 then decide (2 ≤ s_eff) else decide (3 * m.val + 1 ≤ s_eff)
  | .lp1 m =>
      if m.val = 0 then true
      else if b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 then
        if glob = false then false else decide (S_close0 n b + 1 < 3 * m.val)
      else
        let s_eff := if b < 2 ^ n - 1 ∧ glob = true ∧ s = S_close0 n b + 2 then S_close0 n b + 1 else s
        decide (s_eff < 3 * m.val)
  | .lp3 m =>
      if m.val = 0 then true
      else if b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 then
        if glob = false then false else decide (S_close0 n b + 2 < 3 * m.val + 1)
      else
        decide (s < 3 * m.val + 1)
  | .lp2 m =>
      if m.val = 0 then true
      else if b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 then
        if glob = false then false else decide (S_close0 n b + 1 < 3 * m.val + 2)
      else
        let s_eff := if b < 2 ^ n - 1 ∧ glob = true ∧ s = S_close0 n b + 2 then S_close0 n b + 1 else s
        decide (s_eff < 3 * m.val + 2)
  | .r_2 =>
      decide (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
  | .r =>
      rActive0 n b s
  | .s =>
      sActive0 n b s
  | .d1 i =>
      let T_i := 3 * (n + 2 * i.val + 1)
      if b.testBit i.val then
        if b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 3 then glob else true
      else
        if T_i ≤ s then true
        else if glob then decide (0 < b ∧ i.val < lowestOne0 b n ∧ s = 0)
        else if s % 3 = 0 then decide (0 < s ∨ 0 < b)
        else false
  | .d2 i =>
      let T_i := 3 * (n + 2 * i.val + 1)
      if b.testBit i.val then
        if b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 3 then false else true
      else
        if T_i + 2 ≤ s then true
        else if T_i ≤ s then false
        else if glob then false
        else decide (s % 3 = 2)
  | .d3 i =>
      let T_i := 3 * (n + 2 * i.val + 1)
      if b.testBit i.val then
        if b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 3 then false else true
      else
        if T_i + 1 ≤ s then true
        else if s = T_i then false
        else if glob then false
        else if s % 3 = 1 then
          decide ¬(0 < b ∧ i.val + 1 + s < d3Cut0 b n)
        else false
  | .rp i =>
      if i.val = 0 then true
      else if b < 2 ^ n - 1 ∧ S_close0 n b + 1 ≤ s then decide (i.val ≠ lowestZero0 b n)
      else decide ¬(0 < b ∧ i.val = lowestOne0 b n)
  | .sp i =>
      if i.val = 0 then true
      else if b < 2 ^ n - 1 ∧ S_close0 n b + 3 ≤ s then decide (i.val ≠ lowestZero0 b n)
      else decide ¬(0 < b ∧ i.val = lowestOne0 b n)
  | .hy i =>
      if b.testBit i.val then false
      else if 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s then false
      else if b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n then decide (s < S_close0 n b + 1)
      else true
  | .hx i =>
      if b.testBit i.val then false
      else if 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s then false
      else if b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n then decide (s < S_close0 n b + 2)
      else true
  | .h i =>
      if b.testBit i.val then false
      else if 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < hyLim0 b n s then false
      else if b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n then decide (s < S_close0 n b + 3)
      else true
  | .z i =>
      decide (i.val + 1 < n) && hasHigherOne0 b n i.val
  | .u i =>
      if i.val = 0 ∨ ¬(i.val + 1 < n) then false
      else if b.testBit i.val ∨ !hasHigherOne0 b n i.val then false
      else if 0 < b ∧ i.val < lowestOne0 b n then decide ¬(i.val + s < uLim0 b n)
      else true

def chooseTauEdge1 (n b s : ℕ) : V_bin n → Bool
  | .g i =>
      let T_i := 3 * (n + 2 * i.val + 1)
      b.testBit i.val || decide (T_i + 2 ≤ s) ||
        decide (0 < b ∧ i.val < lowestOne0 b n ∧ i.val + 1 + s < uLim0 b n)
  | _ => false

def predState0 (glob : Bool) (n b s : ℕ) (v : V_bin n) : V_bin n :=
  if chooseEdge1 glob n b s v then edge1 n v else edge0 n v

def predTau0 (n b s : ℕ) (v : V_bin n) : V_bin n :=
  if chooseTauEdge1 n b s v then edge1 n v else edge0 n v

lemma predState0_legal (glob : Bool) (n b s : ℕ) :
    Legal (G_bin n) false (predState0 glob n b s) := by
  intro v _; unfold predState0 G_bin; split_ifs <;> simp

lemma predTau0_legal (n b s : ℕ) :
    Legal (G_bin n) true (predTau0 n b s) := by
  intro v _; unfold predTau0 G_bin; split_ifs <;> simp

lemma hasHigherOne0_zero (n i : ℕ) : hasHigherOne0 0 n i = false := by
  rw [hasHigherOne0_eq_false_iff]
  intro j _ _
  exact Nat.zero_testBit j

lemma predState0_zero_eq_init_all (glob : Bool) (n : ℕ) (hn : 0 < n) (v : V_bin n) :
    predState0 glob n 0 0 v = ι_bin n v := by
  cases v with
  | a j =>
    have hj := j.isLt
    have hce : chooseEdge1 glob n 0 0 (.a j) = decide (j.val = 1) := by
      dsimp [chooseEdge1, S_close0]
      split_ifs <;> (try rw [Bool.eq_iff_iff]) <;> simp_all <;> omega
    unfold predState0
    rw [hce]
    dsimp [edge0, edge1, ι_bin]
    split_ifs <;> try rfl
    all_goals (simp_all; try omega)
  | d1 i =>
    have hce : chooseEdge1 glob n 0 0 (.d1 i) = false := by
      dsimp [chooseEdge1, S_close0]; rw [Nat.zero_testBit]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | d2 i =>
    have hce : chooseEdge1 glob n 0 0 (.d2 i) = false := by
      dsimp [chooseEdge1, S_close0]; rw [Nat.zero_testBit]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | d3 i =>
    have hce : chooseEdge1 glob n 0 0 (.d3 i) = false := by
      dsimp [chooseEdge1, S_close0]; rw [Nat.zero_testBit]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | z i =>
    have hce : chooseEdge1 glob n 0 0 (.z i) = false := by
      dsimp [chooseEdge1]; rw [hasHigherOne0_zero, Bool.and_false]
    unfold predState0; rw [hce]; rfl
  | u i =>
    have hce : chooseEdge1 glob n 0 0 (.u i) = false := by
      dsimp [chooseEdge1]; rw [Nat.zero_testBit, hasHigherOne0_zero]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | hy i =>
    have hce : chooseEdge1 glob n 0 0 (.hy i) = true := by
      dsimp [chooseEdge1, S_close0]; rw [Nat.zero_testBit]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | hx i =>
    have hce : chooseEdge1 glob n 0 0 (.hx i) = true := by
      dsimp [chooseEdge1, S_close0]; rw [Nat.zero_testBit]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | h i =>
    have hce : chooseEdge1 glob n 0 0 (.h i) = true := by
      dsimp [chooseEdge1, S_close0]; rw [Nat.zero_testBit]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | l1 m =>
    have hm := m.isLt
    have h2 : ¬(0 = S_close0 n 0 + 2) := by unfold S_close0; omega
    have h3 : ¬(0 = S_close0 n 0 + 3) := by unfold S_close0; omega
    have hce : chooseEdge1 glob n 0 0 (.l1 m) = false := by
      simp only [chooseEdge1, h2, h3, and_false, ite_false]
      split_ifs; try rfl
      simp only [decide_eq_false_iff_not]; omega
    unfold predState0; rw [hce]; rfl
  | l2 m =>
    have hm := m.isLt
    have h2 : ¬(0 = S_close0 n 0 + 2) := by unfold S_close0; omega
    have h3 : ¬(0 = S_close0 n 0 + 3) := by unfold S_close0; omega
    have hce : chooseEdge1 glob n 0 0 (.l2 m) = false := by
      simp only [chooseEdge1, h2, h3, and_false, ite_false]
      split_ifs <;> simp only [decide_eq_false_iff_not] <;> omega
    unfold predState0; rw [hce]; rfl
  | l3 m =>
    have hm := m.isLt
    have h2 : ¬(0 = S_close0 n 0 + 2) := by unfold S_close0; omega
    have h3 : ¬(0 = S_close0 n 0 + 3) := by unfold S_close0; omega
    have hce : chooseEdge1 glob n 0 0 (.l3 m) = false := by
      simp only [chooseEdge1, h2, h3, and_false, ite_false]
      split_ifs <;> simp only [decide_eq_false_iff_not] <;> omega
    unfold predState0; rw [hce]; rfl
  | lp1 m =>
    have hm := m.isLt
    have h2 : ¬(0 = S_close0 n 0 + 2) := by unfold S_close0; omega
    have h3 : ¬(0 = S_close0 n 0 + 3) := by unfold S_close0; omega
    have hce : chooseEdge1 glob n 0 0 (.lp1 m) = true := by
      simp only [chooseEdge1, h2, h3, and_false, ite_false]
      split_ifs; try rfl
      simp only [decide_eq_true_eq]; omega
    unfold predState0; rw [hce]; rfl
  | lp2 m =>
    have hm := m.isLt
    have h2 : ¬(0 = S_close0 n 0 + 2) := by unfold S_close0; omega
    have h3 : ¬(0 = S_close0 n 0 + 3) := by unfold S_close0; omega
    have hce : chooseEdge1 glob n 0 0 (.lp2 m) = true := by
      simp only [chooseEdge1, h2, h3, and_false, ite_false]
      split_ifs <;> rfl
    unfold predState0; rw [hce]; rfl
  | lp3 m =>
    have hm := m.isLt
    have h3 : ¬(0 = S_close0 n 0 + 3) := by unfold S_close0; omega
    have hce : chooseEdge1 glob n 0 0 (.lp3 m) = true := by
      simp only [chooseEdge1, h3, and_false, ite_false]
      split_ifs <;> rfl
    unfold predState0; rw [hce]; rfl
  | rp i =>
    have hce : chooseEdge1 glob n 0 0 (.rp i) = true := by
      dsimp [chooseEdge1, S_close0]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | sp i =>
    have hce : chooseEdge1 glob n 0 0 (.sp i) = true := by
      dsimp [chooseEdge1, S_close0]; split_ifs <;> simp_all
    unfold predState0; rw [hce]; rfl
  | r_2 =>
    have hce : chooseEdge1 glob n 0 0 .r_2 = false := by
      dsimp [chooseEdge1, S_close0]; simp_all
    unfold predState0; rw [hce]; rfl
  | r =>
    have hce : chooseEdge1 glob n 0 0 .r = false := by
      dsimp [chooseEdge1, rActive0, S_close0]; simp_all
    unfold predState0; rw [hce]; rfl
  | s =>
    have hce : chooseEdge1 glob n 0 0 .s = false := by
      dsimp [chooseEdge1, sActive0, S_close0]; simp_all
    unfold predState0; rw [hce]; rfl
  | _ => rfl

lemma predState0_zero_eq_init (glob : Bool) (n : ℕ) (hn : 0 < n) (v : V_bin n) :
    (G_bin n).owner v = false → predState0 glob n 0 0 v = ι_bin n v :=
  fun _ => predState0_zero_eq_init_all glob n hn v

/-! ### Part 3: Topological Rank `predRank0` and Strict Decrease Along `step` -/

def isBot0 (n b s : ℕ) (i : Fin n) : Bool :=
  b.testBit i.val || decide (b < 2 ^ n - 1 ∧ i.val = lowestZero0 b n ∧ S_close0 n b ≤ s)

def uStillH0 (n b s : ℕ) (i : Fin n) : Bool :=
  decide (0 < b ∧ i.val < lowestOne0 b n ∧ i.val + s < uLim0 b n)

def uIsBot0 (n b s : ℕ) (i : Fin n) : Bool :=
  isBot0 n b s i || (decide (1 ≤ i.val) && hasHigherOne0 b n i.val && !uStillH0 n b s i)

def botBase0 (n : ℕ) (i : Fin n) : ℕ := 20 * (n - 1 - i.val) + 1
def topBase0 (n : ℕ) (i : Fin n) : ℕ := 1000 * n + 20 * (n - 1 - i.val) + 1

def rankBase0 (n b s : ℕ) (i : Fin n) : ℕ :=
  if isBot0 n b s i then botBase0 n i else topBase0 n i

def dClosed0 (n b s : ℕ) (i : Fin n) : Bool :=
  let k := lowestZero0 b n
  let S_close := S_close0 n b
  let T_i := 3 * (n + 2 * i.val + 1)
  (b.testBit i.val && decide ¬(b < 2 ^ n - 1 ∧ i.val < k ∧ s = S_close + 3)) ||
  (!b.testBit i.val && decide (T_i + 2 ≤ s))

def predRank0 (glob : Bool) (n b s : ℕ) : V_bin n → ℕ
  | .x => 0
  | .z i => rankBase0 n b s i + 1
  | .k i => rankBase0 n b s i + 2
  | .g i => rankBase0 n b s i + 4
  | .f i => rankBase0 n b s i + 5
  | .hy i => rankBase0 n b s i + 8
  | .hx i => rankBase0 n b s i + 9
  | .h i => rankBase0 n b s i + 10
  | .u i => (if uIsBot0 n b s i then botBase0 n i else topBase0 n i) + 11
  | .d3 i =>
      let T_i := 3 * (n + 2 * i.val + 1)
      if dClosed0 n b s i then rankBase0 n b s i + 5
      else if s = T_i + 1 ∨ (glob = false ∧ s < T_i ∧ s % 3 = 1) then topBase0 n i + 6
      else topBase0 n i + 1
  | .d2 i =>
      if dClosed0 n b s i then rankBase0 n b s i + 6
      else topBase0 n i + 2
  | .d1 i =>
      if dClosed0 n b s i then rankBase0 n b s i + 7
      else topBase0 n i + 3
  | .rp i =>
      if rActive0 n b s && decide (rTarg0 n b s ≤ i.val) then 25 * n + i.val + 1 else 2000 * n + i.val + 1
  | .sp i =>
      if sActive0 n b s && decide (sTarg0 n b s ≤ i.val) then 25 * n + n + i.val + 1 else 2000 * n + n + i.val + 1
  | .s => 25 * n + 2 * n + 1
  | .c => 25 * n + 2 * n + 2
  | .c_odd => 25 * n + 2 * n + 3
  | .r => 25 * n + 2 * n + 4
  | .r_a => 25 * n + 2 * n + 5
  | .a j => 25 * n + 2 * n + 6 + j.val
  | .r_2 => 25 * n + 2 * n + 6 + 3 * (3 * n - 1)
  | .r_2_odd => 25 * n + 2 * n + 7 + 3 * (3 * n - 1)
  | .b k => 25 * n + 2 * n + 8 + 3 * (3 * n - 1) + k.val
  | .l1 m | .l2 m | .l3 m => 25 * n + 2 * n + 10 + 6 * (3 * n - 1) + 2 * m.val + 1
  | .lp1 m | .lp2 m | .lp3 m => 25 * n + 2 * n + 10 + 6 * (3 * n - 1) + 2 * m.val + 2

lemma predRank0_x (glob : Bool) (n b s : ℕ) : predRank0 glob n b s .x = 0 := rfl

lemma step_pred_x (glob : Bool) (n b s : ℕ) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .x = .x := rfl

lemma rankBase0_le_topBase0 (n b s : ℕ) (i : Fin n) :
    rankBase0 n b s i ≤ topBase0 n i := by
  unfold rankBase0 botBase0 topBase0
  split_ifs <;> omega

private lemma rTarg0_lt_of_rActive0 (n b s : ℕ) (hbn : b < 2 ^ n) (hact : rActive0 n b s = true) :
    rTarg0 n b s < n := by
  unfold rActive0 at hact
  rw [decide_eq_true_eq] at hact
  unfold rTarg0
  split_ifs with h2
  · exact lowestZero0_lt h2.1
  · rcases hact with hb0 | h2'
    · exact lowestOne0_lt hb0 hbn
    · exact False.elim (h2 h2')

private lemma sTarg0_lt_of_sActive0 (n b s : ℕ) (hbn : b < 2 ^ n) (hact : sActive0 n b s = true) :
    sTarg0 n b s < n := by
  unfold sActive0 at hact
  rw [decide_eq_true_eq] at hact
  unfold sTarg0
  split_ifs with h2
  · exact lowestZero0_lt h2.1
  · rcases hact with hb0 | h2'
    · exact lowestOne0_lt hb0 hbn
    · exact False.elim (h2 h2')

private lemma predRank0_step_r (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r) <
      predRank0 glob n b s .r := by
  rcases hvalid with ⟨hn, hbn, _⟩
  change predRank0 glob n b s (predState0 glob n b s .r) < predRank0 glob n b s .r
  have hce : chooseEdge1 glob n b s .r = rActive0 n b s := rfl
  unfold predState0
  rw [hce]
  cases hact : rActive0 n b s with
  | false =>
    dsimp [edge0, predRank0]; omega
  | true =>
    dsimp [edge1]
    rw [dif_pos hn]
    have htarg := rTarg0_lt_of_rActive0 n b s hbn hact
    dsimp [predRank0]
    rw [if_pos]
    · omega
    · simp [hact]; omega

private lemma predRank0_step_s (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .s) <
      predRank0 glob n b s .s := by
  rcases hvalid with ⟨hn, hbn, _⟩
  change predRank0 glob n b s (predState0 glob n b s .s) < predRank0 glob n b s .s
  have hce : chooseEdge1 glob n b s .s = sActive0 n b s := rfl
  unfold predState0
  rw [hce]
  cases hact : sActive0 n b s with
  | false =>
    dsimp [edge0, predRank0]; omega
  | true =>
    dsimp [edge1]
    rw [dif_pos hn]
    have htarg := sTarg0_lt_of_sActive0 n b s hbn hact
    dsimp [predRank0]
    rw [if_pos]
    · omega
    · simp [hact]; omega

private lemma isBot0_of_eq_rTarg0 (n b s : ℕ) (hbn : b < 2 ^ n) (i : Fin n)
    (hact : rActive0 n b s = true) (heq : i.val = rTarg0 n b s) :
    isBot0 n b s i = true := by
  unfold rActive0 at hact
  rw [decide_eq_true_eq] at hact
  unfold rTarg0 at heq
  unfold isBot0
  rw [Bool.or_eq_true, decide_eq_true_eq]
  split_ifs at heq with h2
  · right
    exact ⟨h2.1, heq, by omega⟩
  · left
    rcases hact with hb0 | h2'
    · rw [heq]
      exact testBit_lowestOne0 hb0 hbn
    · exact False.elim (h2 h2')

private lemma isBot0_of_eq_sTarg0 (n b s : ℕ) (hbn : b < 2 ^ n) (i : Fin n)
    (hact : sActive0 n b s = true) (heq : i.val = sTarg0 n b s) :
    isBot0 n b s i = true := by
  unfold sActive0 at hact
  rw [decide_eq_true_eq] at hact
  unfold sTarg0 at heq
  unfold isBot0
  rw [Bool.or_eq_true, decide_eq_true_eq]
  split_ifs at heq with h2
  · right
    exact ⟨h2.1, heq, by omega⟩
  · left
    rcases hact with hb0 | h2'
    · rw [heq]
      exact testBit_lowestOne0 hb0 hbn
    · exact False.elim (h2 h2')

private lemma predRank0_step_rp (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.rp i)) <
      predRank0 glob n b s (.rp i) := by
  rcases hvalid with ⟨hn, hbn, _⟩
  have hi := i.isLt
  change predRank0 glob n b s (predState0 glob n b s (.rp i)) < predRank0 glob n b s (.rp i)
  by_cases hi0 : i.val = 0
  · have hstep : predState0 glob n b s (.rp i) = .f i := by
      unfold predState0
      simp [chooseEdge1, edge1, hi0]
    rw [hstep]
    dsimp [predRank0]
    split_ifs with hcond
    · rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have heq : i.val = rTarg0 n b s := by omega
      have hbot := isBot0_of_eq_rTarg0 n b s hbn i hcond.1 heq
      dsimp [rankBase0, botBase0]
      rw [hbot]
      simp only [ite_true]
      omega
    · have := rankBase0_le_topBase0 n b s i
      dsimp [topBase0] at this
      omega
  · by_cases hce : chooseEdge1 glob n b s (.rp i) = true
    · have hstep : predState0 glob n b s (.rp i) = .rp ⟨i.val - 1, by omega⟩ := by
        unfold predState0
        rw [if_pos hce]
        simp [edge1, hi0]
      rw [hstep]
      have hne_targ : rActive0 n b s = true → i.val ≠ rTarg0 n b s := by
        intro hact
        dsimp [chooseEdge1] at hce
        rw [if_neg hi0] at hce
        unfold rActive0 at hact
        rw [decide_eq_true_eq] at hact
        unfold rTarg0
        split_ifs at hce with h2
        · rw [if_pos h2]
          exact of_decide_eq_true hce
        · rw [if_neg h2]
          have hb0 : 0 < b := by rcases hact with hb0 | h2'; exact hb0; exact False.elim (h2 h2')
          have hnot := of_decide_eq_true hce
          intro heq
          exact hnot ⟨hb0, heq⟩
      dsimp [predRank0]
      split_ifs with hcond1 hcond2 hcond2
      · omega
      · omega
      · exfalso
        rw [Bool.and_eq_true, decide_eq_true_eq] at hcond2
        have hne := hne_targ hcond2.1
        have hcond1' : rActive0 n b s = true ∧ rTarg0 n b s ≤ i.val - 1 := ⟨hcond2.1, by omega⟩
        have : (rActive0 n b s && decide (rTarg0 n b s ≤ i.val - 1)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_eq]
          exact hcond1'
        exact hcond1 this
      · omega
    · have hce_false : chooseEdge1 glob n b s (.rp i) = false := Bool.eq_false_of_not_eq_true hce
      have hstep : predState0 glob n b s (.rp i) = .f i := by
        unfold predState0
        rw [hce_false]
        rfl
      rw [hstep]
      have heq_targ : i.val = rTarg0 n b s ∧ rActive0 n b s = true := by
        dsimp [chooseEdge1] at hce_false
        rw [if_neg hi0] at hce_false
        unfold rTarg0 rActive0
        split_ifs at hce_false with h2
        · rw [decide_eq_false_iff_not, not_not] at hce_false
          rw [if_pos h2, decide_eq_true_eq]
          exact ⟨hce_false, Or.inr h2⟩
        · rw [decide_eq_false_iff_not, not_not] at hce_false
          rw [if_neg h2, decide_eq_true_eq]
          exact ⟨hce_false.2, Or.inl hce_false.1⟩
      have hbot := isBot0_of_eq_rTarg0 n b s hbn i heq_targ.2 heq_targ.1
      dsimp [predRank0, rankBase0, botBase0, topBase0]
      rw [hbot]
      simp only [ite_true]
      split_ifs <;> omega

private lemma predRank0_step_sp (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.sp i)) <
      predRank0 glob n b s (.sp i) := by
  rcases hvalid with ⟨hn, hbn, _⟩
  have hi := i.isLt
  change predRank0 glob n b s (predState0 glob n b s (.sp i)) < predRank0 glob n b s (.sp i)
  by_cases hi0 : i.val = 0
  · have hstep : predState0 glob n b s (.sp i) = .hx i := by
      unfold predState0
      simp [chooseEdge1, edge1, hi0]
    rw [hstep]
    dsimp [predRank0]
    split_ifs with hcond
    · rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have heq : i.val = sTarg0 n b s := by omega
      have hbot := isBot0_of_eq_sTarg0 n b s hbn i hcond.1 heq
      dsimp [rankBase0, botBase0]
      rw [hbot]
      simp only [ite_true]
      omega
    · have := rankBase0_le_topBase0 n b s i
      dsimp [topBase0] at this
      omega
  · by_cases hce : chooseEdge1 glob n b s (.sp i) = true
    · have hstep : predState0 glob n b s (.sp i) = .sp ⟨i.val - 1, by omega⟩ := by
        unfold predState0
        rw [if_pos hce]
        simp [edge1, hi0]
      rw [hstep]
      have hne_targ : sActive0 n b s = true → i.val ≠ sTarg0 n b s := by
        intro hact
        dsimp [chooseEdge1] at hce
        rw [if_neg hi0] at hce
        unfold sActive0 at hact
        rw [decide_eq_true_eq] at hact
        unfold sTarg0
        split_ifs at hce with h2
        · rw [if_pos h2]
          exact of_decide_eq_true hce
        · rw [if_neg h2]
          have hb0 : 0 < b := by rcases hact with hb0 | h2'; exact hb0; exact False.elim (h2 h2')
          have hnot := of_decide_eq_true hce
          intro heq
          exact hnot ⟨hb0, heq⟩
      dsimp [predRank0]
      split_ifs with hcond1 hcond2 hcond2
      · omega
      · omega
      · exfalso
        rw [Bool.and_eq_true, decide_eq_true_eq] at hcond2
        have hne := hne_targ hcond2.1
        have hcond1' : sActive0 n b s = true ∧ sTarg0 n b s ≤ i.val - 1 := ⟨hcond2.1, by omega⟩
        have : (sActive0 n b s && decide (sTarg0 n b s ≤ i.val - 1)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_eq]
          exact hcond1'
        exact hcond1 this
      · omega
    · have hce_false : chooseEdge1 glob n b s (.sp i) = false := Bool.eq_false_of_not_eq_true hce
      have hstep : predState0 glob n b s (.sp i) = .hx i := by
        unfold predState0
        rw [hce_false]
        rfl
      rw [hstep]
      have heq_targ : i.val = sTarg0 n b s ∧ sActive0 n b s = true := by
        dsimp [chooseEdge1] at hce_false
        rw [if_neg hi0] at hce_false
        unfold sTarg0 sActive0
        split_ifs at hce_false with h2
        · rw [decide_eq_false_iff_not, not_not] at hce_false
          rw [if_pos h2, decide_eq_true_eq]
          exact ⟨hce_false, Or.inr h2⟩
        · rw [decide_eq_false_iff_not, not_not] at hce_false
          rw [if_neg h2, decide_eq_true_eq]
          exact ⟨hce_false.2, Or.inl hce_false.1⟩
      have hbot := isBot0_of_eq_sTarg0 n b s hbn i heq_targ.2 heq_targ.1
      dsimp [predRank0, rankBase0, botBase0, topBase0]
      rw [hbot]
      simp only [ite_true]
      split_ifs <;> omega

private lemma uIsBot0_succ_of_hasHigherOne0 (n b s : ℕ) (i : Fin n) (hi1 : i.val + 1 < n)
    (hhi : hasHigherOne0 b n i.val = true)
    (hnot_still : uStillH0 n b s ⟨i.val + 1, hi1⟩ = false) :
    uIsBot0 n b s ⟨i.val + 1, hi1⟩ = true := by
  rcases (hasHigherOne0_iff b n i.val).mp hhi with ⟨j, hij, hjn, hbit⟩
  unfold uIsBot0 isBot0
  by_cases hj : j = i.val + 1
  · subst hj
    simp [hbit]
  · have hij' : i.val + 1 < j := by omega
    have hhi' : hasHigherOne0 b n (i.val + 1) = true :=
      (hasHigherOne0_iff b n (i.val + 1)).mpr ⟨j, hij', hjn, hbit⟩
    rw [Bool.or_eq_true]
    right
    simp [hhi', hnot_still]

private lemma predRank0_step_z (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z i)) <
      predRank0 glob n b s (.z i) := by
  rcases hvalid with ⟨hn, hbn, _⟩
  have hi := i.isLt
  change predRank0 glob n b s (predState0 glob n b s (.z i)) < predRank0 glob n b s (.z i)
  have hce_eq : chooseEdge1 glob n b s (.z i) = (decide (i.val + 1 < n) && hasHigherOne0 b n i.val) := rfl
  unfold predState0
  rw [hce_eq]
  by_cases hce : (decide (i.val + 1 < n) && hasHigherOne0 b n i.val) = true
  · rw [if_pos hce]
    rw [Bool.and_eq_true, decide_eq_true_eq] at hce
    rcases hce with ⟨hi1, hhi⟩
    dsimp [edge1]
    rw [dif_pos hi1]
    dsimp [predRank0, rankBase0]
    cases hbot : isBot0 n b s i with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      dsimp [botBase0, topBase0]
      split_ifs <;> omega
    | true =>
      simp only [ite_true]
      have hnot_still : uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
        unfold uStillH0 uLim0
        rw [decide_eq_false_iff_not]
        dsimp only
        rintro ⟨hb0, hlt_prev, hlt_lim⟩
        unfold isBot0 at hbot
        rw [Bool.or_eq_true, decide_eq_true_eq] at hbot
        rcases hbot with hbit | ⟨hb_lt, hik, hs_ge⟩
        · have hle := lowestOne0_le_of_testBit_true hi hbit
          omega
        · have hprev_lt := lowestOne0_lt hb0 hbn
          unfold S_close0 at hs_ge
          split_ifs at hlt_lim <;> omega
      have hubot := uIsBot0_succ_of_hasHigherOne0 n b s i hi1 hhi hnot_still
      rw [hubot]
      simp only [ite_true]
      dsimp [botBase0]
      omega
  · rw [if_neg hce]
    dsimp [edge0, predRank0, rankBase0, botBase0, topBase0]
    split_ifs <;> omega

private lemma predRank0_step_u (glob : Bool) (n b s : ℕ) (i : Fin n) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u i)) <
      predRank0 glob n b s (.u i) := by
  have hi := i.isLt
  by_cases hi0 : i.val = 0
  · have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u i) = .h i := by
      unfold step G_bin owner_bin predTau0
      rw [if_neg (by simp [hi0])]
      rfl
    rw [hstep]
    have hubot : uIsBot0 n b s i = isBot0 n b s i := by
      unfold uIsBot0
      simp [hi0]
    dsimp [predRank0, rankBase0]
    rw [hubot]
    omega
  · have hstep_eq : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u i) =
        predState0 glob n b s (.u i) := by
      unfold step G_bin owner_bin
      rw [if_pos (by simp [hi0])]
    rw [hstep_eq]
    by_cases hce : chooseEdge1 glob n b s (.u i) = true
    · have hce' := hce
      dsimp [chooseEdge1] at hce'
      split_ifs at hce' with h1 h2 h3
      · have hi1 : i.val + 1 < n := by omega
        have hhi : hasHigherOne0 b n i.val = true := by
          cases hhi_b : hasHigherOne0 b n i.val with
          | true => rfl
          | false => exfalso; exact h2 (Or.inr (by simp [hhi_b]))
        have hnot_still : uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
          dsimp [uStillH0]
          rw [decide_eq_false_iff_not]
          have hnot := of_decide_eq_true hce'
          intro hcond
          exact hnot (by omega)
        have hubot := uIsBot0_succ_of_hasHigherOne0 n b s i hi1 hhi hnot_still
        have hpred : predState0 glob n b s (.u i) = .u ⟨i.val + 1, hi1⟩ := by
          unfold predState0
          rw [if_pos hce]
          dsimp [edge1]
          rw [dif_pos ⟨hi0, hi1⟩]
        rw [hpred]
        dsimp [predRank0]
        rw [hubot]
        simp only [ite_true]
        dsimp [botBase0, topBase0]
        split_ifs <;> omega
      · have hi1 : i.val + 1 < n := by omega
        have hhi : hasHigherOne0 b n i.val = true := by
          cases hhi_b : hasHigherOne0 b n i.val with
          | true => rfl
          | false => exfalso; exact h2 (Or.inr (by simp [hhi_b]))
        have hnot_still : uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
          dsimp [uStillH0]
          rw [decide_eq_false_iff_not]
          intro hcond
          exact h3 ⟨hcond.1, by omega⟩
        have hubot := uIsBot0_succ_of_hasHigherOne0 n b s i hi1 hhi hnot_still
        have hpred : predState0 glob n b s (.u i) = .u ⟨i.val + 1, hi1⟩ := by
          unfold predState0
          rw [if_pos hce]
          dsimp [edge1]
          rw [dif_pos ⟨hi0, hi1⟩]
        rw [hpred]
        dsimp [predRank0]
        rw [hubot]
        simp only [ite_true]
        dsimp [botBase0, topBase0]
        split_ifs <;> omega
    · have hce_false : chooseEdge1 glob n b s (.u i) = false := Bool.eq_false_of_not_eq_true hce
      have hpred : predState0 glob n b s (.u i) = .h i := by
        unfold predState0
        rw [hce_false]
        rfl
      rw [hpred]
      have hubot : uIsBot0 n b s i = isBot0 n b s i := by
        unfold uIsBot0
        cases hbot : isBot0 n b s i with
        | true => rfl
        | false =>
          cases hhi : hasHigherOne0 b n i.val with
          | false => simp
          | true =>
            have hbit : b.testBit i.val = false := by
              unfold isBot0 at hbot
              simpa using (Bool.or_eq_false_iff.mp hbot).1
            have hi1 : i.val + 1 < n := by
              rcases (hasHigherOne0_iff b n i.val).mp hhi with ⟨j, hij, hjn, _⟩
              omega
            have h1 : ¬(i.val = 0 ∨ ¬i.val + 1 < n) := by omega
            have h2 : ¬(b.testBit i.val = true ∨ (!hasHigherOne0 b n i.val) = true) := by
              simp [hbit, hhi]
            dsimp [chooseEdge1] at hce_false
            rw [if_neg h1, if_neg h2] at hce_false
            split_ifs at hce_false with h3
            · rw [decide_eq_false_iff_not, not_not] at hce_false
              have hstill : uStillH0 n b s i = true := by
                unfold uStillH0
                simp [h3.1, h3.2, hce_false]
              simp [hstill]
      dsimp [predRank0, rankBase0]
      rw [hubot]
      omega

private lemma predRank0_step_g (glob : Bool) (n b s : ℕ) (i : Fin n) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i)) <
      predRank0 glob n b s (.g i) := by
  change predRank0 glob n b s (predTau0 n b s (.g i)) < predRank0 glob n b s (.g i)
  unfold predTau0
  by_cases htau : chooseTauEdge1 n b s (.g i) = true
  · rw [if_pos htau]
    dsimp [edge1, predRank0]
    omega
  · rw [if_neg htau]
    have htau_false : chooseTauEdge1 n b s (.g i) = false := Bool.eq_false_of_not_eq_true htau
    dsimp [chooseTauEdge1] at htau_false
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at htau_false
    rcases htau_false with ⟨⟨hbit, hlt_T⟩, _⟩
    have hd : dClosed0 n b s i = false := by
      unfold dClosed0
      simp [hbit, hlt_T]
    have hbot : isBot0 n b s i = false := by
      unfold isBot0 S_close0
      simp only [hbit, Bool.false_or, decide_eq_false_iff_not]
      rintro ⟨_, hik, hs_ge⟩
      rw [← hik] at hs_ge
      exact hlt_T hs_ge
    dsimp [edge0, predRank0, rankBase0]
    rw [hd, hbot]
    simp only [Bool.false_eq_true, ite_false]
    omega

private lemma predRank0_step_d1 (glob : Bool) (n b s : ℕ) (i : Fin n) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i)) <
      predRank0 glob n b s (.d1 i) := by
  have hi := i.isLt
  change predRank0 glob n b s (predState0 glob n b s (.d1 i)) < predRank0 glob n b s (.d1 i)
  cases hd : dClosed0 n b s i with
  | true =>
    have hce : chooseEdge1 glob n b s (.d1 i) = true := by
      unfold dClosed0 at hd
      dsimp [chooseEdge1]
      rcases Bool.or_eq_true_iff.mp hd with h1 | h2
      · rw [Bool.and_eq_true, decide_eq_true_eq] at h1
        rw [if_pos h1.1, if_neg h1.2]
      · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2
        rw [if_neg (by simp [h2.1]), if_pos (by omega)]
    unfold predState0
    rw [if_pos hce]
    dsimp [edge1, predRank0]
    rw [hd]
    simp only [ite_true]
    omega
  | false =>
    unfold predState0
    split_ifs with hce
    · dsimp [edge1, predRank0]
      rw [hd]
      simp only [Bool.false_eq_true, ite_false]
      omega
    · dsimp [edge0, tap_bin, predRank0, topBase0]
      rw [hd]
      simp only [Bool.false_eq_true, ite_false]
      omega

private lemma predRank0_step_d2 (glob : Bool) (n b s : ℕ) (i : Fin n) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i)) <
      predRank0 glob n b s (.d2 i) := by
  have hi := i.isLt
  change predRank0 glob n b s (predState0 glob n b s (.d2 i)) < predRank0 glob n b s (.d2 i)
  cases hd : dClosed0 n b s i with
  | true =>
    have hce : chooseEdge1 glob n b s (.d2 i) = true := by
      unfold dClosed0 at hd
      dsimp [chooseEdge1]
      rcases Bool.or_eq_true_iff.mp hd with h1 | h2
      · rw [Bool.and_eq_true, decide_eq_true_eq] at h1
        rw [if_pos h1.1, if_neg h1.2]
      · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2
        rw [if_neg (by simp [h2.1]), if_pos h2.2]
    unfold predState0
    rw [if_pos hce]
    dsimp [edge1, predRank0]
    rw [hd]
    simp only [ite_true]
    omega
  | false =>
    unfold predState0
    split_ifs with hce
    · have hnot_branch : ¬(s = 3 * (n + 2 * i.val + 1) + 1 ∨
          (glob = false ∧ s < 3 * (n + 2 * i.val + 1) ∧ s % 3 = 1)) := by
        unfold dClosed0 at hd
        dsimp [chooseEdge1] at hce
        cases hbit : b.testBit i.val with
        | true =>
          simp [hbit] at hd
          simp [hbit, hd] at hce
        | false =>
          simp [hbit] at hd hce
          omega
      dsimp [edge1, predRank0]
      rw [hd, if_neg hnot_branch]
      simp only [Bool.false_eq_true, ite_false]
      omega
    · dsimp [edge0, tap_bin, predRank0, topBase0]
      rw [hd]
      simp only [Bool.false_eq_true, ite_false]
      omega

private lemma predRank0_step_d3 (glob : Bool) (n b s : ℕ) (i : Fin n) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d3 i)) <
      predRank0 glob n b s (.d3 i) := by
  have hi := i.isLt
  change predRank0 glob n b s (predState0 glob n b s (.d3 i)) < predRank0 glob n b s (.d3 i)
  cases hd : dClosed0 n b s i with
  | true =>
    have hce : chooseEdge1 glob n b s (.d3 i) = true := by
      unfold dClosed0 at hd
      dsimp [chooseEdge1]
      rcases Bool.or_eq_true_iff.mp hd with h1 | h2
      · rw [Bool.and_eq_true, decide_eq_true_eq] at h1
        rw [if_pos h1.1, if_neg h1.2]
      · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2
        rw [if_neg (by simp [h2.1]), if_pos (by omega)]
    unfold predState0
    rw [if_pos hce]
    dsimp [edge1, predRank0]
    rw [hd]
    simp only [ite_true]
    omega
  | false =>
    unfold predState0
    split_ifs with hce
    · have hbranch : s = 3 * (n + 2 * i.val + 1) + 1 ∨
          (glob = false ∧ s < 3 * (n + 2 * i.val + 1) ∧ s % 3 = 1) := by
        unfold dClosed0 at hd
        dsimp [chooseEdge1] at hce
        cases hbit : b.testBit i.val with
        | true =>
          simp [hbit] at hd
          simp [hbit, hd] at hce
        | false =>
          simp [hbit] at hd hce
          rcases hce with hce | ⟨_, hglob, hmod, _⟩
          · left; omega
          · by_cases hs : s = 3 * (n + 2 * i.val + 1) + 1
            · left; exact hs
            · right; exact ⟨hglob, by omega, hmod⟩
      dsimp [edge1, predRank0]
      rw [hd, if_pos hbranch]
      simp only [Bool.false_eq_true, ite_false]
      have := rankBase0_le_topBase0 n b s i
      omega
    · dsimp [edge0, tap_bin, predRank0, topBase0]
      rw [hd]
      simp only [Bool.false_eq_true, ite_false]
      split_ifs <;> omega

lemma predRank0_step_lt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (v : V_bin n) (hv : v ≠ .x) :
    predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) v) <
      predRank0 glob n b s v := by
  cases v with
  | x => contradiction
  | r => exact predRank0_step_r glob n b s hvalid
  | s => exact predRank0_step_s glob n b s hvalid
  | rp i => exact predRank0_step_rp glob n b s hvalid i
  | sp i => exact predRank0_step_sp glob n b s hvalid i
  | z i => exact predRank0_step_z glob n b s hvalid i
  | u i => exact predRank0_step_u glob n b s i
  | g i => exact predRank0_step_g glob n b s i
  | d1 i => exact predRank0_step_d1 glob n b s i
  | d2 i => exact predRank0_step_d2 glob n b s i
  | d3 i => exact predRank0_step_d3 glob n b s i
  | a j =>
    have hj := j.isLt
    unfold step
    dsimp only [G_bin, owner_bin]
    unfold predState0 predTau0
    split_ifs <;> (dsimp [chooseTauEdge1, edge0, edge1]; try split_ifs) <;> (dsimp [predRank0]; omega)
  | b k =>
    have hk := k.isLt
    have hb := (bTarget n k).isLt
    dsimp [step, G_bin, owner_bin, predTau0, chooseTauEdge1, edge0, predRank0]
    omega
  | l1 m | lp1 m | lp2 m | lp3 m =>
    have hm := m.isLt
    unfold step
    dsimp only [G_bin, owner_bin]
    unfold predState0 predTau0
    split_ifs <;> (dsimp [chooseTauEdge1, edge0, edge1]; try split_ifs) <;> (dsimp [predRank0]; omega)
  | l2 m | l3 m =>
    have hm := m.isLt
    change predRank0 glob n b s (predState0 glob n b s _) < predRank0 glob n b s _
    unfold predState0
    split_ifs <;> (dsimp [edge0, edge1, predRank0]; omega)
  | r_2 | hy _ | hx _ | h _ =>
    change predRank0 glob n b s (predState0 glob n b s _) < predRank0 glob n b s _
    unfold predState0
    split_ifs <;> (dsimp [edge0, edge1, predRank0]; omega)
  | r_2_odd | r_a | c_odd | c | f _ | k _ =>
    dsimp [step, G_bin, owner_bin, predTau0, chooseTauEdge1, edge0, predRank0]
    omega

/-! ### Part 4: Consequences from `Sol_friedmann_parity_binary_sink` -/

lemma pred_cyclePriority_eq_one (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (v : V_bin n) :
    (playValue (G_bin n) (predState0 glob n b s) (predTau0 n b s) v).cyclePriority = 1 :=
  cyclePriority_eq_one_of_rank
    (G_bin_wellFormed n hvalid.1)
    (G_bin_sink_priority n)
    (step_pred_x glob n b s)
    (predRank0 glob n b s)
    (predRank0_step_lt glob n b s hvalid)
    v

lemma pred_path_x (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    (playValue (G_bin n) (predState0 glob n b s) (predTau0 n b s) .x).path = ∅ :=
  path_sink_of_rank
    (G_bin_wellFormed n hvalid.1)
    (step_pred_x glob n b s)
    (predRank0 glob n b s)
    (predRank0_step_lt glob n b s hvalid)

lemma pred_path_step (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (v : V_bin n) (hv : v ≠ .x) :
    (playValue (G_bin n) (predState0 glob n b s) (predTau0 n b s) v).path =
      insert v (playValue (G_bin n) (predState0 glob n b s) (predTau0 n b s)
        (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) v)).path :=
  path_step_of_rank
    (G_bin_wellFormed n hvalid.1)
    (G_bin_sink_priority n)
    (step_pred_x glob n b s)
    (predRank0 glob n b s)
    (predRank0_step_lt glob n b s hvalid)
    (G_bin_gt_one_of_ne_sink n hvalid.1)
    v hv

lemma pred_not_mem_path_of_rank_lt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w v : V_bin n) (hlt : predRank0 glob n b s w < predRank0 glob n b s v) :
    v ∉ (playValue (G_bin n) (predState0 glob n b s) (predTau0 n b s) w).path :=
  not_mem_path_of_rank_lt
    (G_bin_wellFormed n hvalid.1)
    (step_pred_x glob n b s)
    (predRank0 glob n b s)
    (predRank0_step_lt glob n b s hvalid)
    w v hlt

/-! ### Part 5: Next-State Transition, `BestEdgeProp`, `HitsPortal`, and `PrefixTo` -/

def nextPair (n b s : ℕ) : ℕ × ℕ :=
  if b = 2 ^ n - 1 ∧ s = 9 * n - 4 then (b, s)
  else if b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 then (b + 1, 0)
  else (b, s + 1)

def bestEdge1 (n b s : ℕ) (v : V_bin n) : Bool :=
  chooseEdge1 false n (nextPair n b s).1 (nextPair n b s).2 v

def bestEdge (n b s : ℕ) (v : V_bin n) : V_bin n :=
  if bestEdge1 n b s v then edge1 n v else edge0 n v

def worstEdge (n b s : ℕ) (v : V_bin n) : V_bin n :=
  if bestEdge1 n b s v then edge0 n v else edge1 n v

noncomputable abbrev predVal (glob : Bool) (n b s : ℕ) (v : V_bin n) : Valuation (V_bin n) :=
  playValue (G_bin n) (predState0 glob n b s) (predTau0 n b s) v

noncomputable abbrev predPath (glob : Bool) (n b s : ℕ) (v : V_bin n) : Finset (V_bin n) :=
  (predVal glob n b s v).path

def BestEdgeProp (glob : Bool) (n b s : ℕ) (v : V_bin n) : Prop :=
  (G_bin n).owner v = false → edge0 n v ≠ edge1 n v →
    ValueLT (G_bin n) (predVal glob n b s (worstEdge n b s v)) (predVal glob n b s (bestEdge n b s v))

lemma edge_eq_bestEdge_or_worstEdge (n b s : ℕ) (v w : V_bin n) (he : (G_bin n).edge v w) :
    w = bestEdge n b s v ∨ w = worstEdge n b s v := by
  unfold bestEdge worstEdge
  rcases he with rfl | rfl
  · split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]
  · split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]

lemma predVal_lt_of_setLT (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (u w : V_bin n) (hset : SetLT (G_bin n) (predPath glob n b s u) (predPath glob n b s w)) :
    ValueLT (G_bin n) (predVal glob n b s u) (predVal glob n b s w) :=
  valueLT_of_setLT_of_cyclePriority_eq_one
    (pred_cyclePriority_eq_one glob n b s hvalid u)
    (pred_cyclePriority_eq_one glob n b s hvalid w)
    hset

def HitsPortal (glob : Bool) (n b s : ℕ) (w p : V_bin n) : Prop :=
  p ∈ predPath glob n b s w ∧
  ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
    (u ∈ predPath glob n b s w ↔ u ∈ predPath glob n b s p)

lemma hitsPortal_refl (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (p : V_bin n) (hp : p ≠ .x) :
    HitsPortal glob n b s p p := by
  refine ⟨?_, fun _ _ => Iff.rfl⟩
  rw [predPath, predVal, pred_path_step glob n b s hvalid p hp]
  exact Finset.mem_insert_self p _

lemma hitsPortal_of_step (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w p : V_bin n) (hw : w ≠ .x)
    (hprio : (G_bin n).priority w < (G_bin n).priority .c)
    (hstep : HitsPortal glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) p) :
    HitsPortal glob n b s w p := by
  have hpath : predPath glob n b s w =
      insert w (predPath glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w)) :=
    pred_path_step glob n b s hvalid w hw
  refine ⟨?_, ?_⟩
  · rw [hpath]
    exact Finset.mem_insert_of_mem hstep.1
  · intro u hu
    rw [hpath, Finset.mem_insert]
    have hne : u ≠ w := by
      intro heq
      subst heq
      omega
    simp only [hne, false_or]
    exact hstep.2 u hu

def PrefixTo (glob : Bool) (n b s : ℕ) (w m : V_bin n) (P : Finset (V_bin n)) : Prop :=
  predRank0 glob n b s m ≤ predRank0 glob n b s w ∧
  predPath glob n b s w = P ∪ predPath glob n b s m

lemma prefixTo_refl (glob : Bool) (n b s : ℕ) (m : V_bin n) :
    PrefixTo glob n b s m m ∅ :=
  ⟨le_rfl, (Finset.empty_union _).symm⟩

lemma prefixTo_of_step (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w m : V_bin n) (P : Finset (V_bin n)) (hw : w ≠ .x)
    (hstep : PrefixTo glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) m P) :
    PrefixTo glob n b s w m (insert w P) := by
  have hlt := predRank0_step_lt glob n b s hvalid w hw
  refine ⟨by have := hstep.1; omega, ?_⟩
  rw [predPath, predVal, pred_path_step glob n b s hvalid w hw]
  change insert w (predPath glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w)) = _
  rw [hstep.2, Finset.insert_union]

lemma predVal_lt_of_prefixTo_even (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w₁ w₂ m d : V_bin n} {P₁ P₂ : Finset (V_bin n)}
    (h₁ : PrefixTo glob n b s w₁ m P₁) (h₂ : PrefixTo glob n b s w₂ m P₂)
    (hd_not : d ∉ P₁) (hd_mem : d ∈ P₂)
    (hd_even : (G_bin n).priority d % 2 = 0)
    (hd_rank : predRank0 glob n b s m < predRank0 glob n b s d)
    (hhigh : ∀ u, (G_bin n).priority d < (G_bin n).priority u →
      (u ∈ P₁ ↔ u ∈ P₂) ∧ (u ∉ predPath glob n b s m ∨ (u ∈ P₁ ∧ u ∈ P₂))) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := d)
  · rw [h₁.2, Finset.mem_union, not_or]
    exact ⟨hd_not, pred_not_mem_path_of_rank_lt glob n b s hvalid m d hd_rank⟩
  · rw [h₂.2, Finset.mem_union]
    exact Or.inl hd_mem
  · exact hd_even
  · intro u hu
    rw [h₁.2, h₂.2, Finset.mem_union, Finset.mem_union]
    rcases hhigh u hu with ⟨hiff, hnot | ⟨hm1, hm2⟩⟩
    · simp only [hnot, or_false, hiff]
    · simp only [hm1, hm2, true_or]

lemma predVal_lt_of_prefixTo_odd (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w₁ w₂ m d : V_bin n} {P₁ P₂ : Finset (V_bin n)}
    (h₁ : PrefixTo glob n b s w₁ m P₁) (h₂ : PrefixTo glob n b s w₂ m P₂)
    (hd_mem : d ∈ P₁) (hd_not : d ∉ P₂)
    (hd_odd : (G_bin n).priority d % 2 = 1)
    (hd_rank : predRank0 glob n b s m < predRank0 glob n b s d)
    (hhigh : ∀ u, (G_bin n).priority d < (G_bin n).priority u →
      (u ∈ P₁ ↔ u ∈ P₂) ∧ (u ∉ predPath glob n b s m ∨ (u ∈ P₁ ∧ u ∈ P₂))) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := d)
  · rw [h₁.2, Finset.mem_union]
    exact Or.inl hd_mem
  · rw [h₂.2, Finset.mem_union, not_or]
    exact ⟨hd_not, pred_not_mem_path_of_rank_lt glob n b s hvalid m d hd_rank⟩
  · exact hd_odd
  · intro u hu
    rw [h₁.2, h₂.2, Finset.mem_union, Finset.mem_union]
    rcases hhigh u hu with ⟨hiff, hnot | ⟨hm1, hm2⟩⟩
    · simp only [hnot, or_false, hiff]
    · simp only [hm1, hm2, true_or]

def HitsWithTop (glob : Bool) (n b s : ℕ) (w p topV : V_bin n) : Prop :=
  predRank0 glob n b s p < predRank0 glob n b s topV ∧
  topV ∈ predPath glob n b s w ∧
  ∀ u, (G_bin n).priority topV < (G_bin n).priority u →
    (u ∈ predPath glob n b s w ↔ u ∈ predPath glob n b s p)

lemma hitsWithTop_of_step_eq (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w p : V_bin n) (hw : w ≠ .x)
    (hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w = p) :
    HitsWithTop glob n b s w p w := by
  have hlt := predRank0_step_lt glob n b s hvalid w hw
  rw [hstep] at hlt
  have hpath : predPath glob n b s w = insert w (predPath glob n b s p) := by
    rw [predPath, predVal, pred_path_step glob n b s hvalid w hw, hstep]
  refine ⟨hlt, ?_, ?_⟩
  · rw [hpath]; exact Finset.mem_insert_self w _
  · intro u hu
    rw [hpath, Finset.mem_insert]
    have hne : u ≠ w := by intro heq; subst heq; omega
    simp [hne]

lemma hitsWithTop_of_step_lt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w p topV : V_bin n) (hw : w ≠ .x)
    (hprio : (G_bin n).priority w < (G_bin n).priority topV)
    (hstep : HitsWithTop glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) p topV) :
    HitsWithTop glob n b s w p topV := by
  have hpath : predPath glob n b s w =
      insert w (predPath glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w)) :=
    pred_path_step glob n b s hvalid w hw
  refine ⟨hstep.1, ?_, ?_⟩
  · rw [hpath]; exact Finset.mem_insert_of_mem hstep.2.1
  · intro u hu
    rw [hpath, Finset.mem_insert]
    have hne : u ≠ w := by intro heq; subst heq; omega
    simp only [hne, false_or]
    exact hstep.2.2 u hu

lemma hitsWithTop_of_step_gt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w p topV : V_bin n) (hw : w ≠ .x)
    (hrank : predRank0 glob n b s p < predRank0 glob n b s w)
    (hprio : (G_bin n).priority topV < (G_bin n).priority w)
    (hstep : HitsWithTop glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) p topV) :
    HitsWithTop glob n b s w p w := by
  have hpath : predPath glob n b s w =
      insert w (predPath glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w)) :=
    pred_path_step glob n b s hvalid w hw
  refine ⟨hrank, ?_, ?_⟩
  · rw [hpath]; exact Finset.mem_insert_self w _
  · intro u hu
    rw [hpath, Finset.mem_insert]
    have hne : u ≠ w := by intro heq; subst heq; omega
    simp only [hne, false_or]
    exact hstep.2.2 u (by omega)

lemma predVal_lt_of_hitsWithTop_even_self (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w p topV : V_bin n} (h : HitsWithTop glob n b s w p topV)
    (heven : (G_bin n).priority topV % 2 = 0) :
    ValueLT (G_bin n) (predVal glob n b s p) (predVal glob n b s w) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := topV)
  · exact pred_not_mem_path_of_rank_lt glob n b s hvalid p topV h.1
  · exact h.2.1
  · exact heven
  · intro u hu
    exact (h.2.2 u hu).symm

lemma predVal_lt_of_hitsWithTop_odd_self (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w p topV : V_bin n} (h : HitsWithTop glob n b s w p topV)
    (hodd : (G_bin n).priority topV % 2 = 1) :
    ValueLT (G_bin n) (predVal glob n b s w) (predVal glob n b s p) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := topV)
  · exact h.2.1
  · exact pred_not_mem_path_of_rank_lt glob n b s hvalid p topV h.1
  · exact hodd
  · intro u hu
    exact h.2.2 u hu

lemma predVal_lt_of_hitsWithTop_even (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w₁ w₂ p top₁ top₂ : V_bin n}
    (h₁ : HitsWithTop glob n b s w₁ p top₁)
    (h₂ : HitsWithTop glob n b s w₂ p top₂)
    (hprio : (G_bin n).priority top₁ < (G_bin n).priority top₂)
    (heven : (G_bin n).priority top₂ % 2 = 0) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := top₂)
  · rw [h₁.2.2 top₂ hprio]
    exact pred_not_mem_path_of_rank_lt glob n b s hvalid p top₂ h₂.1
  · exact h₂.2.1
  · exact heven
  · intro u hu
    rw [h₁.2.2 u (by omega), h₂.2.2 u hu]

lemma predVal_lt_of_hitsWithTop_odd (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w₁ w₂ p top₁ top₂ : V_bin n}
    (h₁ : HitsWithTop glob n b s w₁ p top₁)
    (h₂ : HitsWithTop glob n b s w₂ p top₂)
    (hprio : (G_bin n).priority top₂ < (G_bin n).priority top₁)
    (hodd : (G_bin n).priority top₁ % 2 = 1) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := top₁)
  · exact h₁.2.1
  · rw [h₂.2.2 top₁ hprio]
    exact pred_not_mem_path_of_rank_lt glob n b s hvalid p top₁ h₁.1
  · exact hodd
  · intro u hu
    rw [h₁.2.2 u hu, h₂.2.2 u (by omega)]

def PortalOrderProp (glob : Bool) (n b s : ℕ) : Prop :=
  if b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2) then
    ∀ w₁ w₂, HitsPortal glob n b s w₁ .c → HitsPortal glob n b s w₂ .r →
      ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂)
  else
    ∀ w₁ w₂, HitsPortal glob n b s w₁ .r → HitsPortal glob n b s w₂ .c →
      ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂)

end FriedmannParity
