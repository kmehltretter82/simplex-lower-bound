import Definitions.Def_friedmann_parity
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace FriedmannParity

inductive V_bin (n : ℕ) : Type
  | x
  | r_2_odd | r_a | r_2 | c_odd | c | r | s
  | rp (i : Fin n) | sp (i : Fin n) | u (i : Fin n)
  | d1 (i : Fin n) | d2 (i : Fin n) | d3 (i : Fin n) | g (i : Fin n)
  | hy (i : Fin n) | hx (i : Fin n) | h (i : Fin n)
  | z (i : Fin n) | f (i : Fin n) | k (i : Fin n)
  | l1 (m : Fin (3 * n - 1)) | l2 (m : Fin (3 * n - 1)) | l3 (m : Fin (3 * n - 1))
  | lp1 (m : Fin (3 * n - 1)) | lp2 (m : Fin (3 * n - 1)) | lp3 (m : Fin (3 * n - 1))
  | a (j : Fin (3 * (3 * n - 1))) | b (j : Fin (3 * (3 * n - 1)))
  deriving DecidableEq

abbrev V_bin_Raw (n : ℕ) : Type :=
  (Fin 8 ⊕ (Fin 13 × Fin n)) ⊕ ((Fin 6 × Fin (3 * n - 1)) ⊕ (Fin 2 × Fin (3 * (3 * n - 1))))

def vBinToRaw (n : ℕ) : V_bin n → V_bin_Raw n
  | .x => Sum.inl (Sum.inl ⟨0, by omega⟩)
  | .r_2_odd => Sum.inl (Sum.inl ⟨1, by omega⟩)
  | .r_a => Sum.inl (Sum.inl ⟨2, by omega⟩)
  | .r_2 => Sum.inl (Sum.inl ⟨3, by omega⟩)
  | .c_odd => Sum.inl (Sum.inl ⟨4, by omega⟩)
  | .c => Sum.inl (Sum.inl ⟨5, by omega⟩)
  | .r => Sum.inl (Sum.inl ⟨6, by omega⟩)
  | .s => Sum.inl (Sum.inl ⟨7, by omega⟩)
  | .rp i => Sum.inl (Sum.inr (⟨0, by omega⟩, i))
  | .sp i => Sum.inl (Sum.inr (⟨1, by omega⟩, i))
  | .u i => Sum.inl (Sum.inr (⟨2, by omega⟩, i))
  | .d1 i => Sum.inl (Sum.inr (⟨3, by omega⟩, i))
  | .d2 i => Sum.inl (Sum.inr (⟨4, by omega⟩, i))
  | .d3 i => Sum.inl (Sum.inr (⟨5, by omega⟩, i))
  | .g i => Sum.inl (Sum.inr (⟨6, by omega⟩, i))
  | .hy i => Sum.inl (Sum.inr (⟨7, by omega⟩, i))
  | .hx i => Sum.inl (Sum.inr (⟨8, by omega⟩, i))
  | .h i => Sum.inl (Sum.inr (⟨9, by omega⟩, i))
  | .z i => Sum.inl (Sum.inr (⟨10, by omega⟩, i))
  | .f i => Sum.inl (Sum.inr (⟨11, by omega⟩, i))
  | .k i => Sum.inl (Sum.inr (⟨12, by omega⟩, i))
  | .l1 m => Sum.inr (Sum.inl (⟨0, by omega⟩, m))
  | .l2 m => Sum.inr (Sum.inl (⟨1, by omega⟩, m))
  | .l3 m => Sum.inr (Sum.inl (⟨2, by omega⟩, m))
  | .lp1 m => Sum.inr (Sum.inl (⟨3, by omega⟩, m))
  | .lp2 m => Sum.inr (Sum.inl (⟨4, by omega⟩, m))
  | .lp3 m => Sum.inr (Sum.inl (⟨5, by omega⟩, m))
  | .a j => Sum.inr (Sum.inr (⟨0, by omega⟩, j))
  | .b j => Sum.inr (Sum.inr (⟨1, by omega⟩, j))

def vBinFromRaw (n : ℕ) : V_bin_Raw n → V_bin n
  | Sum.inl (Sum.inl ⟨0, _⟩) => .x
  | Sum.inl (Sum.inl ⟨1, _⟩) => .r_2_odd
  | Sum.inl (Sum.inl ⟨2, _⟩) => .r_a
  | Sum.inl (Sum.inl ⟨3, _⟩) => .r_2
  | Sum.inl (Sum.inl ⟨4, _⟩) => .c_odd
  | Sum.inl (Sum.inl ⟨5, _⟩) => .c
  | Sum.inl (Sum.inl ⟨6, _⟩) => .r
  | Sum.inl (Sum.inl ⟨_, _⟩) => .s
  | Sum.inl (Sum.inr (⟨0, _⟩, i)) => .rp i
  | Sum.inl (Sum.inr (⟨1, _⟩, i)) => .sp i
  | Sum.inl (Sum.inr (⟨2, _⟩, i)) => .u i
  | Sum.inl (Sum.inr (⟨3, _⟩, i)) => .d1 i
  | Sum.inl (Sum.inr (⟨4, _⟩, i)) => .d2 i
  | Sum.inl (Sum.inr (⟨5, _⟩, i)) => .d3 i
  | Sum.inl (Sum.inr (⟨6, _⟩, i)) => .g i
  | Sum.inl (Sum.inr (⟨7, _⟩, i)) => .hy i
  | Sum.inl (Sum.inr (⟨8, _⟩, i)) => .hx i
  | Sum.inl (Sum.inr (⟨9, _⟩, i)) => .h i
  | Sum.inl (Sum.inr (⟨10, _⟩, i)) => .z i
  | Sum.inl (Sum.inr (⟨11, _⟩, i)) => .f i
  | Sum.inl (Sum.inr (⟨_, _⟩, i)) => .k i
  | Sum.inr (Sum.inl (⟨0, _⟩, m)) => .l1 m
  | Sum.inr (Sum.inl (⟨1, _⟩, m)) => .l2 m
  | Sum.inr (Sum.inl (⟨2, _⟩, m)) => .l3 m
  | Sum.inr (Sum.inl (⟨3, _⟩, m)) => .lp1 m
  | Sum.inr (Sum.inl (⟨4, _⟩, m)) => .lp2 m
  | Sum.inr (Sum.inl (⟨_, _⟩, m)) => .lp3 m
  | Sum.inr (Sum.inr (⟨0, _⟩, j)) => .a j
  | Sum.inr (Sum.inr (⟨_, _⟩, j)) => .b j

def vBinEquivRaw (n : ℕ) : V_bin n ≃ V_bin_Raw n where
  toFun := vBinToRaw n
  invFun := vBinFromRaw n
  left_inv v := by cases v <;> rfl
  right_inv x := by
    rcases x with (⟨⟨t, ht⟩⟩ | ⟨⟨t, ht⟩, i⟩) | (⟨⟨t, ht⟩, m⟩ | ⟨⟨t, ht⟩, j⟩)
    · rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;> try rfl
      omega
    · rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t <;> try rfl
      omega
    · rcases t with _ | _ | _ | _ | _ | _ | t <;> try rfl
      omega
    · rcases t with _ | _ | t <;> try rfl
      omega

instance (n : ℕ) : Fintype (V_bin n) :=
  Fintype.ofEquiv (V_bin_Raw n) (vBinEquivRaw n).symm

lemma card_V_bin_le (n : ℕ) (hn : 0 < n) : Fintype.card (V_bin n) ≤ 57 * n := by
  have hcard : Fintype.card (V_bin n) = Fintype.card (V_bin_Raw n) :=
    Fintype.card_congr (vBinEquivRaw n)
  rw [hcard]
  simp only [V_bin_Raw, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

def M_bin (n : ℕ) : ℕ := 3 * n - 1
def baseL_bin (n : ℕ) : ℕ := 6 * n
def shift_bin (n : ℕ) : ℕ := baseL_bin n + 12 * M_bin n + 8
def Na_bin (n : ℕ) : ℕ := 3 * M_bin n - 1
def top_bin (n : ℕ) : ℕ := shift_bin n + 12 * n + 4 * Na_bin n + 10
def tap_bin (n : ℕ) (i : Fin n) : Fin (3 * n - 1) := ⟨n + 2 * i.val, by omega⟩

def owner_bin (n : ℕ) : V_bin n → Bool
  | .x => true
  | .rp _ => false
  | .sp _ => false
  | .u i => if i.val = 0 then true else false
  | .l1 m => if m.val = 0 then true else false
  | .l3 _ => false
  | .l2 _ => false
  | .lp1 m => if m.val = 0 then true else false
  | .lp3 m => if m.val = 0 then true else false
  | .lp2 m => if m.val = 0 then true else false
  | .r_2_odd => true
  | .r_a => true
  | .r_2 => false
  | .c_odd => true
  | .c => true
  | .r => false
  | .s => false
  | .a j => if j.val = 0 ∨ j.val = 3 * M_bin n - 1 then true else false
  | .b _ => true
  | .d1 _ => false
  | .d2 _ => false
  | .d3 _ => false
  | .g _ => true
  | .hy _ => false
  | .hx _ => false
  | .h _ => false
  | .z _ => false
  | .f _ => true
  | .k _ => true

def priority_bin (n : ℕ) : V_bin n → ℕ
  | .x => 1
  | .rp i => 2 * (i.val + 1)
  | .sp i => 2 * n + 2 * (i.val + 1)
  | .u i => 4 * n + 2 * (i.val + 1)
  | .l1 m => baseL_bin n + 6 * M_bin n + 6 * (M_bin n - 1 - m.val) + 2
  | .l3 m => baseL_bin n + 6 * M_bin n + 6 * (M_bin n - 1 - m.val) + 4
  | .l2 m => baseL_bin n + 6 * M_bin n + 6 * (M_bin n - 1 - m.val) + 6
  | .lp1 m => baseL_bin n + 6 * m.val + 2
  | .lp3 m => baseL_bin n + 6 * m.val + 4
  | .lp2 m => baseL_bin n + 6 * m.val + 6
  | .r_2_odd => shift_bin n + 12 * n + 1
  | .r_a => top_bin n + 3
  | .r_2 => top_bin n + 4
  | .c_odd => top_bin n + 5
  | .c => top_bin n + 6
  | .r => top_bin n + 8
  | .s => top_bin n + 10
  | .a j => shift_bin n + 12 * n + 4 * (j.val + 1) + 1
  | .b k =>
      let a_idx := if k.val ≤ 2 then k.val else k.val - 1
      shift_bin n + 12 * n + 4 * (a_idx + 1) + 1 + (if k.val = 3 then 3 else 1)
  | .d1 i => shift_bin n + 12 * (i.val + 1) - 11
  | .d2 i => shift_bin n + 12 * (i.val + 1) - 9
  | .d3 i => shift_bin n + 12 * (i.val + 1) - 7
  | .g i => shift_bin n + 12 * (i.val + 1) - 6
  | .hy i => shift_bin n + 12 * (i.val + 1) - 5
  | .hx i => shift_bin n + 12 * (i.val + 1) - 3
  | .h i => shift_bin n + 12 * (i.val + 1) - 2
  | .z i => top_bin n + 10 + 4 * (i.val + 1) + 1
  | .f i => top_bin n + 10 + 4 * (i.val + 1) + 3
  | .k i => top_bin n + 10 + 4 * (i.val + 1) + 4

def bTarget (n : ℕ) (k : Fin (3 * (3 * n - 1))) : Fin (3 * (3 * n - 1)) :=
  if k.val ≤ 2 then k else ⟨k.val - 1, by have := k.isLt; omega⟩

def edge0 (n : ℕ) : V_bin n → V_bin n
  | .x => .x
  | .rp i => .f i
  | .sp i => .hx i
  | .u i => .h i
  | .l1 m => if m.val = 0 then .b ⟨0, by have := m.isLt; omega⟩ else .r_2_odd
  | .l3 _ => .r_2
  | .l2 _ => .r_2
  | .lp1 m => .l1 m
  | .lp3 m => .l3 m
  | .lp2 m => .l2 m
  | .r_2_odd => .r_2
  | .r_a => .r
  | .r_2 => .c_odd
  | .c_odd => .c
  | .c => .s
  | .r => .x
  | .s => .x
  | .a j => if j.val = 0 then .c else .r_a
  | .b k => .a (bTarget n k)
  | .d1 i => .lp1 (tap_bin n i)
  | .d2 i => .lp2 (tap_bin n i)
  | .d3 i => .lp3 (tap_bin n i)
  | .g i => .d1 i
  | .hy i => .f i
  | .hx i => .hy i
  | .h i => .hx i
  | .z _ => .x
  | .f i => .g i
  | .k i => .z i

def edge1 (n : ℕ) : V_bin n → V_bin n
  | .x => .x
  | .rp i => if h : i.val = 0 then .f i else .rp ⟨i.val - 1, by have := i.isLt; omega⟩
  | .sp i => if h : i.val = 0 then .hx i else .sp ⟨i.val - 1, by have := i.isLt; omega⟩
  | .u i => if h : i.val ≠ 0 ∧ i.val + 1 < n then .u ⟨i.val + 1, h.2⟩ else .h i
  | .l1 m => .b ⟨3 * m.val, by have := m.isLt; omega⟩
  | .l3 m => .b ⟨3 * m.val + 1, by have := m.isLt; omega⟩
  | .l2 m => .b ⟨3 * m.val + 2, by have := m.isLt; omega⟩
  | .lp1 m => if h : m.val = 0 then .l1 m else .lp1 ⟨m.val - 1, by have := m.isLt; omega⟩
  | .lp3 m => if h : m.val = 0 then .l3 m else .lp3 ⟨m.val - 1, by have := m.isLt; omega⟩
  | .lp2 m => if h : m.val = 0 then .l2 m else .lp2 ⟨m.val - 1, by have := m.isLt; omega⟩
  | .r_2_odd => .r_2
  | .r_a => .r
  | .r_2 => .r
  | .c_odd => .c
  | .c => .s
  | .r => if hn : 0 < n then .rp ⟨n - 1, by omega⟩ else .x
  | .s => if hn : 0 < n then .sp ⟨n - 1, by omega⟩ else .x
  | .a j =>
      if h0 : j.val = 0 then .c
      else if h1 : j.val = 3 * (3 * n - 1) - 1 then .r_a
      else .a ⟨j.val - 1, by have := j.isLt; omega⟩
  | .b k => .a (bTarget n k)
  | .d1 i => .d2 i
  | .d2 i => .d3 i
  | .d3 i => .g i
  | .g i => .k i
  | .hy i => .z i
  | .hx i => .z i
  | .h i => .z i
  | .z i => if h : i.val + 1 < n then .u ⟨i.val + 1, h⟩ else .x
  | .f i => .g i
  | .k i => .z i

def ι_bin (n : ℕ) : V_bin n → V_bin n
  | .x => .x
  | .rp i => if h : i.val = 0 then .f i else .rp ⟨i.val - 1, by have := i.isLt; omega⟩
  | .sp i => if h : i.val = 0 then .hx i else .sp ⟨i.val - 1, by have := i.isLt; omega⟩
  | .u i => .h i
  | .l1 m => if m.val = 0 then .b ⟨0, by have := m.isLt; omega⟩ else .r_2_odd
  | .l3 _ => .r_2
  | .l2 _ => .r_2
  | .lp1 m => if h : m.val = 0 then .l1 m else .lp1 ⟨m.val - 1, by have := m.isLt; omega⟩
  | .lp3 m => if h : m.val = 0 then .l3 m else .lp3 ⟨m.val - 1, by have := m.isLt; omega⟩
  | .lp2 m => if h : m.val = 0 then .l2 m else .lp2 ⟨m.val - 1, by have := m.isLt; omega⟩
  | .r_2_odd => .r_2
  | .r_a => .r
  | .r_2 => .c_odd
  | .c_odd => .c
  | .c => .s
  | .r => .x
  | .s => .x
  | .a j =>
      if h0 : j.val = 0 then .c
      else if h1 : j.val = 1 then .a ⟨0, by have := j.isLt; omega⟩
      else .r_a
  | .b k => .a (bTarget n k)
  | .d1 i => .lp1 (tap_bin n i)
  | .d2 i => .lp2 (tap_bin n i)
  | .d3 i => .lp3 (tap_bin n i)
  | .g i => .d1 i
  | .hy i => .z i
  | .hx i => .z i
  | .h i => .z i
  | .z _ => .x
  | .f i => .g i
  | .k i => .z i

def G_bin (n : ℕ) : Game (V_bin n) where
  owner := owner_bin n
  priority := priority_bin n
  edge v w := w = edge0 n v ∨ w = edge1 n v

lemma G_bin_binary (n : ℕ) : Binary (G_bin n) :=
  fun v => ⟨edge0 n v, edge1 n v, fun _ h => h⟩

lemma G_bin_has_out (n : ℕ) : ∀ v, ∃ w, (G_bin n).edge v w :=
  fun v => ⟨edge0 n v, Or.inl rfl⟩

lemma ι_bin_legal (n : ℕ) : Legal (G_bin n) false (ι_bin n) := by
  intro v _
  cases v with
  | a j =>
    have hj := j.isLt
    dsimp [G_bin, ι_bin, edge0, edge1]
    split_ifs with h0 h1 h2
    · left; rfl
    · omega
    · right
      congr 1
      ext
      dsimp
      omega
    · left; rfl
    · left; rfl
  | _ =>
    dsimp [G_bin, ι_bin, edge0, edge1]
    try split_ifs
    all_goals simp

def toFin (K : ℕ) (hK : 0 < K) (x : ℕ) : Fin K :=
  if hx : x < K then ⟨x, hx⟩ else ⟨0, hK⟩

lemma toFin_eq_of_val_eq {K : ℕ} (hK : 0 < K) (x : ℕ) (i : Fin K) (h : x = i.val) :
    toFin K hK x = i := by
  subst h
  dsimp [toFin]
  exact if_pos i.isLt

def invLp (n : ℕ) (hM : 0 < 3 * n - 1) (d : ℕ) : V_bin n :=
  let m := toFin (3 * n - 1) hM (d / 6)
  if d % 6 = 0 then .lp1 m
  else if d % 6 = 2 then .lp3 m
  else .lp2 m

def invL (n : ℕ) (hM : 0 < 3 * n - 1) (d : ℕ) : V_bin n :=
  let m := toFin (3 * n - 1) hM (M_bin n - 1 - d / 6)
  if d % 6 = 0 then .l1 m
  else if d % 6 = 2 then .l3 m
  else .l2 m

def invDGH (n : ℕ) (hn : 0 < n) (d : ℕ) : V_bin n :=
  let i := toFin n hn (d / 12)
  if d % 12 = 0 then .d1 i
  else if d % 12 = 2 then .d2 i
  else if d % 12 = 4 then .d3 i
  else if d % 12 = 5 then .g i
  else if d % 12 = 6 then .hy i
  else if d % 12 = 8 then .hx i
  else .h i

def invAB (n : ℕ) (h3M : 0 < 3 * (3 * n - 1)) (d : ℕ) : V_bin n :=
  if d % 4 = 0 then
    .a (toFin (3 * (3 * n - 1)) h3M (d / 4))
  else if d % 4 = 3 then
    .b (toFin (3 * (3 * n - 1)) h3M 3)
  else if d / 4 ≤ 2 then
    .b (toFin (3 * (3 * n - 1)) h3M (d / 4))
  else
    .b (toFin (3 * (3 * n - 1)) h3M (d / 4 + 1))

def invZFK (n : ℕ) (hn : 0 < n) (d : ℕ) : V_bin n :=
  let i := toFin n hn (d / 4)
  if d % 4 = 0 then .z i
  else if d % 4 = 2 then .f i
  else .k i

def invPriority (n : ℕ) (hn : 0 < n) (p : ℕ) : V_bin n :=
  have hM : 0 < 3 * n - 1 := by omega
  have h3M : 0 < 3 * (3 * n - 1) := by omega
  let M := M_bin n
  let base_l := baseL_bin n
  let shift := shift_bin n
  let top := top_bin n
  if p ≤ 1 then .x
  else if p ≤ 2 * n then
    .rp (toFin n hn ((p - 2) / 2))
  else if p ≤ 4 * n then
    .sp (toFin n hn ((p - 2 * n - 2) / 2))
  else if p ≤ 6 * n then
    .u (toFin n hn ((p - 4 * n - 2) / 2))
  else if p < base_l + 6 * M + 2 then
    invLp n hM (p - (base_l + 2))
  else if p < base_l + 12 * M + 2 then
    invL n hM (p - (base_l + 6 * M + 2))
  else if p ≤ shift + 12 * n then
    invDGH n hn (p - (shift + 1))
  else if p = shift + 12 * n + 1 then
    .r_2_odd
  else if p < top + 3 then
    invAB n h3M (p - (shift + 12 * n + 5))
  else if p = top + 3 then .r_a
  else if p = top + 4 then .r_2
  else if p = top + 5 then .c_odd
  else if p = top + 6 then .c
  else if p = top + 8 then .r
  else if p ≤ top + 10 then .s
  else
    invZFK n hn (p - (top + 15))

lemma ite_pos_eq {α : Type} {c : Prop} [Decidable c] {t e v : α} (hc : c) (ht : t = v) :
    (if c then t else e) = v := by
  rw [if_pos hc, ht]

lemma ite_neg_eq {α : Type} {c : Prop} [Decidable c] {t e v : α} (hc : ¬c) (he : e = v) :
    (if c then t else e) = v := by
  rw [if_neg hc, he]

lemma invPriority_priority (n : ℕ) (hn : 0 < n) (v : V_bin n) :
    invPriority n hn ((G_bin n).priority v) = v := by
  cases v <;>
  { dsimp only [G_bin, priority_bin, M_bin, baseL_bin, shift_bin, Na_bin, top_bin]
    try split_ifs
    all_goals try omega
    all_goals
      dsimp only [invPriority, invLp, invL, invDGH, invAB, invZFK, M_bin, baseL_bin, shift_bin, Na_bin, top_bin]
      repeat' (first | apply ite_neg_eq (by omega) | apply ite_pos_eq (by omega))
      try rfl
      try (congr 1; apply toFin_eq_of_val_eq; omega) }

lemma G_bin_priority_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (G_bin n).priority :=
  Function.LeftInverse.injective (invPriority_priority n hn)

lemma G_bin_wellFormed (n : ℕ) (hn : 0 < n) : WellFormed (G_bin n) :=
  ⟨G_bin_has_out n, G_bin_priority_injective n hn⟩

lemma G_bin_sink_edge (n : ℕ) : (G_bin n).edge .x .x := Or.inl rfl

lemma G_bin_sink_priority (n : ℕ) : (G_bin n).priority .x = 1 := rfl

lemma G_bin_gt_one_of_ne_sink (n : ℕ) (hn : 0 < n) (v : V_bin n) (hv : v ≠ .x) :
    1 < (G_bin n).priority v := by
  cases v <;>
  { dsimp [G_bin, priority_bin, M_bin, baseL_bin, shift_bin, Na_bin, top_bin]
    try contradiction
    try split_ifs
    all_goals omega }

lemma G_bin_priority_le (n : ℕ) (hn : 0 < n) (v : V_bin n) :
    (G_bin n).priority v ≤ 114 * n := by
  cases v <;>
  { dsimp [G_bin, priority_bin, M_bin, baseL_bin, shift_bin, Na_bin, top_bin]
    try split_ifs
    all_goals omega }

lemma G_bin_edgeCount_le (n : ℕ) (hn : 0 < n) : edgeCount (G_bin n) ≤ 114 * n := by
  classical
  let f : Bool × V_bin n → V_bin n × V_bin n :=
    fun p => (p.2, if p.1 then edge0 n p.2 else edge1 n p.2)
  have hsub : Finset.univ.filter (fun e : V_bin n × V_bin n => (G_bin n).edge e.1 e.2) ⊆
      Finset.univ.image f := by
    intro ⟨v, w⟩ hvw
    have hw : (G_bin n).edge v w := (Finset.mem_filter.mp hvw).2
    rw [Finset.mem_image]
    rcases hw with rfl | rfl
    · exact ⟨(true, v), Finset.mem_univ _, rfl⟩
    · exact ⟨(false, v), Finset.mem_univ _, rfl⟩
  have hcard1 : edgeCount (G_bin n) ≤ (Finset.univ.image f).card := by
    unfold edgeCount
    exact Finset.card_le_card hsub
  have hcard2 : (Finset.univ.image f).card ≤ (Finset.univ : Finset (Bool × V_bin n)).card :=
    Finset.card_image_le
  have hcard3 : (Finset.univ : Finset (Bool × V_bin n)).card = 2 * Fintype.card (V_bin n) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
  have hcardV := card_V_bin_le n hn
  omega

end FriedmannParity
