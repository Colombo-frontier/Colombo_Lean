import SecondOrder.Tracker
import SecondOrder.DyadicIntervals
import Mathlib.Data.Nat.Log

open scoped BigOperators Classical

namespace SecondOrder

/-- A dyadic interval is [j 2^l, (j+1) 2^l]. The level is bounded and the
index is unrestricted; a finite execution creates only a finite prefix. -/
abbrev BinaryNode (L : ℕ) := Fin L × ℕ

def nodeLeft {L : ℕ} (i : BinaryNode L) : ℕ := i.2*2^i.1.val
def nodeRight {L : ℕ} (i : BinaryNode L) : ℕ := (i.2+1)*2^i.1.val
def binaryCut (n l : ℕ) : ℕ := n/2^l*2^l
def binaryActive (n l : ℕ) : Prop := n/2^l%2 = 1

instance binaryActiveDecidable (n l : ℕ) : Decidable (binaryActive n l) := inferInstanceAs (Decidable (_ = _))

def activeNode {L : ℕ} (n : ℕ) (l : Fin L) : BinaryNode L := (l,n/2^l.val-1)

theorem nodeLeft_lt_right {L : ℕ} (i : BinaryNode L) : nodeLeft i < nodeRight i := by
  have hp : 0 < 2^i.1.val := by positivity
  dsimp [nodeLeft, nodeRight]
  nlinarith

theorem nodeRight_pos {L : ℕ} (i : BinaryNode L) : 0 < nodeRight i :=
  lt_of_le_of_lt (Nat.zero_le _) (nodeLeft_lt_right i)

theorem binaryCut_zero (n : ℕ) : binaryCut n 0 = n := by simp [binaryCut]

theorem binaryCut_le (n l : ℕ) : binaryCut n l ≤ n := Nat.div_mul_le_self _ _

theorem binaryCut_top {n L : ℕ} (h : n < 2^L) : binaryCut n L = 0 := by
  simp [binaryCut, Nat.div_eq_of_lt h]

theorem binaryCut_step (n l : ℕ) :
    binaryCut n l = binaryCut n (l+1)+(n/2^l%2)*2^l := by
  have he := Nat.mod_add_div (n/2^l) 2
  have hd : n/2^(l+1) = (n/2^l)/2 := by rw [Nat.div_div_eq_div_mul, pow_succ]
  unfold binaryCut
  rw [hd, pow_succ]
  nlinarith [congrArg (fun q : ℕ => q*2^l) he]

theorem binaryCut_mono_level (n l : ℕ) : binaryCut n (l+1) ≤ binaryCut n l := by
  rw [binaryCut_step n l]
  omega

theorem activeNode_endpoints {L : ℕ} (n : ℕ) (l : Fin L) (ha : binaryActive n l.val) :
    nodeLeft (activeNode n l) = binaryCut n (l.val+1) ∧
    nodeRight (activeNode n l) = binaryCut n l.val := by
  have hq : 0 < n/2^l.val := by
    have hr := Nat.mod_le (n/2^l.val) 2
    dsimp [binaryActive] at ha
    omega
  have he := binaryCut_step n l.val
  dsimp [binaryActive] at ha
  rw [ha, one_mul] at he
  have hs : n/2^l.val-1+1 = n/2^l.val := by omega
  constructor
  · dsimp [nodeLeft, activeNode, binaryCut]
    have ht := congrArg (fun q : ℕ => q*2^l.val) hs
    dsimp [binaryCut] at he
    nlinarith
  · dsimp [nodeRight, activeNode, binaryCut]
    rw [hs]

theorem inactive_cuts_equal (n l : ℕ) (ha : ¬ binaryActive n l) :
    binaryCut n l = binaryCut n (l+1) := by
  have hr := Nat.mod_lt (n/2^l) (by norm_num : 0 < 2)
  have hz : n/2^l%2 = 0 := by dsimp [binaryActive] at ha; omega
  simpa only [hz, zero_mul, add_zero] using binaryCut_step n l

/-- The canonical active intervals telescope, including zero-length gaps at
inactive levels. This proves the partition endpoint identity. -/
theorem binary_partition_telescopes {E : Type*} [AddCommGroup E]
    (G : ℕ → E) (n L : ℕ) (hn : n < 2^L) :
    (∑ l : Fin L, if binaryActive n l.val then
      G (nodeRight (activeNode n l))-G (nodeLeft (activeNode n l)) else 0) = G n-G 0 := by
  have he (l : Fin L) : (if binaryActive n l.val then
      G (nodeRight (activeNode n l))-G (nodeLeft (activeNode n l)) else 0) =
      G (binaryCut n l.val)-G (binaryCut n (l.val+1)) := by
    by_cases ha : binaryActive n l.val
    · rw [if_pos ha, (activeNode_endpoints n l ha).1, (activeNode_endpoints n l ha).2]
    · rw [if_neg ha, inactive_cuts_equal n l.val ha, sub_self]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun l => G (binaryCut n l)-G (binaryCut n (l+1)))]
  have ht := Finset.sum_range_sub (fun l => G (binaryCut n l)) L
  have hh : (∑ l ∈ Finset.range L, (G (binaryCut n l)-G (binaryCut n (l+1)))) =
      -(∑ l ∈ Finset.range L, (G (binaryCut n (l+1))-G (binaryCut n l))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    abel
  rw [hh, ht, binaryCut_zero, binaryCut_top hn]
  abel

/-- A logarithmic depth sufficient for every time up to the cap. -/
def binaryDepth (M : ℕ) : ℕ := Nat.log 2 M+1

theorem binaryDepth_sufficient {n M : ℕ} (hn : n ≤ M) : n < 2^(binaryDepth M) :=
  hn.trans_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) M)

end SecondOrder
