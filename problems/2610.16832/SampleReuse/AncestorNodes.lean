import SampleReuse.TreeEstimator
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! The literal binary-ancestor edge `k - 2^(v₂(k)) → k`. Useful dyadic
nodes are in bijection with positive checkpoint indices, not all dyadic
nodes. Hence the actual estimator creates exactly one edge per checkpoint. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def ancestorParent (k : ℕ) : ℕ := k - 2 ^ padicValNat 2 k

theorem usefulNode_valuation {depth : ℕ} (i : BinaryNode depth) (hi : usefulNode i) :
    padicValNat 2 (nodeRight i) = i.1.val := by
  have hn : ¬ 2 ∣ i.2 + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    unfold usefulNode at hi
    omega
  rw [nodeRight, padicValNat.mul (by omega) (by positivity),
    padicValNat.eq_zero_of_not_dvd hn, padicValNat.prime_pow, zero_add]

theorem usefulNode_parent {depth : ℕ} (i : BinaryNode depth) (hi : usefulNode i) :
    ancestorParent (nodeRight i) = nodeLeft i := by
  rw [ancestorParent, usefulNode_valuation i hi]
  unfold nodeRight nodeLeft
  rw [Nat.add_mul, one_mul, Nat.add_sub_cancel]

theorem usefulNode_right_injective {depth : ℕ} {i j : BinaryNode depth}
    (hi : usefulNode i) (hj : usefulNode j) (he : nodeRight i = nodeRight j) : i = j := by
  have hlevel : i.1 = j.1 := Fin.ext (by
    rw [← usefulNode_valuation i hi, ← usefulNode_valuation j hj, he])
  apply Prod.ext hlevel
  have hnum := he
  unfold nodeRight at hnum
  rw [hlevel] at hnum
  exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ j.1.val) hnum)

theorem valuation_lt_depth {k depth : ℕ} (hk : 0 < k) (hdepth : k < 2 ^ depth) :
    padicValNat 2 k < depth := by
  have hpow : 2 ^ padicValNat 2 k ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
  exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp (hpow.trans_lt hdepth)

def ancestorNode {depth : ℕ} (k : ℕ) (hk : 0 < k) (hdepth : k < 2 ^ depth) : BinaryNode depth :=
  (⟨padicValNat 2 k, valuation_lt_depth hk hdepth⟩, k / 2 ^ padicValNat 2 k - 1)

theorem ancestorNode_useful {depth : ℕ} (k : ℕ) (hk : 0 < k) (hdepth : k < 2 ^ depth) :
    usefulNode (ancestorNode k hk hdepth) := by
  have hpow : 2 ^ padicValNat 2 k ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
  have hq : 0 < k / 2 ^ padicValNat 2 k := Nat.div_pos hpow (by positivity)
  have hv : padicValNat 2 (k / 2 ^ padicValNat 2 k) = 0 := by
    rw [padicValNat.div_pow pow_padicValNat_dvd, Nat.sub_self]
  have hnot : ¬ 2 ∣ k / 2 ^ padicValNat 2 k := by
    simpa only [padicValNat.eq_zero_iff, show (2 : ℕ) ≠ 1 by decide,
      hq.ne', false_or] using hv
  rw [Nat.dvd_iff_mod_eq_zero] at hnot
  unfold usefulNode ancestorNode
  dsimp only
  omega

theorem ancestorNode_right {depth : ℕ} (k : ℕ) (hk : 0 < k) (hdepth : k < 2 ^ depth) :
    nodeRight (ancestorNode k hk hdepth) = k := by
  have hpow : 2 ^ padicValNat 2 k ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
  have hq : 0 < k / 2 ^ padicValNat 2 k := Nat.div_pos hpow (by positivity)
  simp only [nodeRight, ancestorNode]
  rw [Nat.sub_add_cancel hq, Nat.div_mul_cancel pow_padicValNat_dvd]

theorem ancestorNode_left {depth : ℕ} (k : ℕ) (hk : 0 < k) (hdepth : k < 2 ^ depth) :
    nodeLeft (ancestorNode k hk hdepth) = ancestorParent k := by
  rw [← usefulNode_parent _ (ancestorNode_useful k hk hdepth), ancestorNode_right]

theorem unique_ancestor_node {depth : ℕ} (k : ℕ) (hk : 0 < k) (hdepth : k < 2 ^ depth) :
    ∃! i : BinaryNode depth, usefulNode i ∧ nodeRight i = k := by
  refine ⟨ancestorNode k hk hdepth, ⟨ancestorNode_useful k hk hdepth, ancestorNode_right k hk hdepth⟩, ?_⟩
  intro i hi
  exact usefulNode_right_injective hi.1 (ancestorNode_useful k hk hdepth)
    (hi.2.trans (ancestorNode_right k hk hdepth).symm)

def ancestorNodes (depth M : ℕ) : Finset (BinaryNode depth) :=
  (completedNodes depth M).filter usefulNode

theorem ancestorNodes_image (depth M : ℕ) (hM : M < 2 ^ depth) :
    (ancestorNodes depth M).image nodeRight = Finset.Icc 1 M := by
  ext k
  constructor
  · rintro hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr ⟨nodeRight_pos i, (mem_completedNodes i).mp (Finset.mem_filter.mp hi).1⟩
  · intro hk
    have hk' := Finset.mem_Icc.mp hk
    let i := ancestorNode k hk'.1 (hk'.2.trans_lt hM)
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨?_, ancestorNode_useful k hk'.1 (hk'.2.trans_lt hM)⟩,
      ancestorNode_right k hk'.1 (hk'.2.trans_lt hM)⟩
    apply (mem_completedNodes i).mpr
    exact (ancestorNode_right k hk'.1 (hk'.2.trans_lt hM)).le.trans hk'.2

/-- Exactly one charged difference per nonroot checkpoint. -/
theorem ancestorNodes_card (depth M : ℕ) (hM : M < 2 ^ depth) :
    (ancestorNodes depth M).card = M := by
  have hinj : (ancestorNodes depth M : Set (BinaryNode depth)).InjOn nodeRight := by
    intro i hi j hj he
    exact usefulNode_right_injective (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 he
  rw [← Finset.card_image_of_injOn hinj, ancestorNodes_image depth M hM]
  simp

theorem selected_ancestor_card_le (depth M N : ℕ) (selected : completedNodes depth M → Prop)
    (hsel : ∀ i, selected i → usefulNode i.val ∧ nodeRight i.val ≤ N) :
    (Finset.univ.filter selected).card ≤ N := by
  have hc := Finset.card_le_card_of_injOn (s := Finset.univ.filter selected)
    (t := Finset.Icc 1 N) (fun i => nodeRight i.val)
    (fun i hi => Finset.mem_Icc.mpr ⟨nodeRight_pos i.val, (hsel i (Finset.mem_filter.mp hi).2).2⟩)
    (by
      intro i hi j hj he
      apply Subtype.ext
      exact usefulNode_right_injective (hsel i (Finset.mem_filter.mp hi).2).1
        (hsel j (Finset.mem_filter.mp hj).2).1 he)
  simpa using hc

theorem binaryActive_false_of_succ_dvd {n l : ℕ} (h : 2 ^ (l + 1) ∣ n) :
    ¬ binaryActive n l := by
  obtain ⟨r, rfl⟩ := h
  unfold binaryActive
  rw [pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ l)]
  omega

theorem even_successor_high_quotient {j r : ℕ} (hj : j % 2 = 0) (hr : 0 < r) :
    (j + 1) / 2 ^ r = j / 2 ^ r := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have he : (j + 1) / 2 = j / 2 := by omega
  rw [pow_succ, Nat.mul_comm (2 ^ s) 2, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, he]

theorem useful_node_high_quotient {depth : ℕ} (i : BinaryNode depth) (hi : usefulNode i)
    {l : ℕ} (hl : i.1.val < l) : nodeRight i / 2 ^ l = nodeLeft i / 2 ^ l := by
  have hpow : 2 ^ l = 2 ^ i.1.val * 2 ^ (l - i.1.val) := by
    rw [← pow_add, Nat.add_sub_of_le hl.le]
  rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  simp only [nodeRight, nodeLeft, Nat.mul_div_cancel _ (show 0 < 2 ^ i.1.val by positivity)]
  exact even_successor_high_quotient hi (Nat.sub_pos_of_lt hl)

theorem useful_node_low_inactive {depth : ℕ} (i : BinaryNode depth)
    {l : ℕ} (hl : l < i.1.val) :
    ¬ binaryActive (nodeRight i) l ∧ ¬ binaryActive (nodeLeft i) l := by
  have hdvd : 2 ^ (l + 1) ∣ 2 ^ i.1.val := pow_dvd_pow 2 (Nat.succ_le_of_lt hl)
  exact ⟨binaryActive_false_of_succ_dvd (hdvd.trans (dvd_mul_left _ _)),
    binaryActive_false_of_succ_dvd (hdvd.trans (dvd_mul_left _ _))⟩

theorem useful_node_own_activity {depth : ℕ} (i : BinaryNode depth) (hi : usefulNode i) :
    binaryActive (nodeRight i) i.1.val ∧ ¬ binaryActive (nodeLeft i) i.1.val := by
  unfold binaryActive nodeRight nodeLeft usefulNode at *
  rw [Nat.mul_div_cancel _ (show 0 < 2 ^ i.1.val by positivity),
    Nat.mul_div_cancel _ (show 0 < 2 ^ i.1.val by positivity)]
  omega

theorem useful_node_activeNode {depth : ℕ} (i : BinaryNode depth) :
    activeNode (nodeRight i) i.1 = i := by
  simp [activeNode, nodeRight, Nat.mul_div_cancel _ (show 0 < 2 ^ i.1.val by positivity)]

/-- Literal ancestor cache recurrence: the estimate at the right endpoint is
the cached estimate at the left endpoint plus its single fresh edge packet. -/
theorem binaryTracker_ancestor_update {E : Type*} [AddCommMonoid E] {depth : ℕ}
    (anchor : E) (packet : ℕ → BinaryNode depth → E) (i : BinaryNode depth)
    (hi : usefulNode i) :
    binaryTracker anchor packet (nodeRight i) =
      binaryTracker anchor packet (nodeLeft i) + packet (nodeRight i - 1) i := by
  have hlevel (l : Fin depth) : levelEstimate packet (nodeRight i) l =
      levelEstimate packet (nodeLeft i) l +
        if l = i.1 then packet (nodeRight i - 1) i else 0 := by
    rcases lt_trichotomy l.val i.1.val with hl | hl | hl
    · have hinact := useful_node_low_inactive i hl
      have hne : l ≠ i.1 := fun h => (Nat.ne_of_lt hl) (congrArg Fin.val h)
      simp [levelEstimate, hinact.1, hinact.2, hne]
    · have he : l = i.1 := Fin.ext hl
      subst l
      have hac := useful_node_own_activity i hi
      rw [levelEstimate_active packet _ _ hac.1, useful_node_activeNode]
      simp [levelEstimate, hac.2]
    · have heq := useful_node_high_quotient i hi hl
      have hact : binaryActive (nodeRight i) l.val ↔ binaryActive (nodeLeft i) l.val := by
        unfold binaryActive
        rw [heq]
      have hnode : activeNode (nodeRight i) l = activeNode (nodeLeft i) l := by
        unfold activeNode
        rw [heq]
      have hne : l ≠ i.1 := fun h => (Nat.ne_of_gt hl) (congrArg Fin.val h)
      by_cases ha : binaryActive (nodeRight i) l.val
      · rw [levelEstimate_active packet _ _ ha,
          levelEstimate_active packet _ _ (hact.mp ha), hnode, if_neg hne, add_zero]
      · have hb : ¬ binaryActive (nodeLeft i) l.val := fun h => ha (hact.mpr h)
        simp [levelEstimate, ha, hb, hne]
  unfold binaryTracker
  simp_rw [hlevel, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (add_assoc _ _ _).symm

theorem binaryTracker_lowbit_update {E : Type*} [AddCommMonoid E] {depth : ℕ}
    (anchor : E) (packet : ℕ → BinaryNode depth → E) (k : ℕ)
    (hk : 0 < k) (hdepth : k < 2 ^ depth) :
    binaryTracker anchor packet k = binaryTracker anchor packet (ancestorParent k) +
      packet (k - 1) (ancestorNode k hk hdepth) := by
  have h := binaryTracker_ancestor_update anchor packet (ancestorNode k hk hdepth)
    (ancestorNode_useful k hk hdepth)
  simpa only [ancestorNode_right, ancestorNode_left] using h

theorem ancestorParent_lt {k : ℕ} (hk : 0 < k) : ancestorParent k < k :=
  Nat.sub_lt hk (by positivity)

/-- Algorithm 2's actual recursive update from the cached parent. The input
`difference k` is the newly sampled same-handle difference at checkpoint k. -/
def ancestorEstimate {E : Type*} [Add E] (anchor : E) (difference : ℕ → E) : ℕ → E
  | 0 => anchor
  | k + 1 => ancestorEstimate anchor difference (ancestorParent (k + 1)) + difference (k + 1)
termination_by k => k
decreasing_by exact ancestorParent_lt (Nat.succ_pos _)

theorem binaryTracker_zero {E : Type*} [AddCommMonoid E] {depth : ℕ}
    (anchor : E) (packet : ℕ → BinaryNode depth → E) : binaryTracker anchor packet 0 = anchor := by
  simp [binaryTracker, levelEstimate, binaryActive]

/-- The literal cache recursion equals the logarithmic-depth readout already
used by the estimator accuracy theorem. No fictitious packets are sampled. -/
theorem ancestorEstimate_eq_binaryTracker {E : Type*} [AddCommMonoid E] {depth : ℕ}
    (anchor : E) (difference : ℕ → E) (k : ℕ) (hk : k < 2 ^ depth) :
    ancestorEstimate anchor difference k =
      binaryTracker (L := depth) anchor (fun _ i => difference (nodeRight i)) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp only [ancestorEstimate, binaryTracker_zero]
    | succ k =>
      have hparent := ancestorParent_lt (Nat.succ_pos k)
      rw [ancestorEstimate, ih _ hparent (hparent.trans hk)]
      have hupdate := binaryTracker_lowbit_update (depth := depth) anchor (fun _ i => difference (nodeRight i))
        (k + 1) (Nat.succ_pos k) hk
      simpa only [ancestorNode_right] using hupdate.symm

end
end SampleReuse
