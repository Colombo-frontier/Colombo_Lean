import GradientHessian.AugmentedPolicyReplies
import GradientHessian.NumericalCachedOracle

/-! The complete augmented disclosure packet assembled from an external leaf
factor and a finite numerical cache. The target matrix is identically zero;
all memory completions and every other numerical leaf are retained exactly. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalPacket
open Classical HigherHierarchy HierarchyAddresses HierarchyParameters RawHierarchy
  FrontierState TaskState GeometricRepair GeometricDisclosure AugmentedDisclosure
  NumericalCachedOracle NumericalCoefficientPatch

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
  (fallback : Fin d → ℝ) (t : ℕ) (leaf : Leaf (t+1))

def packet (K : ℝ) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (s : State (t+1) (4096*J^2+1) ell) : AugmentedPolicy.Packet d J E H t ell :=
  let v := view K (assemble P B fallback t (restore t ((leafEquiv t).symm leaf) w)) s
  (s,(fun q => if q=leaf then 0 else v.2.1 q),
    (fun q k => if q=leaf then if MarkSupplied s leaf k then c.1 k else 0 else v.2.2.1 q k),
    (fun q k => if q=leaf then if TaskDisclosed s leaf k then c.2 k else 0 else v.2.2.2.1 q k),
    v.2.2.2.2)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [∀ h,InnerProductSpace ℝ (H h)] in
theorem restored_factor (x : Raw d n r J E H t) :
    (RawLeafFactor.factor t ((leafEquiv t).symm leaf)
      (restore t ((leafEquiv t).symm leaf) (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2)).2=
        (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 := by
  have he := congrArg (fun z : RawFirstFactor.Target d n r J × RawLeafFactor.Rest d n r J E H t => z.2)
    ((RawLeafFactor.factor t ((leafEquiv t).symm leaf)).apply_symm_apply
    ((0,0),(RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2))
  exact he

theorem packet_eq_view (K : ℝ) (x : Raw d n r J E H t) (c : Cache d J)
    (s : State (t+1) (4096*J^2+1) ell) (hret : leaf∉TaskState.retired s)
    (hb : ∀ k,MarkSupplied s leaf k → c.1 k=(leafCoefficients (assemble P B fallback t x) leaf).b k)
    (ha : ∀ k,TaskDisclosed s leaf k → c.2 k=(leafCoefficients (assemble P B fallback t x) leaf).a k) :
    packet P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c s=
      view K (assemble P B fallback t x) s := by
  let y := restore t ((leafEquiv t).symm leaf) (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2
  have he := restored_factor t leaf x
  have hother (q : Leaf (t+1)) (hq : q≠leaf) :
      leafCoefficients (assemble P B fallback t y) q=leafCoefficients (assemble P B fallback t x) q :=
    RawLeafLocality.rest_eq_other_leaf P B fallback t ((leafEquiv t).symm leaf) y x he
      ((leafEquiv t).symm q) (fun h => hq ((leafEquiv t).symm.injective h))
  have hdir (a : Action t (4096*J^2)) :
      direction K (assemble P B fallback t y) a=direction K (assemble P B fallback t x) a :=
    direction_eq_of_memory P B fallback K t y x
      (RawLeafLocality.rest_eq_memory t ((leafEquiv t).symm leaf) y x he) a
  dsimp only [packet,view]
  refine Prod.ext rfl ?_
  apply Prod.ext
  · funext q
    by_cases hq : q=leaf
    · subst q
      simp only [packet,if_true,view,matrix,if_neg hret]
    · simp only [packet,if_neg hq,view,matrix]
      rw [hother q hq]
  apply Prod.ext
  · funext q k
    by_cases hq : q=leaf
    · subst q
      simp only [packet,if_true,view,mark]
      split_ifs with hk
      · exact hb k hk
      · rfl
    · simp only [packet,if_neg hq,view,mark]
      rw [hother q hq]
  apply Prod.ext
  · funext q k
    by_cases hq : q=leaf
    · subst q
      simp only [packet,if_true,view,readout]
      split_ifs with hk
      · exact ha k hk
      · rfl
    · simp only [packet,if_neg hq,view,readout]
      rw [hother q hq]
  · funext a
    simp only [packet,view,completion]
    rw [hdir a]

omit [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)] in
theorem atLeaf_b : ∀ t (i : LeafSlot t) (x : Raw d n r J E H t),
    (atLeaf t i (coefficients P B fallback t x)).2.1=(leafData t (assemble P B fallback t x) i).b
  | 0,_,_ => rfl
  | t+1,i,x => atLeaf_b t i.2 (x.1 i.1)

omit [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)] in
theorem atLeaf_a : ∀ t (i : LeafSlot t) (x : Raw d n r J E H t),
    (atLeaf t i (coefficients P B fallback t x)).2.2.1=(leafData t (assemble P B fallback t x) i).a
  | 0,_,_ => rfl
  | t+1,i,x => atLeaf_a t i.2 (x.1 i.1)

theorem packet_before_disclosure (K : ℝ) (x : Raw d n r J E H t) (c : Cache d J)
    (j : Fin (4096*J^2+1)) (s : State (t+1) (4096*J^2+1) ell)
    (hs : ComparisonControllerReplay.taskDisclosed leaf j s=false)
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.2.1 k) :
    packet P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c s=
      view K (assemble P B fallback t x) s := by
  have hn : ¬j.val<(s.completed leaf).val := of_decide_eq_false hs
  have hj : (s.completed leaf).val≤j.val := Nat.le_of_not_gt hn
  apply packet_eq_view P B fallback t leaf K x c s
  · exact fun h => hn (retired_all_tasks_disclosed h j)
  · intro k hk
    have hk' : k≤j := by
      rcases hk with hk | ⟨_,hk⟩
      · change k.val<(s.completed leaf).val at hk
        exact Nat.le_trans (Nat.le_of_lt hk) hj
      · change k.val≤j.val
        omega
    simpa only [atLeaf_b,leafCoefficients] using hb k hk'
  · intro k hk
    have hk' : k<j := Nat.lt_of_lt_of_le hk hj
    simpa only [atLeaf_a,leafCoefficients] using ha k hk'

theorem packet_before_supply (K : ℝ) (x : Raw d n r J E H t) (c : Cache d J)
    (j : Fin (4096*J^2+1)) (s : State (t+1) (4096*J^2+1) ell)
    (hs : AugmentedDisclosure.markStop leaf j s=false)
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.2.1 k) :
    packet P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c s=
      view K (assemble P B fallback t x) s := by
  have hn : ¬MarkSupplied s leaf j := of_decide_eq_false hs
  have hj : (s.completed leaf).val≤j.val := by
    have h : ¬j.val<(s.completed leaf).val := fun h => hn (Or.inl h)
    omega
  apply packet_eq_view P B fallback t leaf K x c s
  · exact fun h => hn (Or.inl (retired_all_tasks_disclosed h j))
  · intro k hk
    have hk' : k<j := by
      rcases hk with hk | ⟨hc,hk⟩
      · exact Nat.lt_of_lt_of_le hk hj
      · have hne : j.val≠(s.completed leaf).val := fun h => hn (Or.inr ⟨hc,h⟩)
        change k.val<j.val
        omega
    simpa only [atLeaf_b,leafCoefficients] using hb k hk'
  · intro k hk
    have hk' : k<j := Nat.lt_of_lt_of_le hk hj
    simpa only [atLeaf_a,leafCoefficients] using ha k hk'

variable [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]

theorem packet_fixed_measurable (K : ℝ) (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : RawLeafFactor.Rest d n r J E H t × Cache d J =>
      packet P B fallback t leaf K q.1 q.2 s) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := borel _
  have hv := (view_fixed_measurable P B fallback t K s).comp
    ((restore_measurable t ((leafEquiv t).symm leaf)).comp
      (measurable_fst : Measurable (Prod.fst : RawLeafFactor.Rest d n r J E H t × Cache d J → _)))
  unfold packet
  apply measurable_const.prodMk
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro q
    split_ifs
    · exact measurable_const
    · exact (measurable_pi_apply q).comp hv.snd.fst
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro q
    apply measurable_pi_lambda
    intro k
    split_ifs
    · exact (measurable_pi_apply k).comp measurable_snd.fst
    · exact measurable_const
    · exact (measurable_pi_apply k).comp ((measurable_pi_apply q).comp hv.snd.snd.fst)
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro q
    apply measurable_pi_lambda
    intro k
    split_ifs
    · exact (measurable_pi_apply k).comp measurable_snd.snd
    · exact measurable_const
    · exact (measurable_pi_apply k).comp ((measurable_pi_apply q).comp hv.snd.snd.snd.fst)
  · exact hv.snd.snd.snd.snd

end GradientHessian.AugmentedNumericalPacket
