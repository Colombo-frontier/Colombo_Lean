import GradientHessian.NumericalFrontierOrder
import GradientHessian.NumericalPolicyReplies

/-! Reply equality from the exact finite prior cache. The current hidden
matrix enters only through its supplied product; future leaves are erased
by the already proved recursive coefficient view. -/

noncomputable section
namespace GradientHessian.NumericalCacheReplyAgreement
open Classical HigherHierarchy HierarchyParameters HierarchyAddresses CensoredHierarchy CensoredOracle
  ControllerCensor NumericalCachedOracle NumericalCoefficientPatch FrontierState TaskState
  ComparisonControllerReplay

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
  (fallback : Fin d → ℝ) (t : ℕ) (leaf : Leaf (t+1))

theorem ordinary_future {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (before after : State (t+1) (4096*J^2+1) ell) (cur : Leaf (t+1))
    (hc : TaskState.current before=some cur) (hne : cur≠leaf)
    (hf : FutureLeaf t (planAt before after cur hc t) ((leafEquiv t).symm leaf))
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Ay : EuclideanSpace ℝ (Fin d)) :
    NumericalPolicyReplies.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z Ay=
      CensoredPolicy.ordinaryReply K t (RawHierarchy.coefficients P B fallback t x) before after Z := by
  have hn : TaskState.current before≠some leaf := fun he => hne (Option.some.inj (hc.symm.trans he))
  rw [NumericalPolicyReplies.ordinary,dif_neg hn]
  rw [CensoredPolicy.ordinaryReply_current _ _ _ _ _ cur hc,CensoredPolicy.ordinaryReply_current _ _ _ _ _ cur hc]
  rw [cached_eq_patch,future_selectedMatrix t _ _ _ _ hf]
  exact (ordinaryDecoder_erasure hK t _ _ _ (future_sameKnown t _ _ _ _ hf) Z _).symm

theorem ordinary_current {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (before after : State (t+1) (4096*J^2+1) ell) (hc : TaskState.current before=some leaf)
    (hb : ∀ k,k≤(leafMask t (planAt before after leaf hc t)).current →
      c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<(leafMask t (planAt before after leaf hc t)).current ∨
      (k=(leafMask t (planAt before after leaf hc t)).current ∧
        (leafMask t (planAt before after leaf hc t)).readout=true) →
      c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    NumericalPolicyReplies.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z
        ((atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).1 (numericalMap t Z))=
      CensoredPolicy.ordinaryReply K t (RawHierarchy.coefficients P B fallback t x) before after Z := by
  rw [NumericalPolicyReplies.ordinary_current P B fallback t leaf hK x c before after hc hb ha,
    CensoredPolicy.ordinaryReply_current _ _ _ _ _ leaf hc,selectedMatrix_atLeaf,selectedLeaf_plan]

theorem ordinary_before_supply {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (before after : State (t+1) (4096*J^2+1) ell) (hs : markSupplied leaf j before=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    NumericalPolicyReplies.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z
        ((atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).1 (numericalMap t Z))=
      CensoredPolicy.ordinaryReply K t (RawHierarchy.coefficients P B fallback t x) before after Z := by
  cases hc : TaskState.current before with
  | none =>
      have hn : TaskState.current before≠some leaf := by simp [hc]
      rw [NumericalPolicyReplies.ordinary,dif_neg hn,
        CensoredPolicy.ordinaryReply_none _ _ _ _ _ hc,CensoredPolicy.ordinaryReply_none _ _ _ _ _ hc]
  | some cur =>
      by_cases he : cur=leaf
      · subst cur
        have hj := NumericalFrontierOrder.current_index_before_supply before after leaf hc j hs
        apply ordinary_current P B fallback t leaf hK x c before after hc
        · intro k hk
          exact hb k (hk.trans_lt hj)
        · intro k hk
          have hh : k≤(leafMask t (planAt before after leaf hc t)).current := by
            rcases hk with hk | ⟨hk,_⟩
            · exact hk.le
            · exact hk.le
          exact ha k (hh.trans_lt hj)
      · exact ordinary_future P B fallback t leaf hK x c before after cur hc he
          (NumericalFrontierOrder.futureLeaf_before_supply before after cur leaf hc j hs he) Z _

theorem ordinary_after_supply {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (before after : State (t+1) (4096*J^2+1) ell) (hc : TaskState.current before=some leaf)
    (hj : (before.completed leaf).val=j.val) (hs : taskDisclosed leaf j after=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    NumericalPolicyReplies.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z
        ((atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).1 (numericalMap t Z))=
      CensoredPolicy.ordinaryReply K t (RawHierarchy.coefficients P B fallback t x) before after Z := by
  have hcur : (leafMask t (planAt before after leaf hc t)).current=j := by
    rw [NumericalFrontierOrder.leafMask_current]
    exact Fin.ext hj
  have hread : (leafMask t (planAt before after leaf hc t)).readout=false := by
    rw [NumericalFrontierOrder.leafMask_current]
    change decide (GeometricDisclosure.TaskDisclosed after leaf ⟨(before.completed leaf).val,current_live before hc⟩)=false
    have he : (⟨(before.completed leaf).val,current_live before hc⟩ : Fin (4096*J^2+1))=j := Fin.ext hj
    rw [he]
    apply decide_eq_false
    have hn : ¬j.val<(after.completed leaf).val := of_decide_eq_false hs
    exact hn
  apply ordinary_current P B fallback t leaf hK x c before after hc
  · simpa only [hcur] using hb
  · intro k hk
    simp only [hcur,hread,Bool.false_eq_true,and_false,or_false] at hk
    exact ha k hk

end GradientHessian.NumericalCacheReplyAgreement
