import GradientHessian.AugmentedNumericalPacket
import GradientHessian.NumericalRichAgreement

/-! Actual augmented callbacks with one target matrix-vector reply. Packet
equality includes all already disclosed subtrees and completion directions. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalReplies
open Classical HigherHierarchy HierarchyAddresses HierarchyParameters RawHierarchy
  FrontierState TaskState GeometricRepair GeometricDisclosure AugmentedDisclosure
  NumericalCachedOracle NumericalCoefficientPatch ComparisonController ComparisonControllerReplay

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
  (fallback : Fin d → ℝ) (t : ℕ) (leaf : Leaf (t+1))

def ordinary (K : ℝ) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (before after : State (t+1) (4096*J^2+1) ell)
    (Z : DirectionPolicyReplay.Point d J E H t) (Ay : EuclideanSpace ℝ (Fin d)) :
    AugmentedPolicy.Ordinary d J E H t ell :=
  ((if TaskState.retired before⊆TaskState.retired after then
      NumericalPolicyReplies.ordinary P B fallback t leaf K w c before after Z Ay else 0),
    AugmentedNumericalPacket.packet P B fallback t leaf K w c after)

def rich (K : ℝ) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (before after : State (t+1) (4096*J^2+1) ell)
    (Z : DirectionPolicyReplay.Point d J E H t) : AugmentedPolicy.Rich d J E H t ell :=
  ((if TaskState.retired before⊆TaskState.retired after then
      NumericalPolicyReplies.rich P B fallback t leaf K w c before after Z else 0),
    AugmentedNumericalPacket.packet P B fallback t leaf K w c after)

omit [MeasurableSpace E] [∀ h,MeasurableSpace (H h)] in
theorem ordinary_guard (K : ℝ) (x : Raw d n r J E H t)
    (before after : State (t+1) (4096*J^2+1) ell) (j : Fin (4096*J^2+1))
    (hs : taskDisclosed leaf j after=false) (Z : DirectionPolicyReplay.Point d J E H t) :
    DirectionPolicy.ordinary K t (coefficients P B fallback t x) before after Z=
      if TaskState.retired before⊆TaskState.retired after then
        CensoredPolicy.ordinaryReply K t (coefficients P B fallback t x) before after Z else 0 := by
  unfold DirectionPolicy.ordinary
  split_ifs with hm
  · have hn : ¬j.val<(after.completed leaf).val := of_decide_eq_false hs
    rw [CensoredPolicy.completedOrdinary_active K t _ before after
      (DirectionPolicy.active_of_hidden_task before after hm leaf j hn)]
  · rfl

omit [MeasurableSpace E] [∀ h,MeasurableSpace (H h)] in
theorem rich_guard (K : ℝ) (x : Raw d n r J E H t)
    (before after : State (t+1) (4096*J^2+1) ell) (j : Fin (4096*J^2+1))
    (hs : taskDisclosed leaf j after=false) (Z : DirectionPolicyReplay.Point d J E H t) :
    DirectionPolicy.rich K t (coefficients P B fallback t x) before after Z=
      if TaskState.retired before⊆TaskState.retired after then
        CensoredPolicy.richReply K t (coefficients P B fallback t x) before after Z else 0 := by
  unfold DirectionPolicy.rich
  split_ifs with hm
  · have hn : ¬j.val<(after.completed leaf).val := of_decide_eq_false hs
    rw [CensoredPolicy.completedRich_active K t _ before after
      (DirectionPolicy.active_of_hidden_task before after hm leaf j hn)]
  · rfl

theorem ordinary_before_supply {K : ℝ} (hK : 0<K)
    (x : Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.2.1 k)
    (before after : State (t+1) (4096*J^2+1) ell)
    (hsb : markStop leaf j before=false) (hsa : markStop leaf j after=false)
    (Z : DirectionPolicyReplay.Point d J E H t) :
    ordinary P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z
      ((atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).1 (CensoredOracle.numericalMap t Z))=
      AugmentedPolicy.ordinary P B fallback K t x before after Z := by
  have hs : taskDisclosed leaf j after=false := by
    apply decide_eq_false
    exact fun h => (of_decide_eq_false hsa) (Or.inl h)
  apply Prod.ext
  · change (if _ then _ else _) = DirectionPolicy.ordinary _ _ _ _ _ _
    rw [ordinary_guard P B fallback t leaf K x before after j hs]
    split_ifs
    · exact NumericalCacheReplyAgreement.ordinary_before_supply P B fallback t leaf hK x c j hb ha
        before after (markStop_open leaf j before hsb) Z
    · rfl
  · exact AugmentedNumericalPacket.packet_before_supply P B fallback t leaf K x c j after hsa hb ha

theorem ordinary_after_supply {K : ℝ} (hK : 0<K)
    (x : Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.2.1 k)
    (before after : State (t+1) (4096*J^2+1) ell)
    (hc : TaskState.current before=some leaf) (hj : (before.completed leaf).val=j.val)
    (hs : taskDisclosed leaf j after=false) (Z : DirectionPolicyReplay.Point d J E H t) :
    ordinary P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z
      ((atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).1 (CensoredOracle.numericalMap t Z))=
      AugmentedPolicy.ordinary P B fallback K t x before after Z := by
  apply Prod.ext
  · change (if _ then _ else _) = DirectionPolicy.ordinary _ _ _ _ _ _
    rw [ordinary_guard P B fallback t leaf K x before after j hs]
    split_ifs
    · exact NumericalCacheReplyAgreement.ordinary_after_supply P B fallback t leaf hK x c j hb ha
        before after hc hj hs Z
    · rfl
  · exact AugmentedNumericalPacket.packet_before_disclosure P B fallback t leaf K x c j after hs hb ha

theorem rich_before_disclosure {K : ℝ} (hK : 0<K)
    (x : Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.2.1 k)
    (R : Rules (t+1) (4096*J^2+1) ell (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)))
    (p : Pending (DirectionPolicyReplay.Point d J E H t)) (hk : p.kind=.rich)
    (before after : State (t+1) (4096*J^2+1) ell) (he : after=normal R p before)
    (hs : taskDisclosed leaf j after=false) :
    rich P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after p.point=
      AugmentedPolicy.rich P B fallback K t x before after p.point := by
  apply Prod.ext
  · change (if _ then _ else _) = DirectionPolicy.rich _ _ _ _ _ _
    rw [rich_guard P B fallback t leaf K x before after j hs]
    split_ifs
    · exact NumericalRichAgreement.rich_after_supply P B fallback t leaf hK x c j R p hk before after he hs
    · rfl
  · exact AugmentedNumericalPacket.packet_before_disclosure P B fallback t leaf K x c j after hs hb ha

theorem rich_before_supply {K : ℝ} (hK : 0<K)
    (x : Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.2.1 k)
    (R : Rules (t+1) (4096*J^2+1) ell (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)))
    (p : Pending (DirectionPolicyReplay.Point d J E H t)) (hk : p.kind=.rich)
    (before after : State (t+1) (4096*J^2+1) ell) (he : after=normal R p before)
    (hs : markStop leaf j after=false) :
    rich P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after p.point=
      AugmentedPolicy.rich P B fallback K t x before after p.point := by
  have hd : taskDisclosed leaf j after=false := by
    apply decide_eq_false
    exact fun h => (of_decide_eq_false hs) (Or.inl h)
  apply Prod.ext
  · change (if _ then _ else _) = DirectionPolicy.rich _ _ _ _ _ _
    rw [rich_guard P B fallback t leaf K x before after j hd]
    split_ifs
    · exact NumericalRichAgreement.rich_before_supply P B fallback t leaf hK x c j R p hk before after he
        (markStop_open leaf j after hs)
    · rfl
  · exact AugmentedNumericalPacket.packet_before_supply P B fallback t leaf K x c j after hs hb ha

variable [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
  [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]

theorem ordinary_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      DirectionPolicyReplay.Point d J E H t) × EuclideanSpace ℝ (Fin d) =>
      ordinary P B fallback t leaf K q.1.1.1 q.1.1.2 before after q.1.2 q.2) := by
  apply Measurable.prodMk
  · by_cases hm : TaskState.retired before⊆TaskState.retired after
    · exact (by simpa only [if_pos hm] using
        NumericalPolicyReplies.ordinary_fixed_measurable (n := n) P B fallback t leaf hK before after)
    · simpa only [if_neg hm] using (measurable_const (a := (0 : DirectionPolicyReplay.Ordinary d J E H t)))
  · exact (AugmentedNumericalPacket.packet_fixed_measurable P B fallback t leaf K after).comp
      (measurable_fst.comp measurable_fst)

theorem rich_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : (RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      DirectionPolicyReplay.Point d J E H t => rich P B fallback t leaf K q.1.1 q.1.2 before after q.2) := by
  apply Measurable.prodMk
  · by_cases hm : TaskState.retired before⊆TaskState.retired after
    · exact (by simpa only [if_pos hm] using
        NumericalPolicyReplies.rich_fixed_measurable (n := n) P B fallback t leaf hK before after)
    · simpa only [if_neg hm] using (measurable_const (a := (0 : DirectionPolicyReplay.Rich d J E H t)))
  · exact (AugmentedNumericalPacket.packet_fixed_measurable P B fallback t leaf K after).comp measurable_fst

end GradientHessian.AugmentedNumericalReplies
