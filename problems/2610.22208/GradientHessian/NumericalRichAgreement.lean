import GradientHessian.NumericalCacheReplyAgreement

/-! Rich receipts preserve the cached decoder whenever their actual normal
operation leaves the target matrix undisclosed. The receipt equation, not
an arbitrary pair of snapshots, supplies the needed frontier ordering. -/

noncomputable section
namespace GradientHessian.NumericalRichAgreement
open Classical HigherHierarchy HierarchyAddresses FrontierState TaskState TaskSlots
  ComparisonController ComparisonControllerReplay NumericalCachedOracle

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
  (fallback : Fin d → ℝ) (t : ℕ) (leaf : Leaf (t+1))

theorem rich_unretired {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (R : Rules (t+1) (4096*J^2+1) ell (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (GeometricRepair.Action t (4096*J^2)))
    (p : Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)) (hk : p.kind=.rich)
    (before after : State (t+1) (4096*J^2+1) ell) (ha : after=normal R p before)
    (hnr : leaf∉TaskState.retired after) :
    NumericalPolicyReplies.rich P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after p.point=
      CensoredPolicy.richReply K t (RawHierarchy.coefficients P B fallback t x) before after p.point := by
  cases hc : TaskState.current before with
  | none =>
    rw [NumericalPolicyReplies.rich,CensoredPolicy.richReply_none _ _ _ _ _ hc,
      CensoredPolicy.richReply_none _ _ _ _ _ hc]
  | some cur =>
    have he : after=retireSet before {cur} := by simpa [normal,hk,richComplete,hc] using ha
    have hb : leaf∉TaskState.retired before := by
      rw [he,retired_retireSet] at hnr
      exact fun hl => hnr (Finset.mem_union_left _ hl)
    have hn : cur≠leaf := by
      intro hh
      rw [he,retired_retireSet] at hnr
      apply hnr
      exact Finset.mem_union_right _ (by simp [hh])
    let j : Fin (4096*J^2+1) := ⟨0,by omega⟩
    have hs : markSupplied leaf j before=false := by
      simp [markSupplied,hb,hc,hn]
    exact NumericalPolicyReplies.rich_future P B fallback t leaf hK x c before after cur hc
      (NumericalFrontierOrder.futureLeaf_before_supply before after cur leaf hc j hs hn) p.point

theorem rich_before_supply {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (R : Rules (t+1) (4096*J^2+1) ell (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (GeometricRepair.Action t (4096*J^2)))
    (p : Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)) (hk : p.kind=.rich)
    (before after : State (t+1) (4096*J^2+1) ell) (ha : after=normal R p before)
    (hs : markSupplied leaf j after=false) :
    NumericalPolicyReplies.rich P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after p.point=
      CensoredPolicy.richReply K t (RawHierarchy.coefficients P B fallback t x) before after p.point := by
  apply rich_unretired P B fallback t leaf hK x c R p hk before after ha
  intro hl
  exact (of_decide_eq_false hs) (Or.inl hl)

theorem rich_after_supply {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (R : Rules (t+1) (4096*J^2+1) ell (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (GeometricRepair.Action t (4096*J^2)))
    (p : Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)) (hk : p.kind=.rich)
    (before after : State (t+1) (4096*J^2+1) ell) (ha : after=normal R p before)
    (hs : taskDisclosed leaf j after=false) :
    NumericalPolicyReplies.rich P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after p.point=
      CensoredPolicy.richReply K t (RawHierarchy.coefficients P B fallback t x) before after p.point := by
  apply rich_unretired P B fallback t leaf hK x c R p hk before after ha
  intro hl
  have he := (mem_retired _ _).mp hl
  have hh := of_decide_eq_false hs
  change ¬j.val<(after.completed leaf).val at hh
  apply hh
  simpa only [he] using j.isLt

end GradientHessian.NumericalRichAgreement
