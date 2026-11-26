import GradientHessian.CensoredMarkOrder
import GradientHessian.CensoredJointOracle
import GradientHessian.GeometricMarkErasure

/-! Actual raw-factor erasure for both full physical oracle decoders. The
only stopping premise is that the target mark has not been supplied. -/

noncomputable section
namespace GradientHessian.CensoredMark
open Classical HigherHierarchy HierarchyAddresses RawHierarchy CensoredHierarchy
  CensoredOracle HierarchyParameters ControllerCensor FrontierState TaskState

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (target : Leaf (t+1)) (j : Fin (4096*J^2+1)) (x y : Raw d n r J E H t)
  (he : (RawMarkFactor.factor t ((leafEquiv t).symm target) j x).2=
    (RawMarkFactor.factor t ((leafEquiv t).symm target) j y).2)

include he in
theorem selectedMatrix_eq (p : Plan (4096*J^2) t) :
    selectedMatrix t p (assemble P B fallback t x)=selectedMatrix t p (assemble P B fallback t y) := by
  unfold CensoredOracle.selectedMatrix
  by_cases hi : selectedLeaf (4096*J^2) t p=(leafEquiv t).symm target
  · rw [hi]
    exact RawMarkLocality.rest_eq_target_A P B fallback t _ j x y he
  · exact congrArg LeafCoefficients.A (RawMarkLocality.rest_eq_other_leaf P B fallback t _ j x y he _ hi)

include he in
theorem controller_sameKnown (before after : State (t+1) (4096*J^2+1) ell)
    (cur : Leaf (t+1)) (hc : TaskState.current before=some cur)
    (hs : ComparisonControllerReplay.markSupplied target j before=false) :
    SameKnown t (planAt before after cur hc t) (coefficients P B fallback t x) (coefficients P B fallback t y) :=
  sameKnown_of_future P B fallback t _ _ j x y he (future_controller before after cur target hc j hs)

include he in
theorem controller_ordinary_eq {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) (cur : Leaf (t+1))
    (hc : TaskState.current before=some cur)
    (hs : ComparisonControllerReplay.markSupplied target j before=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Ay : EuclideanSpace ℝ (Fin d)) :
    ordinaryDecoder K t (planAt before after cur hc t) ((coefficients P B fallback t x,Z),Ay)=
      ordinaryDecoder K t (planAt before after cur hc t) ((coefficients P B fallback t y,Z),Ay) :=
  ordinaryDecoder_erasure hK t _ _ _ (controller_sameKnown P B fallback t target j x y he before after cur hc hs) Z Ay

include he in
theorem controller_rich_eq {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) (cur : Leaf (t+1))
    (hc : TaskState.current before=some cur)
    (hs : ComparisonControllerReplay.markSupplied target j before=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    richDecoder K t (planAt before after cur hc t) (coefficients P B fallback t x,Z)=
      richDecoder K t (planAt before after cur hc t) (coefficients P B fallback t y,Z) := by
  apply richDecoder_erasure hK t _ _ _
    (controller_sameKnown P B fallback t target j x y he before after cur hc hs)
  simpa only [decode_coefficients] using selectedMatrix_eq P B fallback t target j x y he _

include he in
theorem controller_product_reply_eq {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) (cur : Leaf (t+1))
    (hc : TaskState.current before=some cur)
    (hs : ComparisonControllerReplay.markSupplied target j before=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    ordinaryDecoder K t (planAt before after cur hc t) ((coefficients P B fallback t x,Z),
      selectedMatrix t (planAt before after cur hc t) (assemble P B fallback t x) (numericalMap t Z))=
    ordinaryDecoder K t (planAt before after cur hc t) ((coefficients P B fallback t y,Z),
      selectedMatrix t (planAt before after cur hc t) (assemble P B fallback t y) (numericalMap t Z)) := by
  rw [selectedMatrix_eq P B fallback t target j x y he]
  exact controller_ordinary_eq P B fallback t target j x y he hK before after cur hc hs Z _

theorem controller_rich_factors {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) (cur : Leaf (t+1))
    (hc : TaskState.current before=some cur)
    (hs : ComparisonControllerReplay.markSupplied target j before=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    richDecoder K t (planAt before after cur hc t) (coefficients P B fallback t x,Z)=
      richDecoder K t (planAt before after cur hc t)
        (coefficients P B fallback t ((RawMarkFactor.factor t ((leafEquiv t).symm target) j).symm
          (0,(RawMarkFactor.factor t ((leafEquiv t).symm target) j x).2)),Z) := by
  apply controller_rich_eq P B fallback t target j x _ _ hK before after cur hc hs Z
  simp only [MeasurableEquiv.apply_symm_apply]

end GradientHessian.CensoredMark
