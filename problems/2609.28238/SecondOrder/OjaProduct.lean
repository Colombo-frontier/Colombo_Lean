import SecondOrder.ReverseDraws
import SecondOrder.OjaRunMoments
import SecondOrder.RademacherTransfer

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

theorem measurable_point_adjoint_apply {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ}
    {L : Ξ → Point d →L[ℝ] Point d} (hL : Measurable L) (g : Point d) :
    Measurable (fun w => ContinuousLinearMap.adjoint (L w) g) := by
  have hc : Continuous (fun A : Point d →L[ℝ] Point d => ContinuousLinearMap.adjoint A g) :=
    ContinuousLinearMap.adjoint.continuous.clm_apply continuous_const
  exact hc.measurable.comp hL

def drawsAll {Ω : Type*} (Q : Ω → Prop) : (N : ℕ) → Draws Ω N → Prop
  | 0, _ => True
  | N+1, w => drawsAll Q N w.1 ∧ Q w.2

theorem drawsAll_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Q : Ω → Prop} (hQ : ∀ᵐ z ∂μ, Q z) (N : ℕ) :
    ∀ᵐ w ∂drawsLaw μ N, drawsAll Q N w := by
  induction N with
  | zero => exact Eventually.of_forall (fun _ => True.intro)
  | succ N ih =>
    have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae ih
    have hz := (Measure.quasiMeasurePreserving_snd (μ := drawsLaw μ N) (ν := μ)).ae hQ
    filter_upwards [hp,hz] with w hw hz
    exact ⟨hw,hz⟩

def linearDrawProduct {Ω : Type*} {d : ℕ} (A : Ω → Point d →L[ℝ] Point d) :
    (N : ℕ) → Draws Ω N → Point d →L[ℝ] Point d
  | 0, _ => ContinuousLinearMap.id ℝ (Point d)
  | N+1, w => (A w.2).comp (linearDrawProduct A N w.1)

theorem linearDrawProduct_prepend {Ω : Type*} {d : ℕ}
    (A : Ω → Point d →L[ℝ] Point d) (N : ℕ) (z : Ω) (w : Draws Ω N) :
    linearDrawProduct A (N+1) (prependDraw N (z,w)) =
      (linearDrawProduct A N w).comp (A z) := by
  induction N with
  | zero => simp [linearDrawProduct, prependDraw]
  | succ N ih =>
    change (A w.2).comp (linearDrawProduct A (N+1) (prependDraw N (z,w.1))) =
      ((A w.2).comp (linearDrawProduct A N w.1)).comp (A z)
    rw [ih, ContinuousLinearMap.comp_assoc]

theorem linearDrawProduct_adjoint_reverse {Ω : Type*} {d : ℕ}
    (A : Ω → Point d →L[ℝ] Point d) (N : ℕ) (w : Draws Ω N)
    (hs : drawsAll (fun z => ContinuousLinearMap.adjoint (A z) = A z) N w) :
    ContinuousLinearMap.adjoint (linearDrawProduct A N w) =
      linearDrawProduct A N (reverseDraws N w) := by
  induction N with
  | zero => simp [linearDrawProduct, ContinuousLinearMap.adjoint_id]
  | succ N ih =>
    change ContinuousLinearMap.adjoint ((A w.2).comp (linearDrawProduct A N w.1)) = _
    rw [ContinuousLinearMap.adjoint_comp, ih w.1 hs.1, hs.2]
    exact (linearDrawProduct_prepend A N w.2 (reverseDraws N w.1)).symm

theorem linearDrawProduct_measurable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {d : ℕ} {A : Ξ → Ω → Point d →L[ℝ] Point d}
    (hA : Measurable (fun w : Ξ × Ω => A w.1 w.2)) (N : ℕ) :
    Measurable (fun w : Ξ × Draws Ω N => linearDrawProduct (A w.1) N w.2) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have hlast : Measurable (fun w : Ξ × (Draws Ω N × Ω) => A w.1 w.2.2) :=
      hA.comp (measurable_fst.prodMk measurable_snd.snd)
    have hpast : Measurable (fun w : Ξ × (Draws Ω N × Ω) =>
        linearDrawProduct (A w.1) N w.2.1) :=
      ih.comp (measurable_fst.prodMk measurable_snd.fst)
    exact (continuous_fst.clm_comp continuous_snd).measurable.comp (hlast.prodMk hpast)

def ojaProduct {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x : Point d) (N : ℕ) (w : Draws Ω N) : Point d →L[ℝ] Point d :=
  linearDrawProduct (fun z => ojaUpdateOperator η (sampledShiftedHessian P f x z)) N w

theorem ojaProduct_apply {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) :
    ojaProduct P f η x N w v = ojaRawRun P f η x v N w := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change ojaUpdate η (sampledShiftedHessian P f x w.2) (ojaProduct P f η x N w.1 v) = _
    rw [ih]
    rfl

theorem ojaUpdateOperator_adjoint {d : ℕ} (η : ℝ) {A : Point d →L[ℝ] Point d}
    (hA : A.toLinearMap.IsSymmetric) :
    ContinuousLinearMap.adjoint (ojaUpdateOperator η A) = ojaUpdateOperator η A := by
  have ha : ContinuousLinearMap.adjoint A = A :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)
  simp [ojaUpdateOperator, map_add, map_smul, ContinuousLinearMap.adjoint_id, ha]

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaProduct_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : Point d × Draws Ω N => ojaProduct P f η w.1 N w.2) := by
  unfold ojaProduct
  apply linearDrawProduct_measurable (A := fun x z => ojaUpdateOperator η (sampledShiftedHessian P f x z))
  exact measurable_const.add ((h.shifted_hessian_measurable.comp measurable_swap).const_smul η)

theorem CommonLoss.ojaProduct_adjoint_reverse (h : CommonLoss μ P ν F f) (η : ℝ)
    (x : Point d) (N : ℕ) :
    ∀ᵐ w ∂drawsLaw μ N, ContinuousLinearMap.adjoint (ojaProduct P f η x N w) =
      ojaProduct P f η x N (reverseDraws N w) := by
  have hs : ∀ᵐ z ∂μ, ContinuousLinearMap.adjoint
      (ojaUpdateOperator η (sampledShiftedHessian P f x z)) =
        ojaUpdateOperator η (sampledShiftedHessian P f x z) := by
    filter_upwards [h.shifted_hessian_good] with z hz
    exact ojaUpdateOperator_adjoint η (hz x).1
  filter_upwards [drawsAll_ae hs N] with w hw
  exact linearDrawProduct_adjoint_reverse _ N w hw

end
end SecondOrder
