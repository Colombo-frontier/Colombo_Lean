import SecondOrder.OjaRawRun
import SecondOrder.OjaStepMoments

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

def ojaUpdateOperator {d : ℕ} (η : ℝ) (A : Point d →L[ℝ] Point d) :
    Point d →L[ℝ] Point d := ContinuousLinearMap.id ℝ (Point d) + η • A

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaRawRun_norm_bound (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (N : ℕ) :
    ∀ᵐ w ∂drawsLaw μ N, ∀ (x v : Point d),
      ‖ojaRawRun P f η x v N w‖ ≤ (1 + η)^N * ‖v‖ := by
  induction N with
  | zero => filter_upwards with w x v; simp [ojaRawRun]
  | succ N ih =>
    have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae ih
    have hz := (Measure.quasiMeasurePreserving_snd (μ := drawsLaw μ N) (ν := μ)).ae
      h.shifted_hessian_good
    filter_upwards [hp, hz] with w hw hz
    intro x v
    calc
      _ ≤ (1 + η) * ‖ojaRawRun P f η x v N w.1‖ :=
        ojaUpdate_norm_upper hη (hz x).2.1 _
      _ ≤ (1 + η) * ((1 + η)^N * ‖v‖) :=
        mul_le_mul_of_nonneg_left (hw x v) (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem CommonLoss.ojaRawRun_integrable (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) (N : ℕ) :
    Integrable (ojaRawRun P f η x v N) (drawsLaw μ N) := by
  have hg : Measurable (fun w : Draws Ω N => ((x,v),w)) :=
    measurable_const.prodMk measurable_id
  have hm : Measurable (ojaRawRun P f η x v N) :=
    (h.ojaRawRun_measurable η N).comp hg
  apply (integrable_const ((1 + η)^N * ‖v‖)).mono' hm.aestronglyMeasurable
  filter_upwards [h.ojaRawRun_norm_bound hη N] with w hw
  exact hw x v

theorem CommonLoss.ojaRawRun_norm_pow_integrable (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) (N k : ℕ) :
    Integrable (fun w => ‖ojaRawRun P f η x v N w‖^k) (drawsLaw μ N) := by
  have hg : Measurable (fun w : Draws Ω N => ((x,v),w)) :=
    measurable_const.prodMk measurable_id
  have hm : Measurable (ojaRawRun P f η x v N) :=
    (h.ojaRawRun_measurable η N).comp hg
  apply (integrable_const (((1 + η)^N * ‖v‖)^k)).mono'
    (hm.norm.pow_const k).aestronglyMeasurable
  filter_upwards [h.ojaRawRun_norm_bound hη N] with w hw
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) k)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hw x v) k

/-- Independence of the successive samples yields the actual N-step fourth
moment, with no dimension factor introduced by a matrix norm estimate. -/
theorem CommonLoss.ojaRawRun_fourth_moment (h : CommonLoss μ P ν F f)
    {η ℓ : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hℓ0 : 0 ≤ ℓ) (x v : Point d)
    (hℓ : ∀ u, ⟪shiftedHessian (eigenHessianBound P) (hessian F x) u, u⟫_ℝ ≤ ℓ * ‖u‖^2)
    (N : ℕ) : (∫ w, ‖ojaRawRun P f η x v N w‖^4 ∂drawsLaw μ N) ≤
      (1 + (4 * η + 11 * η^2) * ℓ)^N * ‖v‖^4 := by
  induction N with
  | zero => simp [ojaRawRun]
  | succ N ih =>
    have hi := h.ojaRawRun_norm_pow_integrable hη x v (N+1) 4
    change Integrable (fun w : Draws Ω N × Ω =>
      ‖ojaUpdate η (sampledShiftedHessian P f x w.2) (ojaRawRun P f η x v N w.1)‖^4)
      ((drawsLaw μ N).prod μ) at hi
    change (∫ w : Draws Ω N × Ω,
      ‖ojaUpdate η (sampledShiftedHessian P f x w.2) (ojaRawRun P f η x v N w.1)‖^4
      ∂(drawsLaw μ N).prod μ) ≤ _
    rw [integral_prod _ hi]
    change (∫ w, (∫ z, ‖ojaUpdate η (sampledShiftedHessian P f x z)
      (ojaRawRun P f η x v N w)‖^4 ∂μ) ∂drawsLaw μ N) ≤ _
    have hb := integral_mono_of_nonneg
      (Eventually.of_forall (fun w => integral_nonneg (fun z => by positivity)))
      ((h.ojaRawRun_norm_pow_integrable hη x v N 4).const_mul
        (1 + (4 * η + 11 * η^2) * ℓ))
      (Eventually.of_forall (fun w => h.ojaUpdate_fourth_moment hη hη1 x
        (ojaRawRun P f η x v N w) (hℓ _)))
    rw [integral_const_mul] at hb
    calc
      _ ≤ (1 + (4 * η + 11 * η^2) * ℓ) *
          (∫ w, ‖ojaRawRun P f η x v N w‖^4 ∂drawsLaw μ N) := hb
      _ ≤ (1 + (4 * η + 11 * η^2) * ℓ) *
          ((1 + (4 * η + 11 * η^2) * ℓ)^N * ‖v‖^4) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- Starting in an eigendirection of the mean operator gives an exact mean
for the unnormalized product, rather than a postulated growth estimate. -/
theorem CommonLoss.ojaRawRun_mean_eigenvector (h : CommonLoss μ P ν F f)
    {η ℓ : ℝ} (hη : 0 ≤ η) (x v : Point d)
    (hv : shiftedHessian (eigenHessianBound P) (hessian F x) v = ℓ • v) (N : ℕ) :
    (∫ w, ojaRawRun P f η x v N w ∂drawsLaw μ N) = (1 + η * ℓ)^N • v := by
  induction N with
  | zero => simp [ojaRawRun]
  | succ N ih =>
    have hi := h.ojaRawRun_integrable hη x v (N+1)
    change Integrable (fun w : Draws Ω N × Ω =>
      ojaUpdate η (sampledShiftedHessian P f x w.2) (ojaRawRun P f η x v N w.1))
      ((drawsLaw μ N).prod μ) at hi
    change (∫ w : Draws Ω N × Ω,
      ojaUpdate η (sampledShiftedHessian P f x w.2) (ojaRawRun P f η x v N w.1)
      ∂(drawsLaw μ N).prod μ) = _
    rw [integral_prod _ hi]
    change (∫ w, (∫ z, ojaUpdate η (sampledShiftedHessian P f x z)
      (ojaRawRun P f η x v N w) ∂μ) ∂drawsLaw μ N) = _
    simp_rw [h.ojaUpdate_mean]
    change (∫ w, ojaUpdateOperator η (shiftedHessian (eigenHessianBound P) (hessian F x))
      (ojaRawRun P f η x v N w) ∂drawsLaw μ N) = _
    rw [ContinuousLinearMap.integral_comp_comm _ (h.ojaRawRun_integrable hη x v N), ih]
    have hop : ojaUpdateOperator η (shiftedHessian (eigenHessianBound P) (hessian F x)) v =
        (1 + η * ℓ) • v := by
      change v + η • (shiftedHessian (eigenHessianBound P) (hessian F x) v) = _
      rw [hv, smul_smul, add_smul, one_smul]
    rw [map_smul, hop, smul_smul, pow_succ]

theorem CommonLoss.ojaRawRun_second_moment_lower (h : CommonLoss μ P ν F f)
    {η ℓ : ℝ} (hη : 0 ≤ η) (x v : Point d)
    (hv : shiftedHessian (eigenHessianBound P) (hessian F x) v = ℓ • v)
    (hv1 : ‖v‖ = 1) (N : ℕ) :
    (1 + η * ℓ)^(2 * N) ≤ ∫ w, ‖ojaRawRun P f η x v N w‖^2 ∂drawsLaw μ N := by
  have hj := norm_integral_sq_le (h.ojaRawRun_integrable hη x v N)
    (h.ojaRawRun_norm_pow_integrable hη x v N 2)
  rw [h.ojaRawRun_mean_eigenvector hη x v hv N, norm_smul, hv1, mul_one,
    Real.norm_eq_abs, sq_abs, ← pow_mul] at hj
  simpa only [Nat.mul_comm N 2] using hj

end
end SecondOrder
