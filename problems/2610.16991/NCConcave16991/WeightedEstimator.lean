import NCConcave16991.PersistentEstimator
import NCConcave16991.Problem

/-! # Actual weighted persistent-estimator moments in Appendix B -/

open MeasureTheory
open scoped BigOperators

namespace NCConcave16991

noncomputable section

variable {n b dx dy : ℕ} [NeZero n] [MeasurableSpace (Fin n)]
  [MeasurableSingletonClass (Fin n)]

def weightedErrorSq (κ : ℝ) (z : JointSpace dx dy) : ℝ :=
  ‖z.fst‖ ^ 2 + κ * ‖z.snd‖ ^ 2

theorem weightedErrorSq_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (z : JointSpace dx dy) :
    0 ≤ weightedErrorSq κ z :=
  add_nonneg (sq_nonneg _) (mul_nonneg hκ (sq_nonneg _))

theorem weightedErrorSq_le_norm {κ : ℝ} (hκ : 1 ≤ κ) (z : JointSpace dx dy) :
    weightedErrorSq κ z ≤ κ * ‖z‖ ^ 2 := by
  have hz := WithLp.prod_norm_sq_eq_of_L2 z
  dsimp [weightedErrorSq]
  nlinarith [sq_nonneg ‖z.fst‖]

theorem linearMap_minibatchMean {H J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]
    [MeasurableSpace J] [BorelSpace J]
    (U : H →ₗ[ℝ] J) (v : Fin n → H) (I : Fin b → Fin n) :
    U (minibatchMean v I) = minibatchMean (fun i ↦ U (v i)) I := by
  simp [minibatchMean, map_sum]

theorem linearMap_minibatchError {H J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]
    [MeasurableSpace J] [BorelSpace J]
    (U : H →ₗ[ℝ] J) (v : Fin n → H) (I : Fin b → Fin n) :
    U (minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i) =
      minibatchMean (fun i ↦ U (v i)) I - (n : ℝ)⁻¹ • ∑ i, U (v i) := by
  simp [linearMap_minibatchMean, map_sum]

/-- The fresh cross term vanishes separately in both coordinates. The anchor
bias is arbitrary, so this does not assert that the persistent error is centered. -/
theorem weighted_minibatch_bias_second_moment (hb : 0 < b) (κ : ℝ)
    (v : Fin n → JointSpace dx dy) (bias : JointSpace dx dy) :
    (∫ I, weightedErrorSq κ (bias +
      (minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i)) ∂minibatchLaw n b) =
      weightedErrorSq κ bias +
        ∫ I, weightedErrorSq κ (minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i)
          ∂minibatchLaw n b := by
  let Ux := (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).toLinearMap
  let Uy := (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).toLinearMap
  have hx (I : Fin b → Fin n) := linearMap_minibatchError Ux v I
  have hy (I : Fin b → Fin n) := linearMap_minibatchError Uy v I
  simp only [weightedErrorSq, WithLp.add_fst, WithLp.add_snd]
  simp_rw [show ∀ I, (minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i).fst =
      minibatchMean (fun i ↦ (v i).fst) I - (n : ℝ)⁻¹ • ∑ i, (v i).fst from hx,
    show ∀ I, (minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i).snd =
      minibatchMean (fun i ↦ (v i).snd) I - (n : ℝ)⁻¹ • ∑ i, (v i).snd from hy]
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
    minibatch_bias_second_moment hb, minibatch_bias_second_moment hb,
    integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
  ring

/-- Universal weighted variance bound from AS. No weighted variance estimate
about sampled future iterates is assumed. -/
theorem AveragedSmooth.weighted_error_variance_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Fin n → E → JointSpace dx dy} {s : Set E} {L κ : ℝ}
    (hG : AveragedSmooth G s L) (hκ : 1 ≤ κ) (hb : 0 < b)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (∫ I, weightedErrorSq κ (minibatchMean (fun i ↦ G i x - G i y) I -
      (averageMap G x - averageMap G y)) ∂minibatchLaw n b) ≤
      κ * (L ^ 2 / b) * ‖x - y‖ ^ 2 := by
  have hpoint := integral_mono (μ := minibatchLaw n b) Integrable.of_finite
    Integrable.of_finite (fun I ↦ weightedErrorSq_le_norm hκ
      (minibatchMean (fun i ↦ G i x - G i y) I - (averageMap G x - averageMap G y)))
  rw [integral_const_mul] at hpoint
  have hv := mul_le_mul_of_nonneg_left (hG.minibatch_variance_bound hb hx hy)
    (show 0 ≤ κ by linarith)
  nlinarith

theorem AveragedSmooth.weighted_persistent_increment_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Fin n → E → JointSpace dx dy} {s : Set E} {L κ : ℝ}
    (hG : AveragedSmooth G s L) (hκ : 1 ≤ κ) (hb : 0 < b)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) (old : JointSpace dx dy) :
    (∫ I, weightedErrorSq κ
      (old + minibatchMean (fun i ↦ G i x - G i y) I - averageMap G x)
      ∂minibatchLaw n b) ≤ weightedErrorSq κ (old - averageMap G y) +
        κ * (L ^ 2 / b) * ‖x - y‖ ^ 2 := by
  simp_rw [persistent_update_error_identity]
  rw [weighted_minibatch_bias_second_moment hb]
  have hdiff : averageMap G x - averageMap G y =
      (n : ℝ)⁻¹ • ∑ i, (G i x - G i y) := by
    simp [averageMap, Finset.sum_sub_distrib, smul_sub]
  have hv := hG.weighted_error_variance_bound hκ hb hx hy
  rw [hdiff] at hv
  linarith

end

end NCConcave16991
