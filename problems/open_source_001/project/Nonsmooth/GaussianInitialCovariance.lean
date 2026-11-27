import Nonsmooth.TruncationMonotonicity
import Nonsmooth.RotationalCovariance
import Nonsmooth.GaussianPosteriorEnergy

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianAmbientRow_norm_second_le_one :
    (∫ a : E, ‖a‖ ^ 2 ∂gaussianAmbientRowLaw E) ≤ 1 := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  have hf : StronglyMeasurable (fun a : E => ‖a‖ ^ 2) := (continuous_norm.pow 2).stronglyMeasurable
  rw [gaussianAmbientRowLaw, gaussianSupportRowLaw_map, integral_map_of_stronglyMeasurable hm hf]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt hd.le]
  rw [integral_const_mul, ← div_eq_inv_mul, div_le_one hd]
  exact truncatedGaussian_norm_second_le

theorem gaussianAmbientRow_inner_second_le (u : E) :
    (∫ a : E, ⟪u, a⟫_ℝ ^ 2 ∂gaussianAmbientRowLaw E) ≤
      ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  rw [rotational_second_moment (gaussianAmbientRowLaw E) gaussianAmbientRowLaw_isometry
    (gaussianAmbientRowLaw_memLp (E := E))]
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (gaussianAmbientRow_norm_second_le_one (E := E)) (sq_nonneg ‖u‖)

theorem gaussianAmbientRows_inner_second_le {k : ℕ} [Nonempty (Fin k)] (u : E) :
    (∫ a : Fin k → E, ⟪u, ∑ i, a i⟫_ℝ ^ 2 ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
      (k : ℝ) * ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
  have hm : Measurable (fun a : E => ⟪u, a⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  have hLp (i : Fin k) : MemLp (fun a : Fin k → E => ⟪u, a i⟫_ℝ) 2 Q :=
    (gaussianAmbientRows_coordinate_memLp i).const_inner u
  have hsum : MemLp (fun a : Fin k → E => ∑ i, ⟪u, a i⟫_ℝ) 2 Q :=
    memLp_finset_sum _ (fun i _ => hLp i)
  have hmean : (∫ a : Fin k → E, ∑ i, ⟪u, a i⟫_ℝ ∂Q) = 0 := by
    simp only [← inner_sum]
    rw [integral_inner gaussianAmbientRows_aggregate_integrable, gaussianAmbientRows_aggregate_mean_zero,
      inner_zero_right]
  have hind : iIndepFun (fun i (a : Fin k → E) => ⟪u, a i⟫_ℝ) Q :=
    (finite_product_independent (gaussianAmbientRowLaw E) k).comp (fun _ a => ⟪u, a⟫_ℝ) (fun _ => hm)
  have he := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hLp i)
    (fun i _ j _ hij => hind.indepFun hij)
  simp only [Finset.sum_fn] at he
  rw [variance_of_integral_eq_zero hsum.aestronglyMeasurable.aemeasurable hmean] at he
  have hb (i : Fin k) : variance (fun a : Fin k → E => ⟪u, a i⟫_ℝ) Q ≤
      ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
    have hf : StronglyMeasurable (fun a : E => ⟪u, a⟫_ℝ ^ 2) :=
      ((continuous_const.inner continuous_id).pow 2).stronglyMeasurable
    have hmap := integral_map_of_stronglyMeasurable (μ := Q) (measurable_pi_apply i) hf
    rw [(finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq] at hmap
    have hi : (∫ a : Fin k → E, ⟪u, a i⟫_ℝ ^ 2 ∂Q) ≤ ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ) :=
      hmap.symm.trans_le (gaussianAmbientRow_inner_second_le u)
    rw [variance_eq_sub (hLp i)]
    dsimp only [Pi.pow_apply]
    nlinarith [sq_nonneg (∫ a : Fin k → E, ⟪u, a i⟫_ℝ ∂Q)]
  have h := (le_of_eq he).trans (Finset.sum_le_sum (fun i _ => hb i))
  simpa only [← inner_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_div_assoc] using h

theorem gaussianSupportMean_initial_direction_residual {k : ℕ} [Nonempty (Fin k)]
    {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S] (p : Policy Ω S E) (ω : Ω)
    {u : E} (hu : ‖u‖ ≤ 1) :
    (∫ a : Fin k → E, ⟪(∑ i, a i) - gaussianSupportMean p ω 0 a, u⟫_ℝ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
      (k : ℝ) / (Module.finrank ℝ E : ℝ) := by
  simp only [gaussianSupportMean_initial, sub_zero, real_inner_comm u]
  apply (gaussianAmbientRows_inner_second_le u).trans
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  simpa using mul_le_mul_of_nonneg_left hu2 (Nat.cast_nonneg k)

end
end Nonsmooth
