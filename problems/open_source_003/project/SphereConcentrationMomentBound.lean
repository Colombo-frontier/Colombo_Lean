import SphereConcentrationOdd
import SphereConcentrationMoments

/-!
The actual odd-sphere 3/2-moment theorem obtained by normalization and the
proved layer-cake integral. The function, probability law and integrability
are explicit; a target moment inequality is never an input premise.
-/

open Set MeasureTheory ProbabilityTheory Real Metric
open Task006.HaarRebalancing
open scoped ENNReal NNReal

namespace Task006.SphereConcentration
noncomputable section

/-- Genuine 3/2-moment control for an odd Lipschitz scalar sphere function.
The absolute pointwise bound supplies integrability of the actual function. -/
theorem sphere_odd_threeHalves_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v μ) (hvmeas : Measurable v)
    (hd : 0 < d) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a)
    {G : ℝ≥0} (hlip : LipschitzOnWith G a (sphere (0 : _) 1))
    (hodd : ∀ q, a (-q) = -a q)
    (hbound : ∀ q, ‖q‖ = 1 → |a q| ≤ G) :
    Integrable (fun ω => |a (v ω)| ^ (3 / 2 : ℝ)) μ ∧
      (∫ ω, |a (v ω)| ^ (3 / 2 : ℝ) ∂μ) ≤
        thirdHalfMomentConstant * ((G : ℝ) / Real.sqrt (d : ℝ)) ^ (3 / 2 : ℝ) := by
  have haeval : Measurable (fun ω => a (v ω)) := ha.comp hvmeas
  have haMoment : Measurable (fun ω => |a (v ω)| ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).measurable.comp haeval.abs
  have hintegrable : Integrable (fun ω => |a (v ω)| ^ (3 / 2 : ℝ)) μ := by
    apply Integrable.of_bound haMoment.aestronglyMeasurable ((G : ℝ) ^ (3 / 2 : ℝ))
    filter_upwards [hv.unit_ae] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hbound _ hω) (by norm_num)
  refine ⟨hintegrable, ?_⟩
  by_cases hGzero : G = 0
  · have hz : ∀ᵐ ω ∂μ, a (v ω) = 0 := by
      filter_upwards [hv.unit_ae] with ω hω
      have h := hbound (v ω) hω
      simpa only [hGzero, NNReal.coe_zero, abs_nonpos_iff] using h
    have hpowzero : (fun ω => |a (v ω)| ^ (3 / 2 : ℝ)) =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [hz] with ω hω
      simp [hω]
    rw [integral_congr_ae hpowzero]
    simp [hGzero]
  have hG : 0 < G := pos_iff_ne_zero.mpr hGzero
  have hGreal : 0 < (G : ℝ) := hG
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdreal
  let c : ℝ := (G : ℝ) / Real.sqrt (d : ℝ)
  have hc : 0 < c := div_pos hGreal hsqrt
  let Y : Ω → ℝ := fun ω => a (v ω) / c
  have hY : Measurable Y := haeval.div_const _
  have hYbound : ∀ᵐ ω ∂μ, |Y ω| ≤ (G : ℝ) / c := by
    filter_upwards [hv.unit_ae] with ω hω
    change |a (v ω) / c| ≤ (G : ℝ) / c
    rw [abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right (hbound _ hω) hc.le
  obtain ⟨hlo, hhi⟩ := odd_uniform_has_zero_median hv ha hodd
  have hYtail (t : ℝ) (ht : 0 < t) : μ.real {ω | t ≤ |Y ω|} ≤
      Real.exp 128 * Real.exp (-(1 / 128 : ℝ) * t ^ 2) := by
    have hset : {ω | t ≤ |Y ω|} = {ω | c * t ≤ |a (v ω)|} := by
      ext ω
      change t ≤ |a (v ω) / c| ↔ c * t ≤ |a (v ω)|
      rw [abs_div, abs_of_pos hc, le_div_iff₀ hc, mul_comm t c]
    rw [hset]
    have htail := sphere_lipschitz_median_concentration_pos hv hd ha hG hlip hlo hhi (mul_pos hc ht)
    have halg : -(d : ℝ) * (c * t) ^ 2 / (128 * (G : ℝ) ^ 2) =
        -(1 / 128 : ℝ) * t ^ 2 := by
      dsimp [c]
      rw [mul_pow, div_pow, Real.sq_sqrt hdreal.le]
      field_simp [hdreal.ne', hGreal.ne'] <;> ring
    rwa [halg] at htail
  have hYmoment := thirdHalf_moment_of_normalized_tail hY hYbound hYtail
  have hpoint (ω : Ω) : |a (v ω)| ^ (3 / 2 : ℝ) =
      c ^ (3 / 2 : ℝ) * |Y ω| ^ (3 / 2 : ℝ) := by
    have hid : a (v ω) = c * Y ω := by dsimp [Y]; field_simp [hc.ne']
    conv_lhs => rw [hid]
    rw [abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg _)]
  calc
    (∫ ω, |a (v ω)| ^ (3 / 2 : ℝ) ∂μ) =
        ∫ ω, c ^ (3 / 2 : ℝ) * |Y ω| ^ (3 / 2 : ℝ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = c ^ (3 / 2 : ℝ) * ∫ ω, |Y ω| ^ (3 / 2 : ℝ) ∂μ := integral_const_mul _ _
    _ ≤ c ^ (3 / 2 : ℝ) * thirdHalfMomentConstant :=
      mul_le_mul_of_nonneg_left hYmoment (Real.rpow_nonneg hc.le _)
    _ = thirdHalfMomentConstant * ((G : ℝ) / Real.sqrt (d : ℝ)) ^ (3 / 2 : ℝ) := by
      dsimp [c]
      ring

/-- The dimension/scale form appearing in U5, with the same actual moment. -/
theorem sphere_odd_threeHalves_moment_dimension {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v μ) (hvmeas : Measurable v)
    (hd : 0 < d) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a)
    {G : ℝ≥0} (hlip : LipschitzOnWith G a (sphere (0 : _) 1))
    (hodd : ∀ q, a (-q) = -a q)
    (hbound : ∀ q, ‖q‖ = 1 → |a q| ≤ G) :
    (∫ ω, |a (v ω)| ^ (3 / 2 : ℝ) ∂μ) ≤
      thirdHalfMomentConstant * (G : ℝ) ^ (3 / 2 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ) := by
  have hdreal : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsqrt : (Real.sqrt (d : ℝ)) ^ (3 / 2 : ℝ) = (d : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hdreal]
    norm_num
  have h := (sphere_odd_threeHalves_moment hv hvmeas hd ha hlip hodd hbound).2
  rw [Real.div_rpow G.coe_nonneg (Real.sqrt_nonneg _), hsqrt] at h
  simpa only [mul_div_assoc] using h

end
end Task006.SphereConcentration
