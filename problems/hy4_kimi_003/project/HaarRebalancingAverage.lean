import SphereConcentrationMomentBound

/-!
Actual Fubini/averaging step in spherical rebalancing (U5). The sample-wise
odd-Lipschitz moment estimate is the proved spherical concentration consequence,
and the outer expectation uses only the actual third-halves moment of G.
-/

open Set MeasureTheory ProbabilityTheory Real Metric
open Task006.SphereConcentration
open scoped ENNReal NNReal

namespace Task006.HaarRebalancing
noncomputable section

/-- Average the actual pathwise spherical moment over the sample law.
Integrability on the full product is proved by domination by G^(3/2). -/
theorem average_odd_threeHalves_moment {d : ℕ} {Sample Ω : Type*}
    [MeasurableSpace Sample] [MeasurableSpace Ω]
    {σ : Measure Sample} {ν : Measure Ω} [IsProbabilityMeasure σ] [IsProbabilityMeasure ν]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v ν) (hvmeas : Measurable v)
    (hd : 0 < d) (D : Sample → EuclideanSpace ℝ (Fin d) → ℝ) (G : Sample → ℝ≥0)
    (hD : ∀ z, Measurable (D z))
    (hjoint : Measurable (fun p : Sample × Ω => D p.1 (v p.2)))
    (hlip : ∀ z, LipschitzOnWith (G z) (D z) (sphere (0 : _) 1))
    (hodd : ∀ z q, D z (-q) = -D z q)
    (hbound : ∀ z q, ‖q‖ = 1 → |D z q| ≤ G z)
    (hmG : Integrable (fun z => (G z : ℝ) ^ (3 / 2 : ℝ)) σ)
    {L : ℝ} (hbudget : (∫ z, (G z : ℝ) ^ (3 / 2 : ℝ) ∂σ) ≤ L ^ (3 / 2 : ℝ)) :
    Integrable (fun p : Sample × Ω => |D p.1 (v p.2)| ^ (3 / 2 : ℝ)) (σ.prod ν) ∧
      (∫ ω, ∫ z, |D z (v ω)| ^ (3 / 2 : ℝ) ∂σ ∂ν) ≤
        thirdHalfMomentConstant * L ^ (3 / 2 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ) := by
  have hmeas : Measurable (fun p : Sample × Ω => |D p.1 (v p.2)| ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).measurable.comp hjoint.abs
  have hunitprod : ∀ᵐ p : Sample × Ω ∂σ.prod ν, ‖v p.2‖ = 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := σ) (ν := ν)).ae hv.unit_ae
  have hproduct : Integrable (fun p : Sample × Ω => |D p.1 (v p.2)| ^ (3 / 2 : ℝ)) (σ.prod ν) := by
    apply (hmG.comp_fst ν).mono' hmeas.aestronglyMeasurable
    filter_upwards [hunitprod] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hbound _ _ hp) (by norm_num)
  refine ⟨hproduct, ?_⟩
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hdreal _
  have hC : 0 ≤ thirdHalfMomentConstant := le_trans (by norm_num) thirdHalfMomentConstant_ge_one
  have hupper : Integrable (fun z => thirdHalfMomentConstant *
      (G z : ℝ) ^ (3 / 2 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ)) σ :=
    (hmG.const_mul thirdHalfMomentConstant).div_const _
  calc
    (∫ ω, ∫ z, |D z (v ω)| ^ (3 / 2 : ℝ) ∂σ ∂ν) =
        ∫ z, ∫ ω, |D z (v ω)| ^ (3 / 2 : ℝ) ∂ν ∂σ :=
      (integral_integral_swap hproduct).symm
    _ ≤ ∫ z, thirdHalfMomentConstant * (G z : ℝ) ^ (3 / 2 : ℝ) /
        (d : ℝ) ^ (3 / 4 : ℝ) ∂σ := by
      apply integral_mono hproduct.integral_prod_left hupper
      intro z
      exact sphere_odd_threeHalves_moment_dimension hv hvmeas hd (hD z) (hlip z)
        (hodd z) (hbound z)
    _ = (thirdHalfMomentConstant / (d : ℝ) ^ (3 / 4 : ℝ)) *
        ∫ z, (G z : ℝ) ^ (3 / 2 : ℝ) ∂σ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ ≤ (thirdHalfMomentConstant / (d : ℝ) ^ (3 / 4 : ℝ)) * L ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hbudget (div_nonneg hC hden.le)
    _ = thirdHalfMomentConstant * L ^ (3 / 2 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ) := by ring

end
end Task006.HaarRebalancing
