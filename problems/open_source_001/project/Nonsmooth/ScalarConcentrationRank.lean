import Nonsmooth.ScalarMGFTails
import Nonsmooth.AtomlessCDFEntropy
import Nonsmooth.RankQuantileMoment

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem scalar_unit_mgf_rank_point (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * (x - m))) μ)
    (hb : ∀ r : ℝ, (∫ x, Real.exp (r * (x - m)) ∂μ) ≤ Real.exp (r ^ 2 / 2))
    (y : ℝ) (hp : 0 < cdf μ y ∧ cdf μ y < 1) :
    (y - m) ^ 2 ≤ 2 * rankQuantileLog (cdf μ y) := by
  let p := cdf μ y
  have hmin : 0 < min p (1 - p) := lt_min hp.1 (by dsimp only [p]; linarith [hp.2])
  have htail : min p (1 - p) ≤ Real.exp (-(y - m) ^ 2 / 2) := by
    rcases le_total m y with hy | hy
    · have ht := scalar_unit_mgf_upper_tail μ (fun x => x - m) hi hb (y - m) (sub_nonneg.mpr hy)
      have hr : μ.real (Ioi y) = 1 - p := by
        rw [← compl_Iic, measureReal_compl measurableSet_Iic, measureReal_univ_eq_one]
        change 1 - μ.real (Iic y) = 1 - cdf μ y
        rw [cdf_eq_real]
      have hs : μ.real (Ioi y) ≤ μ.real {x | y - m ≤ x - m} :=
        measureReal_mono (by intro x hx; change y < x at hx; change y - m ≤ x - m; linarith)
      exact (min_le_right p (1 - p)).trans ((hr.symm ▸ hs).trans ht)
    · have ht := scalar_unit_mgf_upper_tail μ (fun x => -(x - m))
        (fun r => by simpa only [mul_neg, neg_mul] using hi (-r))
        (fun r => by simpa only [mul_neg, neg_mul, neg_sq] using hb (-r))
        (m - y) (sub_nonneg.mpr hy)
      have hs : μ.real (Iic y) ≤ μ.real {x | m - y ≤ -(x - m)} :=
        measureReal_mono (by intro x hx; change x ≤ y at hx; change m - y ≤ -(x - m); linarith)
      have he : μ.real (Iic y) = p := (cdf_eq_real μ y).symm
      have hsq : (m - y) ^ 2 = (y - m) ^ 2 := by ring
      rw [hsq] at ht
      exact (min_le_left p (1 - p)).trans ((he ▸ hs).trans ht)
  have hlog := Real.log_le_log hmin htail
  rw [Real.log_exp] at hlog
  change (y - m) ^ 2 ≤ 2 * Real.log (1 / min p (1 - p))
  rw [one_div, Real.log_inv]
  linarith

theorem scalar_unit_mgf_rank_ae (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hatom : ∀ y : ℝ, μ {y} = 0)
    (hi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * (x - m))) μ)
    (hb : ∀ r : ℝ, (∫ x, Real.exp (r * (x - m)) ∂μ) ≤ Real.exp (r ^ 2 / 2)) :
    ∀ᵐ y ∂μ, (y - m) ^ 2 ≤ 2 * rankQuantileLog (cdf μ y) := by
  filter_upwards [atomless_cdf_interior_ae μ hatom] with y hy
  exact scalar_unit_mgf_rank_point μ m hi hb y hy

end
end Nonsmooth
