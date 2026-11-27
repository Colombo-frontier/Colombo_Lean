import Nonsmooth.IntervalCovarianceBrascampLieb
import Nonsmooth.CovarianceExhaustion
import Nonsmooth.StrongPotentialVariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- The covariance-strengthened Brascamp--Lieb estimate on the complete line.
Positive reserved curvature supplies normalization and the coordinate L2 bound. -/
theorem full_line_covariance_brascamp_lieb {ρ : ℝ} (hρ : 0 < ρ)
    (U s v f f' : ℝ → ℝ) (hs : Continuous s) (hv : Continuous v)
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt U (s x) x)
    (hsd : ∀ x, HasDerivAt s (v x) x) (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hvρ : ∀ x, 0 < v x - ρ)
    (hf2 : MemLp f 2 (realDensityLaw (fun x => Real.exp (-U x))))
    (hgrad : Integrable (fun x => (f' x) ^ 2 / (v x - ρ))
      (realDensityLaw (fun x => Real.exp (-U x)))) :
    let Q := realDensityLaw (fun x => Real.exp (-U x))
    variance f Q + ρ * (∫ x, x * (f x - ∫ y, f y ∂Q) ∂Q) ^ 2 ≤
      ∫ x, (f' x) ^ 2 / (v x - ρ) ∂Q := by
  dsimp only
  have hmono : Monotone (fun x => s x - ρ * x) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun x => (hsd x).sub ((hasDerivAt_id x).const_mul ρ))
    intro x
    simpa only [mul_one, Pi.zero_apply] using (hvρ x).le
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hw : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hw0 (x : ℝ) : 0 ≤ Real.exp (-U x) := (Real.exp_pos _).le
  have hi : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  have hprob := strong_potential_law_probability_and_memLp U s hs hρ hd hmono
  letI := hprob.1
  let A : ℕ → Set ℝ := fun n => Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hwidth (n : ℕ) : -((n : ℝ) + 1) < (n : ℝ) + 1 := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hA : ∀ n, MeasurableSet (A n) := fun _ => measurableSet_Icc
  have hAm : Monotone A := by
    intro m n hmn x hx
    have hcast : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    change -((m : ℝ) + 1) ≤ x ∧ x ≤ (m : ℝ) + 1 at hx
    change -((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 1
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcover : (⋃ n, A n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change -((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 1
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hpos (n : ℕ) : (realDensityLaw (fun x => Real.exp (-U x))) (A n) ≠ 0 := by
    apply realDensityLaw_interval_positive (hwidth n).le _ hw hi hw0
    exact intervalIntegral.integral_pos (hwidth n) hw.continuousOn (fun x _ => hw0 x)
      ⟨-((n : ℝ) + 1), ⟨le_rfl, (hwidth n).le⟩, Real.exp_pos _⟩
  have hcov := centered_product_conditioning_exhaustion_tendsto _ f (fun x : ℝ => x)
    hf2 hprob.2 A hA hAm hcover hpos
  have hvar := variance_conditioning_exhaustion_tendsto _ hf2 A hA hAm hcover hpos
  apply le_of_tendsto_of_tendsto (hvar.add ((hcov.pow 2).const_mul ρ))
    (integral_conditioning_exhaustion_tendsto _ hgrad A hA hAm hcover)
  apply Eventually.of_forall
  intro n
  dsimp only [A]
  rw [realDensityLaw_condition_interval _ hi hw0]
  exact interval_covariance_brascamp_lieb (hwidth n) hρ.le U s v f f' hs hv hf hf' hd
    (fun x _ => hsd x) (fun x _ => hfd x) (fun x _ => hvρ x)

end
end Nonsmooth
