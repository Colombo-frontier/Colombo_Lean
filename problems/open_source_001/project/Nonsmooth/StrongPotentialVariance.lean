import Nonsmooth.RealDensityLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem strong_potential_law_probability_and_memLp (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) :
    IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-U x))) ∧
      MemLp (fun x : ℝ => x) 2 (realDensityLaw (fun x => Real.exp (-U x))) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hwc : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hw : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  have hw0 : ∀ x, 0 ≤ Real.exp (-U x) := fun x => (Real.exp_pos _).le
  have hZ : 0 < ∫ x, Real.exp (-U x) := integral_exp_pos hw
  exact ⟨realDensityLaw_probability _ hw hw0 hZ,
    realDensityLaw_memLp_two _ hwc.measurable hw hw0 hZ
      (strong_potential_polynomial_integrable U s hU hs hρ hd hmono 2)⟩

/-- On the entire real line, a continuously differentiable strongly convex potential
defines an actual probability density with variance at most 1/ρ. Integrability,
normalization, and the passage from finite intervals are all proved internally. -/
theorem strong_potential_law_variance (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) :
    variance (fun x : ℝ => x) (realDensityLaw (fun x => Real.exp (-U x))) ≤ ρ⁻¹ := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hwc : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hw : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  have hw0 : ∀ x, 0 ≤ Real.exp (-U x) := fun x => (Real.exp_pos _).le
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
    apply realDensityLaw_interval_positive (hwidth n).le _ hwc hw hw0
    exact intervalIntegral.integral_pos (hwidth n) hwc.continuousOn (fun x _ => hw0 x)
      ⟨-((n : ℝ) + 1), ⟨le_rfl, (hwidth n).le⟩, Real.exp_pos _⟩
  apply variance_le_of_conditioning_exhaustion _ hprob.2 A hA hAm hcover hpos
  intro n
  change variance (fun x : ℝ => x)
    ((realDensityLaw (fun x => Real.exp (-U x)))[|Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)]) ≤ _
  rw [realDensityLaw_condition_interval _ hw hw0]
  exact convex_potential_interval_law_variance (hwidth n) hρ U s hU hs
    (fun x _ => hd x) (hmono.monotoneOn _)

end
end Nonsmooth
