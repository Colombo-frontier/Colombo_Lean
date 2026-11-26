import NCBall.GaussianUpperTail

/-! # A finite maximum controlled by positive exponential moments -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace NCBall

def nonnegativeMaximum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (s.sup (fun i => (f i).toNNReal) : ℝ≥0)

theorem nonnegativeMaximum_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    0 ≤ nonnegativeMaximum s f := NNReal.coe_nonneg _

theorem le_nonnegativeMaximum {ι : Type*} (s : Finset ι) (f : ι → ℝ) {i : ι} (hi : i ∈ s) :
    f i ≤ nonnegativeMaximum s f := by
  exact (Real.le_coe_toNNReal _).trans
    (NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j => (f j).toNNReal) hi))

theorem nonnegativeMaximum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i ∈ s, f i ≤ B) : nonnegativeMaximum s f ≤ B := by
  rw [← Real.coe_toNNReal B hB]
  exact NNReal.coe_le_coe.mpr (Finset.sup_le (fun i hi => Real.toNNReal_mono (h i hi)))

theorem nonnegativeMaximum_continuous {ι Ω : Type*} [TopologicalSpace Ω]
    (s : Finset ι) (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => nonnegativeMaximum s (fun i => f i x)) := by
  exact continuous_subtype_val.comp
    (Continuous.finset_sup_apply (fun i hi => continuous_real_toNNReal.comp (hf i hi)))

/-- A pointwise exponential envelope, valid also for an empty family. -/
theorem nonnegativeMaximum_exp_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) :
    nonnegativeMaximum s f ≤ K + a⁻¹ * Real.exp (-a * K) * ∑ i ∈ s, Real.exp (a * f i) := by
  have hsum : 0 ≤ ∑ i ∈ s, Real.exp (a * f i) :=
    Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  apply nonnegativeMaximum_le s f (by positivity)
  intro i hi
  have hex := Real.add_one_le_exp (a * (f i - K))
  have heq : Real.exp (a * (f i - K)) = Real.exp (-a * K) * Real.exp (a * f i) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hex
  have hs : Real.exp (a * f i) ≤ ∑ j ∈ s, Real.exp (a * f j) :=
    Finset.single_le_sum (fun j _ => (Real.exp_pos (a * f j)).le) hi
  have hb : a * (f i - K) ≤ Real.exp (-a * K) * ∑ j ∈ s, Real.exp (a * f j) := by
    nlinarith [mul_le_mul_of_nonneg_left hs (Real.exp_pos (-a * K)).le]
  have hdiv : f i - K ≤ (Real.exp (-a * K) * ∑ j ∈ s, Real.exp (a * f j)) / a :=
    (le_div_iff₀ ha).mpr (by nlinarith only [hb])
  nlinarith [show Real.exp (-a * K) * (∑ j ∈ s, Real.exp (a * f j)) / a =
    a⁻¹ * Real.exp (-a * K) * ∑ j ∈ s, Real.exp (a * f j) by ring]

theorem nonnegativeMaximum_integral_bound {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (f : ι → Ω → ℝ)
    {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (hm : AEStronglyMeasurable (fun x => nonnegativeMaximum s (fun i => f i x)) μ)
    (hf : ∀ i ∈ s, Integrable (fun x => Real.exp (a * f i x)) μ) :
    Integrable (fun x => nonnegativeMaximum s (fun i => f i x)) μ ∧
      (∫ x, nonnegativeMaximum s (fun i => f i x) ∂μ) ≤
        K + a⁻¹ * Real.exp (-a * K) * ∑ i ∈ s, ∫ x, Real.exp (a * f i x) ∂μ := by
  have hs := integrable_finset_sum s hf
  have henv : Integrable (fun x => K + a⁻¹ * Real.exp (-a * K) *
      ∑ i ∈ s, Real.exp (a * f i x)) μ :=
    (integrable_const K).add (hs.const_mul _)
  have hi : Integrable (fun x => nonnegativeMaximum s (fun i => f i x)) μ := by
    apply henv.mono' hm
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (nonnegativeMaximum_nonneg _ _)]
    exact nonnegativeMaximum_exp_bound s (fun i => f i x) ha hK
  refine ⟨hi, ?_⟩
  have hb := integral_mono hi henv (fun x => nonnegativeMaximum_exp_bound s (fun i => f i x) ha hK)
  simpa only [integral_add (integrable_const K) (hs.const_mul _), integral_const,
    measureReal_univ_eq_one, smul_eq_mul, one_mul, integral_const_mul, integral_finset_sum _ hf] using hb

end NCBall
