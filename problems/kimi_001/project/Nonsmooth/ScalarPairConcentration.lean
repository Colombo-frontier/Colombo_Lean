import Nonsmooth.ScalarMGFTails

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem exp_add_le_half_double (a b : ℝ) :
    Real.exp (a + b) ≤ (Real.exp (2 * a) + Real.exp (2 * b)) / 2 := by
  have ha : Real.exp (2 * a) = (Real.exp a) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb : Real.exp (2 * b) = (Real.exp b) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [Real.exp_add, ha, hb]
  nlinarith [sq_nonneg (Real.exp a - Real.exp b)]

/-- Two possibly dependent scalar variables with unit MGF bounds give a
dimension-free bound for any linear combination. -/
theorem scalar_pair_unit_mgf {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F G : α → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFc : ∀ r : ℝ, Integrable (fun x => Real.exp (r * F x)) μ ∧
      (∫ x, Real.exp (r * F x) ∂μ) ≤ Real.exp (r ^ 2 / 2))
    (hGc : ∀ r : ℝ, Integrable (fun x => Real.exp (r * G x)) μ ∧
      (∫ x, Real.exp (r * G x) ∂μ) ≤ Real.exp (r ^ 2 / 2)) (a b : ℝ) :
    Integrable (fun x => Real.exp (a * F x + b * G x)) μ ∧
      (∫ x, Real.exp (a * F x + b * G x) ∂μ) ≤ Real.exp (2 * (a ^ 2 + b ^ 2)) := by
  have hs : Integrable (fun x => (Real.exp (2 * a * F x) + Real.exp (2 * b * G x)) / 2) μ :=
    ((hFc (2 * a)).1.add (hGc (2 * b)).1).div_const 2
  have hbnd (x : α) : Real.exp (a * F x + b * G x) ≤
      (Real.exp (2 * a * F x) + Real.exp (2 * b * G x)) / 2 := by
    simpa only [mul_assoc] using exp_add_le_half_double (a * F x) (b * G x)
  have hm : Measurable (fun x => Real.exp (a * F x + b * G x)) :=
    Real.continuous_exp.measurable.comp ((hF.const_mul a).add (hG.const_mul b))
  have hi : Integrable (fun x => Real.exp (a * F x + b * G x)) μ :=
    hs.mono' hm.aestronglyMeasurable (Eventually.of_forall (fun x => by
      simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hbnd x))
  refine ⟨hi, (integral_mono hi hs hbnd).trans ?_⟩
  rw [integral_div, integral_add (hFc (2 * a)).1 (hGc (2 * b)).1]
  have ha := (hFc (2 * a)).2.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg b] :
    (2 * a) ^ 2 / 2 ≤ 2 * (a ^ 2 + b ^ 2)))
  have hb := (hGc (2 * b)).2.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg a] :
    (2 * b) ^ 2 / 2 ≤ 2 * (a ^ 2 + b ^ 2)))
  linarith

end
end Nonsmooth
