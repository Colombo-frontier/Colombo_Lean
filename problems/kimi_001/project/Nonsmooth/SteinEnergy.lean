import Nonsmooth.DerivativeEnergy

open MeasureTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- The weighted one-dimensional Stein energy identity, with both endpoint
terms zero. No probability or differential-equation solution is postulated. -/
theorem weighted_stein_energy {a b : ℝ} (hab : a ≤ b)
    (w s v f g q : ℝ → ℝ)
    (hw : Continuous w) (hv : Continuous v)
    (hf : Continuous f) (hg : Continuous g) (hq : Continuous q)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hwd : ∀ x ∈ Icc a b, HasDerivAt w (-s x * w x) x)
    (hsd : ∀ x ∈ Icc a b, HasDerivAt s (v x) x)
    (hgd : ∀ x ∈ Icc a b, HasDerivAt g (q x) x)
    (hrel : ∀ x ∈ Icc a b, q x = f x + s x * g x)
    (ha : g a = 0) (hb : g b = 0) :
    (∫ x in a..b, v x * (g x) ^ 2 * w x) ≤ ∫ x in a..b, (f x) ^ 2 * w x := by
  have hder (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun t => s t * (g t) ^ 2 * w t)
        (v x * (g x) ^ 2 * w x + (q x) ^ 2 * w x - (f x) ^ 2 * w x) x := by
    convert! ((hsd x hx).mul ((hgd x hx).pow 2)).mul (hwd x hx) using 1
    simp only [Pi.pow_apply, Pi.mul_apply]
    rw [hrel x hx]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by simpa only [uIcc_of_le hab] using hx))
    ((((hv.mul (hg.pow 2)).mul hw).add ((hq.pow 2).mul hw) |>.sub ((hf.pow 2).mul hw)).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (f := fun x => v x * (g x) ^ 2 * w x + (q x) ^ 2 * w x) (g := fun x => (f x) ^ 2 * w x)
    ((((hv.mul (hg.pow 2)).mul hw).add ((hq.pow 2).mul hw)).intervalIntegrable a b)
    (((hf.pow 2).mul hw).intervalIntegrable a b),
    intervalIntegral.integral_add (f := fun x => v x * (g x) ^ 2 * w x) (g := fun x => (q x) ^ 2 * w x) (((hv.mul (hg.pow 2)).mul hw).intervalIntegrable a b)
      (((hq.pow 2).mul hw).intervalIntegrable a b), ha, hb] at he
  have hn : 0 ≤ ∫ x in a..b, (q x) ^ 2 * w x :=
    intervalIntegral.integral_nonneg hab (fun x hx => mul_nonneg (sq_nonneg _) (hw0 x hx))
  nlinarith

/-- Brascamp--Lieb's weighted gradient bound from an explicit Stein solution.
The solution itself is constructed in the subsequent interval theorem. -/
theorem weighted_stein_gradient_bound {a b : ℝ} (hab : a ≤ b)
    (w s v f f' g q : ℝ → ℝ)
    (hw : Continuous w) (hv : Continuous v)
    (hf : Continuous f) (hf' : Continuous f') (hg : Continuous g) (hq : Continuous q)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hv0 : ∀ x ∈ Icc a b, 0 < v x)
    (hwd : ∀ x ∈ Icc a b, HasDerivAt w (-s x * w x) x)
    (hsd : ∀ x ∈ Icc a b, HasDerivAt s (v x) x)
    (hfd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hgd : ∀ x ∈ Icc a b, HasDerivAt g (q x) x)
    (hrel : ∀ x ∈ Icc a b, q x = f x + s x * g x)
    (ha : g a = 0) (hb : g b = 0) :
    (∫ x in a..b, (f x) ^ 2 * w x) ≤ ∫ x in a..b, (f' x) ^ 2 / v x * w x := by
  have henergy := weighted_stein_energy hab w s v f g q hw hv hf hg hq hw0 hwd hsd hgd hrel ha hb
  have hder (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun t => f t * g t * w t)
        (f' x * g x * w x + (f x) ^ 2 * w x) x := by
    convert! ((hfd x hx).mul (hgd x hx)).mul (hwd x hx) using 1
    simp only [Pi.pow_apply, Pi.mul_apply]
    rw [hrel x hx]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by simpa only [uIcc_of_le hab] using hx))
    ((((hf'.mul hg).mul hw).add ((hf.pow 2).mul hw)).intervalIntegrable a b)
  rw [intervalIntegral.integral_add (f := fun x => f' x * g x * w x) (g := fun x => (f x) ^ 2 * w x) (((hf'.mul hg).mul hw).intervalIntegrable a b)
    (((hf.pow 2).mul hw).intervalIntegrable a b), ha, hb] at he
  have hgrad : ContinuousOn (fun x => (f' x) ^ 2 / v x * w x) (Icc a b) :=
    ((hf'.pow 2).continuousOn.div hv.continuousOn (fun x hx => (hv0 x hx).ne')).mul hw.continuousOn
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      -2 * (f' x * g x * w x) ≤ (f' x) ^ 2 / v x * w x + v x * (g x) ^ 2 * w x := by
    have hbase : -2 * (f' x * g x) ≤ (f' x) ^ 2 / v x + v x * (g x) ^ 2 := by
      apply (mul_le_mul_iff_of_pos_left (hv0 x hx)).mp
      have hcancel : v x * ((f' x) ^ 2 / v x) = (f' x) ^ 2 :=
        mul_div_cancel₀ _ (hv0 x hx).ne'
      nlinarith [sq_nonneg (f' x + v x * g x)]
    nlinarith [mul_le_mul_of_nonneg_right hbase (hw0 x hx)]
  have hle := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_const.mul ((hf'.mul hg).mul hw)).intervalIntegrable a b)
    ((hgrad.add (((hv.mul (hg.pow 2)).mul hw).continuousOn)).intervalIntegrable_of_Icc hab) hpoint
  change (∫ x in a..b, -2 * (f' x * g x * w x)) ≤
    ∫ x in a..b, (f' x) ^ 2 / v x * w x + v x * (g x) ^ 2 * w x at hle
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (f := fun x => (f' x) ^ 2 / v x * w x) (g := fun x => v x * (g x) ^ 2 * w x) (hgrad.intervalIntegrable_of_Icc hab)
      (((hv.mul (hg.pow 2)).mul hw).intervalIntegrable a b)] at hle
  nlinarith

end
end Nonsmooth
