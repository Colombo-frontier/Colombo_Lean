import Nonsmooth.SteinEnergy

open MeasureTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Retaining part of the curvature gives an additional nonnegative Stein
solution energy on the left side of Brascamp--Lieb. -/
theorem weighted_stein_gradient_with_penalty {a b ρ : ℝ} (hab : a ≤ b)
    (w s v f f' g q : ℝ → ℝ)
    (hw : Continuous w) (hv : Continuous v)
    (hf : Continuous f) (hf' : Continuous f') (hg : Continuous g) (hq : Continuous q)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hvρ : ∀ x ∈ Icc a b, 0 < v x - ρ)
    (hwd : ∀ x ∈ Icc a b, HasDerivAt w (-s x * w x) x)
    (hsd : ∀ x ∈ Icc a b, HasDerivAt s (v x) x)
    (hfd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hgd : ∀ x ∈ Icc a b, HasDerivAt g (q x) x)
    (hrel : ∀ x ∈ Icc a b, q x = f x + s x * g x)
    (ha : g a = 0) (hb : g b = 0) :
    (∫ x in a..b, (f x) ^ 2 * w x) + ρ * (∫ x in a..b, (g x) ^ 2 * w x) ≤
      ∫ x in a..b, (f' x) ^ 2 / (v x - ρ) * w x := by
  have henergy := weighted_stein_energy hab w s v f g q hw hv hf hg hq hw0 hwd hsd hgd hrel ha hb
  have hder (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun t => f t * g t * w t)
        (f' x * g x * w x + (f x) ^ 2 * w x) x := by
    convert! ((hfd x hx).mul (hgd x hx)).mul (hwd x hx) using 1
    rw [hrel x hx]
    simp only [Pi.mul_apply]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by simpa only [uIcc_of_le hab] using hx))
    ((((hf'.mul hg).mul hw).add ((hf.pow 2).mul hw)).intervalIntegrable a b)
  rw [intervalIntegral.integral_add (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => f' x * g x * w x) (g := fun x : ℝ => (f x) ^ 2 * w x)
    (((hf'.mul hg).mul hw).intervalIntegrable a b)
    (((hf.pow 2).mul hw).intervalIntegrable a b), ha, hb] at he
  have hgrad : ContinuousOn (fun x => (f' x) ^ 2 / (v x - ρ) * w x) (Icc a b) :=
    ((hf'.pow 2).continuousOn.div (hv.sub continuous_const).continuousOn
      (fun x hx => (hvρ x hx).ne')).mul hw.continuousOn
  have hvshift : Continuous (fun x => (v x - ρ) * (g x) ^ 2 * w x) :=
    ((hv.sub continuous_const).mul (hg.pow 2)).mul hw
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      -2 * (f' x * g x * w x) ≤ (f' x) ^ 2 / (v x - ρ) * w x +
        (v x - ρ) * (g x) ^ 2 * w x := by
    have hbase : -2 * (f' x * g x) ≤ (f' x) ^ 2 / (v x - ρ) + (v x - ρ) * (g x) ^ 2 := by
      apply (mul_le_mul_iff_of_pos_left (hvρ x hx)).mp
      have hcancel : (v x - ρ) * ((f' x) ^ 2 / (v x - ρ)) = (f' x) ^ 2 :=
        mul_div_cancel₀ _ (hvρ x hx).ne'
      nlinarith [sq_nonneg (f' x + (v x - ρ) * g x)]
    nlinarith [mul_le_mul_of_nonneg_right hbase (hw0 x hx)]
  have hle := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_const.mul ((hf'.mul hg).mul hw)).intervalIntegrable a b)
    ((hgrad.add hvshift.continuousOn).intervalIntegrable_of_Icc hab) hpoint
  simp only [Pi.mul_apply, Pi.add_apply] at hle
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hgrad.intervalIntegrable_of_Icc hab)
      (hvshift.intervalIntegrable a b)] at hle
  have hshift : (∫ x in a..b, (v x - ρ) * (g x) ^ 2 * w x) =
      (∫ x in a..b, v x * (g x) ^ 2 * w x) - ρ * (∫ x in a..b, (g x) ^ 2 * w x) := by
    have hfun : (fun x => (v x - ρ) * (g x) ^ 2 * w x) =
        fun x => v x * (g x) ^ 2 * w x - ρ * ((g x) ^ 2 * w x) := by funext x; ring
    rw [hfun, intervalIntegral.integral_sub (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => v x * (g x) ^ 2 * w x)
      (g := fun x : ℝ => ρ * ((g x) ^ 2 * w x))
      (((hv.mul (hg.pow 2)).mul hw).intervalIntegrable a b)
      ((continuous_const.mul ((hg.pow 2).mul hw)).intervalIntegrable a b),
      intervalIntegral.integral_const_mul]
  rw [hshift] at hle
  nlinarith

theorem weighted_stein_first_moment {a b : ℝ} (hab : a ≤ b)
    (w s f g q : ℝ → ℝ) (hw : Continuous w) (hf : Continuous f) (hg : Continuous g)
    (hwd : ∀ x ∈ Icc a b, HasDerivAt w (-s x * w x) x)
    (hgd : ∀ x ∈ Icc a b, HasDerivAt g (q x) x)
    (hrel : ∀ x ∈ Icc a b, q x = f x + s x * g x)
    (ha : g a = 0) (hb : g b = 0) :
    (∫ x in a..b, x * f x * w x) = -(∫ x in a..b, g x * w x) := by
  have hder (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun t => t * g t * w t) (g x * w x + x * f x * w x) x := by
    convert! ((hasDerivAt_id x).mul (hgd x hx)).mul (hwd x hx) using 1
    rw [hrel x hx]
    try simp only [id_eq, Pi.mul_apply]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by simpa only [uIcc_of_le hab] using hx))
    (((hg.mul hw).add ((continuous_id.mul hf).mul hw)).intervalIntegrable a b)
  rw [intervalIntegral.integral_add (f := fun x => g x * w x) (g := fun x => x * f x * w x)
    ((hg.mul hw).intervalIntegrable a b)
    (((continuous_id.mul hf).mul hw).intervalIntegrable a b), ha, hb] at he
  nlinarith

end
end Nonsmooth
