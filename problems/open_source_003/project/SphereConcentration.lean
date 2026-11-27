import Mathlib

/-!
Actual scalar central secants and the L^(3/2) reverse-Minkowski step in the
spherical rebalancing argument. The definitions are function-level objects,
not scalar variables named after desired conclusions. General spherical
concentration is not postulated here.
-/

open MeasureTheory
open scoped ENNReal

namespace Task006.SphereConcentration

noncomputable section

/-- The same-sample, symmetric two-point secant used in the manuscript. -/
def centralSecant {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E → ℝ) (x : E) (δ : ℝ) (q : E) : ℝ :=
  (F (x + δ • q) - F (x - δ • q)) / (2 * δ)

/-- Oddness follows from the actual secant formula, with no smoothness premise. -/
theorem centralSecant_odd {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E → ℝ) (x : E) (δ : ℝ) (q : E) :
    centralSecant F x δ (-q) = -centralSecant F x δ q := by
  simp only [centralSecant, smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-- The secant's actual pathwise Lipschitz bound, using only legal endpoints. -/
theorem centralSecant_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {S : Set E} {G δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ a ∈ S, ∀ b ∈ S, |F a - F b| ≤ G * ‖a - b‖)
    (x q q' : E)
    (hp : x + δ • q ∈ S) (hm : x - δ • q ∈ S)
    (hp' : x + δ • q' ∈ S) (hm' : x - δ • q' ∈ S) :
    |centralSecant F x δ q - centralSecant F x δ q'| ≤ G * ‖q - q'‖ := by
  have hden : 0 < 2 * δ := by positivity
  have hvp : (x + δ • q) - (x + δ • q') = δ • (q - q') := by module
  have hvm : (x - δ • q) - (x - δ • q') = (-δ) • (q - q') := by module
  have hnum :
      (F (x + δ • q) - F (x - δ • q)) -
        (F (x + δ • q') - F (x - δ • q')) =
      (F (x + δ • q) - F (x + δ • q')) -
        (F (x - δ • q) - F (x - δ • q')) := by ring
  rw [centralSecant, centralSecant, ← sub_div, abs_div,
    abs_of_pos hden, hnum]
  apply (div_le_iff₀ hden).2
  have hpbound := hF _ hp _ hp'
  have hmbound := hF _ hm _ hm'
  rw [hvp, norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at hpbound
  rw [hvm, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδ] at hmbound
  have htri := abs_sub (F (x + δ • q) - F (x + δ • q'))
    (F (x - δ • q) - F (x - δ • q'))
  nlinarith

/-- A legal central secant along a unit-ball direction is bounded by G. -/
theorem abs_centralSecant_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {S : Set E} {G δ : ℝ} (hG : 0 ≤ G) (hδ : 0 < δ)
    (hF : ∀ a ∈ S, ∀ b ∈ S, |F a - F b| ≤ G * ‖a - b‖)
    (x q : E) (hq : ‖q‖ ≤ 1)
    (hp : x + δ • q ∈ S) (hm : x - δ • q ∈ S) :
    |centralSecant F x δ q| ≤ G := by
  have hden : 0 < 2 * δ := by positivity
  have hv : (x + δ • q) - (x - δ • q) = (2 * δ) • q := by module
  rw [centralSecant, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  have hf := hF _ hp _ hm
  rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hden] at hf
  have hprod := mul_le_mul_of_nonneg_left hq (mul_nonneg hG hden.le)
  nlinarith only [hf, hprod]

/-- The reverse triangle inequality for actual Lp seminorms, derived from
Minkowski. Both random functions are explicitly in Lp. -/
theorem abs_lpNorm_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : Ω → ℝ} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    |lpNorm f p μ - lpNorm g p μ| ≤ lpNorm (f - g) p μ := by
  apply abs_le.mpr
  constructor
  · have h := lpNorm_le_lpNorm_add_lpNorm_sub' hf hp (f := g)
    rw [lpNorm_sub_comm g f] at h
    linarith
  · have h := lpNorm_le_lpNorm_add_lpNorm_sub' hg hp (f := f)
    linarith

/-- The root moment of a random family is Lipschitz when each sample is
G-Lipschitz and G has a controlled Lp norm. This is the manuscript's h step,
not a premise asserting that h is Lipschitz. -/
theorem lpNorm_family_lipschitz {Ω X : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] {μ : Measure Ω} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (D : X → Ω → ℝ) (G : Ω → ℝ) (hG : MemLp G p μ)
    (hD : ∀ x, MemLp (D x) p μ)
    (hpath : ∀ x y ω, |D x ω - D y ω| ≤ G ω * dist x y) :
    ∀ x y, |lpNorm (D x) p μ - lpNorm (D y) p μ| ≤
      lpNorm G p μ * dist x y := by
  intro x y
  have hmono : lpNorm (D x - D y) p μ ≤
      lpNorm (fun ω => dist x y * G ω) p μ := by
    apply lpNorm_mono_real (hG.const_mul (dist x y))
    intro ω
    simpa only [Pi.sub_apply, Real.norm_eq_abs, mul_comm] using hpath x y ω
  have hscale : lpNorm (fun ω => dist x y * G ω) p μ =
      dist x y * lpNorm G p μ := by
    change lpNorm ((dist x y) • G) p μ = _
    simpa only [Real.nnnorm_of_nonneg dist_nonneg,
      NNReal.coe_mk] using (lpNorm_const_smul (dist x y) G μ (p := p))
  exact (abs_lpNorm_sub_le hp (hD x) (hD y)).trans (hmono.trans_eq (by
    rw [hscale, mul_comm]))

/-- The actual L^(3/2) root is the integral expression printed in the paper. -/
theorem lpNorm_threeHalves_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {D : Ω → ℝ} (hD : AEStronglyMeasurable D μ) :
    lpNorm D (3 / 2 : ℝ≥0∞) μ =
      (∫ ω, |D ω| ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := by
  have h := lpNorm_eq_integral_norm_rpow_toReal (p := (3 / 2 : ℝ≥0∞))
    (by norm_num) (by finiteness) hD
  norm_num [ENNReal.toReal_div, Real.norm_eq_abs] at h
  exact h

/-- A genuine three-halves moment budget bounds the Lp norm; the target
norm inequality is derived, rather than supplied as an assumption. -/
theorem lpNorm_threeHalves_le_of_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {G : Ω → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hG : AEStronglyMeasurable G μ)
    (hm : Integrable (fun ω => |G ω| ^ (3 / 2 : ℝ)) μ)
    (hbudget : (∫ ω, |G ω| ^ (3 / 2 : ℝ) ∂μ) ≤ L ^ (3 / 2 : ℝ)) :
    MemLp G (3 / 2 : ℝ≥0∞) μ ∧ lpNorm G (3 / 2 : ℝ≥0∞) μ ≤ L := by
  have hmem : MemLp G (3 / 2 : ℝ≥0∞) μ := by
    apply (integrable_norm_rpow_iff hG (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (by finiteness)).1
    simpa [ENNReal.toReal_div, Real.norm_eq_abs] using hm
  refine ⟨hmem, ?_⟩
  rw [lpNorm_threeHalves_eq hG]
  calc
    (∫ ω, |G ω| ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) ≤
        (L ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _))
        hbudget (by norm_num)
    _ = L := by rw [← Real.rpow_mul hL]; norm_num

/-- The manuscript's actual moment-root h is L-Lipschitz. Measurability,
pointwise domination, the pathwise Lipschitz estimate and G's actual moment
budget suffice; no Lipschitz property of h is assumed. -/
theorem threeHalves_rootMoment_lipschitz {Ω X : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] {μ : Measure Ω} (D : X → Ω → ℝ)
    (G : Ω → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hG : AEStronglyMeasurable G μ)
    (hm : Integrable (fun ω => |G ω| ^ (3 / 2 : ℝ)) μ)
    (hbudget : (∫ ω, |G ω| ^ (3 / 2 : ℝ) ∂μ) ≤ L ^ (3 / 2 : ℝ))
    (hD : ∀ x, AEStronglyMeasurable (D x) μ)
    (hdom : ∀ x ω, |D x ω| ≤ G ω)
    (hpath : ∀ x y ω, |D x ω - D y ω| ≤ G ω * dist x y) :
    ∀ x y,
      |(∫ ω, |D x ω| ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) -
        (∫ ω, |D y ω| ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ)| ≤ L * dist x y := by
  obtain ⟨hGmem, hGnorm⟩ := lpNorm_threeHalves_le_of_moment hL hG hm hbudget
  have hDmem : ∀ x, MemLp (D x) (3 / 2 : ℝ≥0∞) μ := by
    intro x
    apply hGmem.mono' (hD x)
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs] using hdom x ω
  intro x y
  rw [← lpNorm_threeHalves_eq (hD x), ← lpNorm_threeHalves_eq (hD y)]
  exact (lpNorm_family_lipschitz (by
      apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
      norm_num : (1 : ℝ≥0∞) ≤ 3 / 2)
    D G hGmem hDmem hpath x y).trans
      (mul_le_mul_of_nonneg_right hGnorm dist_nonneg)

end
end Task006.SphereConcentration
