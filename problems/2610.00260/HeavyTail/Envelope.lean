import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Curvature envelope for heavy-tailed optimization

The envelope is implemented by its actual maximizing radius, and its variational
characterization is proved below. No optimization or probability statement is
assumed by this file.
-/

namespace HeavyTail

noncomputable section

def envelopeRadius (μ D a : ℝ) : ℝ :=
  if μ = 0 then D else min D (a / μ)

def radialObjective (μ a r : ℝ) : ℝ := a * r - μ / 2 * r ^ 2

def envelope (μ D a : ℝ) : ℝ :=
  radialObjective μ a (envelopeRadius μ D a)

theorem envelopeRadius_nonneg {μ D a : ℝ} (hμ : 0 ≤ μ)
    (hD : 0 ≤ D) (ha : 0 ≤ a) : 0 ≤ envelopeRadius μ D a := by
  unfold envelopeRadius
  split_ifs with h
  · exact hD
  · exact le_min hD (div_nonneg ha hμ)

theorem envelopeRadius_le {μ D a : ℝ} : envelopeRadius μ D a ≤ D := by
  unfold envelopeRadius
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem radialObjective_le_at_critical {μ a r x : ℝ}
    (hμ : 0 ≤ μ) (hx : μ * x = a) :
    radialObjective μ a r ≤ radialObjective μ a x := by
  unfold radialObjective
  rw [← hx]
  nlinarith [mul_nonneg hμ (sq_nonneg (r - x))]

theorem radialObjective_le_at_endpoint {μ D a r : ℝ}
    (hμ : 0 ≤ μ) (hr : r ≤ D) (ha : μ * D ≤ a) :
    radialObjective μ a r ≤ radialObjective μ a D := by
  have h1 : 0 ≤ D - r := sub_nonneg.mpr hr
  have h2 : 0 ≤ a - μ / 2 * (D + r) := by
    nlinarith [mul_nonneg hμ h1]
  unfold radialObjective
  nlinarith [mul_nonneg h1 h2]

theorem radialObjective_le_envelope {μ D a r : ℝ}
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hr : r ≤ D) :
    radialObjective μ a r ≤ envelope μ D a := by
  by_cases hzero : μ = 0
  · simp only [envelope, envelopeRadius, if_pos hzero]
    exact radialObjective_le_at_endpoint hμ hr (by simpa [hzero] using ha)
  · have hpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hzero)
    unfold envelope envelopeRadius
    rw [if_neg hzero]
    by_cases hsmall : a / μ ≤ D
    · rw [min_eq_right hsmall]
      apply radialObjective_le_at_critical hμ
      exact mul_div_cancel₀ a hzero
    · rw [min_eq_left (le_of_not_ge hsmall)]
      apply radialObjective_le_at_endpoint hμ hr
      have h := (lt_div_iff₀ hpos).mp (lt_of_not_ge hsmall)
      nlinarith

theorem envelope_variational {μ D a : ℝ} (hμ : 0 ≤ μ)
    (hD : 0 ≤ D) (ha : 0 ≤ a) :
    ∃ r ∈ Set.Icc (0 : ℝ) D,
      envelope μ D a = radialObjective μ a r ∧
      ∀ t ∈ Set.Icc (0 : ℝ) D, radialObjective μ a t ≤ envelope μ D a := by
  refine ⟨envelopeRadius μ D a,
    ⟨envelopeRadius_nonneg hμ hD ha, envelopeRadius_le⟩, rfl, ?_⟩
  intro t ht
  exact radialObjective_le_envelope hμ ha ht.2

theorem envelope_zero_curvature (D a : ℝ) : envelope 0 D a = D * a := by
  simp [envelope, envelopeRadius, radialObjective, mul_comm]

theorem envelope_quadratic {μ D a : ℝ} (hμ : 0 < μ) (ha : a ≤ μ * D) :
    envelope μ D a = a ^ 2 / (2 * μ) := by
  unfold envelope envelopeRadius
  rw [if_neg (ne_of_gt hμ), min_eq_right ((div_le_iff₀ hμ).mpr (by nlinarith))]
  unfold radialObjective
  field_simp; ring

theorem envelope_linear {μ D a : ℝ} (hμ : 0 < μ) (ha : μ * D ≤ a) :
    envelope μ D a = D * a - μ * D ^ 2 / 2 := by
  unfold envelope envelopeRadius
  rw [if_neg (ne_of_gt hμ), min_eq_left ((le_div_iff₀ hμ).mpr (by nlinarith))]
  unfold radialObjective
  ring

theorem envelope_nonneg {μ D a : ℝ} (hμ : 0 ≤ μ) (hD : 0 ≤ D)
    (ha : 0 ≤ a) : 0 ≤ envelope μ D a := by
  simpa [radialObjective] using (radialObjective_le_envelope hμ ha hD)

theorem envelope_mono {μ D a b : ℝ} (hμ : 0 ≤ μ) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hab : a ≤ b) : envelope μ D a ≤ envelope μ D b := by
  have hb : 0 ≤ b := ha.trans hab
  have hrad := envelopeRadius_nonneg hμ hD ha
  calc
    envelope μ D a ≤ radialObjective μ b (envelopeRadius μ D a) := by
      unfold envelope radialObjective
      exact sub_le_sub_right (mul_le_mul_of_nonneg_right hab hrad) _
    _ ≤ envelope μ D b := radialObjective_le_envelope hμ hb envelopeRadius_le

theorem envelope_scale_upper {μ D a c : ℝ} (hμ : 0 ≤ μ) (_hD : 0 ≤ D)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    envelope μ D (c * a) ≤ c * envelope μ D a := by
  let r := envelopeRadius μ D (c * a)
  have hbound := radialObjective_le_envelope (r := r) hμ ha envelopeRadius_le
  have hmul := mul_le_mul_of_nonneg_left hbound hc
  have hterm : 0 ≤ (1 - c) * μ * r ^ 2 :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc1) hμ) (sq_nonneg r)
  change radialObjective μ (c * a) r ≤ c * envelope μ D a
  unfold radialObjective at *
  nlinarith

theorem envelope_scale_lower {μ D a c : ℝ} (hμ : 0 ≤ μ) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    c ^ 2 * envelope μ D a ≤ envelope μ D (c * a) := by
  let r := envelopeRadius μ D a
  have hr0 : 0 ≤ r := envelopeRadius_nonneg hμ hD ha
  have hrD : r ≤ D := envelopeRadius_le
  have hcr : c * r ≤ D := (mul_le_of_le_one_left hr0 hc1).trans hrD
  have hbound := radialObjective_le_envelope hμ (mul_nonneg hc ha) hcr
  calc
    c ^ 2 * envelope μ D a = radialObjective μ (c * a) (c * r) := by
      change c ^ 2 * radialObjective μ a r = _
      unfold radialObjective
      ring
    _ ≤ envelope μ D (c * a) := hbound

theorem envelope_le_linear {μ D a : ℝ} (hμ : 0 ≤ μ) (ha : 0 ≤ a) :
    envelope μ D a ≤ D * a := by
  have hrad := envelopeRadius_le (μ := μ) (D := D) (a := a)
  have hm := mul_le_mul_of_nonneg_left hrad ha
  have hs := mul_nonneg hμ (sq_nonneg (envelopeRadius μ D a))
  unfold envelope radialObjective
  nlinarith

theorem envelope_le_quadratic {μ D a : ℝ} (hμ : 0 < μ) :
    envelope μ D a ≤ a ^ 2 / (2 * μ) := by
  have hbound := radialObjective_le_at_critical
    (r := envelopeRadius μ D a) (x := a / μ) hμ.le
    (mul_div_cancel₀ a (ne_of_gt hμ))
  have heq : radialObjective μ a (a / μ) = a ^ 2 / (2 * μ) := by
    unfold radialObjective
    field_simp; ring
  exact heq ▸ hbound

theorem envelope_lower_min {μ D a : ℝ} (hμ : 0 < μ) (hD : 0 ≤ D)
    (_ha : 0 ≤ a) :
    (1 / 2 : ℝ) * min (D * a) (a ^ 2 / μ) ≤ envelope μ D a := by
  by_cases hsmall : a ≤ μ * D
  · rw [envelope_quadratic hμ hsmall]
    have hm := min_le_right (D * a) (a ^ 2 / μ)
    calc
      (1 / 2 : ℝ) * min (D * a) (a ^ 2 / μ) ≤ (1 / 2) * (a ^ 2 / μ) :=
        mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = a ^ 2 / (2 * μ) := by ring
  · have hlarge : μ * D ≤ a := le_of_not_ge hsmall
    rw [envelope_linear hμ hlarge]
    have hprod := mul_le_mul_of_nonneg_right hlarge hD
    have hm := min_le_left (D * a) (a ^ 2 / μ)
    nlinarith

theorem envelope_comparison {μ D a : ℝ} (hμ : 0 < μ) (hD : 0 ≤ D)
    (ha : 0 ≤ a) :
    (1 / 2 : ℝ) * min (D * a) (a ^ 2 / μ) ≤ envelope μ D a ∧
      envelope μ D a ≤ min (D * a) (a ^ 2 / μ) := by
  refine ⟨envelope_lower_min hμ hD ha, le_min (envelope_le_linear hμ.le ha) ?_⟩
  have hq := envelope_le_quadratic (D := D) (a := a) hμ
  have hpos := div_nonneg (sq_nonneg a) hμ.le
  have hid : a ^ 2 / (2 * μ) = (a ^ 2 / μ) / 2 := by ring
  rw [hid] at hq
  linarith

end

end HeavyTail
