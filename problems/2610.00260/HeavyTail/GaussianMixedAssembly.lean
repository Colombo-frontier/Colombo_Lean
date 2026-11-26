import HeavyTail.ScalarClipping
import HeavyTail.GaussianNoiseProduct
import HeavyTail.GaussianShifted

/-! Integration of the scalar clipping estimate against an actual probability
measure. The Gaussian product modules supply its moment ingredients; this
file does not yet identify all of those ingredients with the complete
bounded-center Gaussian mixture of `lem:mixed-exp`.

Any eventual learning-rate specialization must explicitly require `η ≥ 0`.
-/
noncomputable section
open MeasureTheory Filter
namespace HeavyTail.GaussianEstimates

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integrated_mixed_scalar {p ε : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hε : ε = -1 ∨ ε = 1) {t u v : Ω → ℝ}
    (ht : Measurable t) (hu : Measurable u) (hv : Measurable v)
    (hlin : Integrable (fun ω => u ω + v ω) P)
    (hzero : (∫ ω, u ω + v ω ∂P) = 0)
    (hU : Integrable (fun ω => Real.exp (2 * |t ω|) * |u ω| ^ p) P)
    (hV : Integrable (fun ω => Real.exp (2 * |t ω|) * (v ω) ^ 2) P)
    (hT : Integrable (fun ω => Real.exp (2 * |t ω|) *
      (if 1 / 2 < |t ω| then (t ω) ^ 2 else 0)) P) :
    (∫ ω, Real.exp (ε * (HeavyTail.clip (t ω + u ω + v ω) - t ω)) ∂P) ≤
      1 + 100 * ((∫ ω, Real.exp (2 * |t ω|) * |u ω| ^ p ∂P) +
        (∫ ω, Real.exp (2 * |t ω|) * (v ω) ^ 2 ∂P) +
        (∫ ω, Real.exp (2 * |t ω|) *
          (if 1 / 2 < |t ω| then (t ω) ^ 2 else 0) ∂P)) := by
  let A := fun ω => Real.exp (2 * |t ω|) * |u ω| ^ p
  let B := fun ω => Real.exp (2 * |t ω|) * (v ω) ^ 2
  let C := fun ω => Real.exp (2 * |t ω|) * (if 1 / 2 < |t ω| then (t ω) ^ 2 else 0)
  let H := fun ω => (1 + ε * (u ω + v ω)) + 100 * (A ω + B ω + C ω)
  have hH : Integrable H P :=
    ((integrable_const 1).add (hlin.const_mul ε)).add (((hU.add hV).add hT).const_mul 100)
  have hpoint (ω : Ω) : Real.exp (ε * (HeavyTail.clip (t ω + u ω + v ω) - t ω)) ≤ H ω := by
    have h := HeavyTail.mixed_scalar hp hp2 (t ω) (u ω) (v ω) ε hε
    dsimp [H, A, B, C]
    nlinarith
  have hi : Integrable
      (fun ω => Real.exp (ε * (HeavyTail.clip (t ω + u ω + v ω) - t ω))) P := by
    apply hH.mono'
    · apply Measurable.aestronglyMeasurable
      unfold HeavyTail.clip
      fun_prop
    · exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hpoint ω
  have h := integral_mono hi hH hpoint
  have he : (∫ ω, H ω ∂P) = 1 + 100 * ((∫ ω, A ω ∂P) +
      (∫ ω, B ω ∂P) + (∫ ω, C ω ∂P)) := by
    have ha : Integrable A P := hU
    have hb : Integrable B P := hV
    have hc : Integrable C P := hT
    have hsplit : (∫ ω, H ω ∂P) = (∫ ω, 1 + ε * (u ω + v ω) ∂P) +
        ∫ ω, 100 * (A ω + B ω + C ω) ∂P :=
      integral_add ((integrable_const 1).add (hlin.const_mul ε))
        (((ha.add hb).add hc).const_mul 100)
    have hfirst : (∫ ω, 1 + ε * (u ω + v ω) ∂P) =
        (∫ _ : Ω, (1 : ℝ) ∂P) + ∫ ω, ε * (u ω + v ω) ∂P :=
      integral_add (integrable_const 1) (hlin.const_mul ε)
    have habc : (∫ ω, A ω + B ω + C ω ∂P) =
        (∫ ω, A ω ∂P) + (∫ ω, B ω ∂P) + (∫ ω, C ω ∂P) := by
      have hsplit' : (∫ ω, A ω + B ω + C ω ∂P) =
          (∫ ω, A ω + B ω ∂P) + ∫ ω, C ω ∂P := integral_add (ha.add hb) hc
      have hab : (∫ ω, A ω + B ω ∂P) =
          (∫ ω, A ω ∂P) + ∫ ω, B ω ∂P := integral_add ha hb
      rw [hsplit', hab]
    rw [hsplit, hfirst, integral_const, integral_const_mul, hzero, integral_const_mul, habc]
    simp only [measureReal_univ_eq_one, one_smul, mul_zero, add_zero]
  rw [he] at h
  exact h

end HeavyTail.GaussianEstimates
