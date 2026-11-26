import HeavyTail.GaussianMomentModel
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Ambient-space orthogonal projection preserves both raw noise moment bounds.
The corrected-observation mean is computed from the actual integral. -/
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

def ambientProjection : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjection

theorem ambientProjection_norm (x : E) : ‖ambientProjection K x‖ ≤ ‖x‖ := by
  change ‖K.orthogonalProjection x‖ ≤ ‖x‖
  exact (K.orthogonalProjection.le_opNorm x).trans (by
    have h := mul_le_mul_of_nonneg_right K.orthogonalProjection_norm_le (norm_nonneg x)
    simpa only [one_mul] using h)

theorem ambientProjection_inner (v x : E) :
    ⟪v, ambientProjection K x⟫_ℝ = ⟪ambientProjection K v, x⟫_ℝ :=
  (K.inner_orthogonalProjection_left_eq_right v x).symm

theorem ambientProjection_mem (x : E) : ambientProjection K x ∈ K :=
  (K.orthogonalProjection x).property

theorem ambientProjection_eq_self {x : E} (hx : x ∈ K) : ambientProjection K x = x := by
  have h := congrArg (fun v : K => (v : E)) (K.orthogonalProjection_mem_subspace_eq_self ⟨x, hx⟩)
  exact h

section Probability
variable [MeasurableSpace Ω] [CompleteSpace E] {P : Measure Ω} [IsProbabilityMeasure P]

theorem projectedNoise_memLp {ξ : Ω → E} {p : ℝ≥0∞} (hξ : MemLp ξ p P) :
    MemLp (fun ω => ambientProjection K (ξ ω)) p P :=
  (ambientProjection K).comp_memLp' hξ

theorem projectedNoise_centered {ξ : Ω → E} (hξ : Integrable ξ P)
    (hzero : ∫ ω, ξ ω ∂P = 0) : (∫ ω, ambientProjection K (ξ ω) ∂P) = 0 := by
  rw [(ambientProjection K).integral_comp_comm hξ, hzero, map_zero]

theorem projectedNoise_norm_moment {ξ : Ω → E} {p L : ℝ} (hp : 0 < p)
    (hξ : MemLp ξ (ENNReal.ofReal p) P)
    (hstrong : (∫ ω, ‖ξ ω‖ ^ p ∂P) ≤ L ^ p) :
    (∫ ω, ‖ambientProjection K (ξ ω)‖ ^ p ∂P) ≤ L ^ p := by
  have hpj := projectedNoise_memLp K hξ
  have hi : Integrable (fun ω => ‖ξ ω‖ ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hξ.integrable_norm_rpow'
  have hj : Integrable (fun ω => ‖ambientProjection K (ξ ω)‖ ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hpj.integrable_norm_rpow'
  exact (integral_mono hj hi (fun ω => Real.rpow_le_rpow (norm_nonneg _)
    (ambientProjection_norm K (ξ ω)) hp.le)).trans hstrong

theorem projectedNoise_weak_moment [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {ξ : Ω → E} {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s)
    (hweak : ∀ v : E, ‖v‖ = 1 → (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ s ^ p)
    (v : E) (hv : ‖v‖ = 1) :
    (∫ ω, |⟪v, ambientProjection K (ξ ω)⟫_ℝ| ^ p ∂P) ≤ s ^ p := by
  simp_rw [ambientProjection_inner]
  have hb := GaussianEstimates.unit_direction_bound E hp hs hweak (ambientProjection K v)
  apply hb.trans
  have hvp : ‖ambientProjection K v‖ ≤ 1 := (ambientProjection_norm K v).trans_eq hv
  apply Real.rpow_le_rpow (by positivity) _ hp.le
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hvp hs

theorem correctedProjected_observation_mean {g : Ω → E} (hg : Integrable g P) (a : E) :
    (∫ ω, ambientProjection K (g ω) + a ∂P) = ambientProjection K (∫ ω, g ω ∂P) + a := by
  rw [integral_add ((ambientProjection K).integrable_comp hg) (integrable_const a),
    (ambientProjection K).integral_comp_comm hg, integral_const]
  simp

theorem correctedProjected_observation_center (g : Ω → E) (b a : E) (ω : Ω) :
    ambientProjection K (g ω) + a - (ambientProjection K b + a) =
      ambientProjection K (g ω - b) := by
  rw [map_sub]
  abel

end Probability
end HeavyTail
