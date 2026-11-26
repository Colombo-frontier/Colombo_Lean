import MatchingBounds1005.AlgorithmQueryTrace
import MatchingBounds1005.ReadoutIsometry

/-! The measurable canonical event gives the exact physical stopped-prefix
projection bound used by the adaptive tensor energy estimate. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
namespace MatchingBounds1005.Model
open ScheduledPrefix ChronologicalProjection
variable {Seed : Type} [MeasurableSpace Seed] {d : ℕ}

theorem geometryEvent_physical {ι : Type*} (R : ℝ) (A : Algorithm d Seed) (T : ℕ)
    (b : ι → Space d) (ell : ι → ℕ) (θ : ℝ)
    (z : (Rotation (Space d) × Seed) × (Fin T → Response d))
    (hz : z ∈ geometryEvent R A T b ell θ) :
    queryTrace R A T (z.1.2, z.2) ∈ readoutEvent (fun s => isometry _ z.1.1 (b s)) ell θ := by
  have h := (readoutEvent_isometry (isometry _ z.1.1) b ell θ
    (canonicalQueryTrace R A T z)).mpr hz
  simpa only [canonicalQueryTrace, LinearIsometryEquiv.apply_symm_apply] using h

theorem geometryEvent_physical_projection {ι : Type*} (R : ℝ) (A : Algorithm d Seed) (T : ℕ)
    (b : ι → Space d) (ell : ι → ℕ) {θ : ℝ} (hθ : 0 ≤ θ)
    (z : (Rotation (Space d) × Seed) × (Fin T → Response d))
    (hz : z ∈ geometryEvent R A T b ell θ) (s : ι) :
    ‖(prefixSpan (List.ofFn (queryTrace R A T (z.1.2, z.2))) (ell s)).orthogonalProjection
      (isometry _ z.1.1 (b s))‖ ≤ θ * ‖b s‖ := by
  simpa only [LinearIsometryEquiv.norm_map] using
    readoutEvent_projection hθ (geometryEvent_physical R A T b ell θ z hz) s

end MatchingBounds1005.Model
