import Nonsmooth.ImportedGeometryMain
import Nonsmooth.GrunbaumConstantBound

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem finite_volume_ratio_to_fraction {u v : ℝ≥0∞} (hu : u ≠ ⊤)
    (hv0 : v ≠ 0) (hv : v ≠ ⊤) {c : ℝ} (hc : c ≤ (u / v).toReal) :
    ENNReal.ofReal c * v ≤ u := by
  have hfinite : u / v ≠ ⊤ := by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_ne_top hu (by simpa using hv0)
  have h := ENNReal.ofReal_le_ofReal hc
  rw [ENNReal.ofReal_toReal hfinite] at h
  calc
    ENNReal.ofReal c * v ≤ (u / v) * v := mul_le_mul_right' h v
    _ = u := by rw [div_eq_mul_inv, ENNReal.inv_mul_cancel_right hv0 hv]

open ImportedGeometry.Grunbaum

/-- The imported sharp theorem implies a uniform quarter-volume depth at the centroid. -/
theorem imported_grunbaum_centroid_quarter {d : ℕ} (C : FullDimensionalConvexBody d)
    (ℓ : Euc d →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ENNReal.ofReal (1 / 4 : ℝ) * volume (C : Set (Euc d)) ≤
      volume ((C : Set (Euc d)) ∩ {z | ℓ z ≤ ℓ C.centroid}) := by
  have hsharp := grunbaum_centroid_halfspace_functional C ℓ hℓ (ℓ C.centroid) le_rfl
  have hquarter : (1 / 4 : ℝ) ≤ grunbaumConstant d := by
    simpa only [grunbaumConstant, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
      show (1 : ℝ) + 1 = 2 by norm_num] using
      grunbaum_scalar_constant_quarter (d + 1) (by omega)
  apply finite_volume_ratio_to_fraction
    (ne_of_lt ((measure_mono inter_subset_left).trans_lt C.isCompact.measure_lt_top))
    C.volume_ne_zero C.volume_ne_top
  exact hquarter.trans hsharp

theorem imported_grunbaum_centroid_mem {d : ℕ} (C : FullDimensionalConvexBody d) :
    C.centroid ∈ (C : Set (Euc d)) := by
  apply C.convex.set_average_mem C.isClosed C.volume_ne_zero C.volume_ne_top
  · exact ae_restrict_mem C.isClosed.measurableSet
  · exact continuous_id.continuousOn.integrableOn_compact C.isCompact

end
end Nonsmooth
