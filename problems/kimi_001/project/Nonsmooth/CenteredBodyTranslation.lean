import Nonsmooth.GrunbaumApplication

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def centeredBody (x : E) (K : Set E) : Set E := {z | z + x ∈ K}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem centeredBody_convex (x : E) {K : Set E} (hK : Convex ℝ K) :
    Convex ℝ (centeredBody x K) := by
  intro u hu v hv a b ha hb hab
  have h := hK hu hv ha hb hab
  change a • u + b • v + x ∈ K
  convert h using 1
  rw [smul_add, smul_add]
  calc
    a • u + b • v + x = a • u + b • v + (a • x + b • x) := by
      rw [← add_smul, hab, one_smul]
    _ = a • u + a • x + (b • v + b • x) := by abel

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem centeredBody_compact (x : E) {K : Set E} (hK : IsCompact K) :
    IsCompact (centeredBody x K) :=
  (Homeomorph.addRight x).isCompact_preimage.mpr hK

theorem centeredBody_volume (x : E) (K : Set E) : volume (centeredBody x K) = volume K :=
  measure_preimage_add_right volume x K

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem centeredBody_contains_ball {x : E} {K : Set E} (hx : x ∈ interior K) :
    ∃ r > 0, Metric.closedBall (0 : E) r ⊆ centeredBody x K := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hx)
  refine ⟨r, hr, ?_⟩
  intro z hz
  apply hsub
  simpa [Metric.mem_closedBall, dist_eq_norm] using hz

theorem centeredBody_quarter_depth {x : E} {K : Set E}
    (hdepth : ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
      ENNReal.ofReal (1 / 4 : ℝ) * volume K ≤ volume (K ∩ {z | ℓ z ≤ ℓ x})) :
    ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 → ENNReal.ofReal (1 / 4 : ℝ) * volume (centeredBody x K) ≤
      volume (centeredBody x K ∩ {z | 0 ≤ ℓ z}) := by
  intro ℓ hℓ
  have hneg : -ℓ ≠ 0 := neg_ne_zero.mpr hℓ
  have h := hdepth (-ℓ) hneg
  have hset : centeredBody x K ∩ {z | 0 ≤ ℓ z} =
      centeredBody x (K ∩ {z | (-ℓ) z ≤ (-ℓ) x}) := by
    ext z
    simp only [centeredBody, mem_inter_iff, mem_setOf_eq, ContinuousLinearMap.neg_apply, map_add]
    constructor <;> rintro ⟨hz, hle⟩ <;> exact ⟨hz, by linarith⟩
  rw [hset, centeredBody_volume, centeredBody_volume]
  exact h

end
end Nonsmooth
