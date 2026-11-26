import Nonsmooth.GrunbaumApplication
import Nonsmooth.ProtasovVolumeCertificate

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem closed_halfspace_volume_partition (K : Set E) (hK : MeasurableSet K)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    volume (K ∩ {z | ℓ z ≤ 0}) + volume (K ∩ {z | 0 ≤ ℓ z}) = volume K := by
  have hinter : volume ((K ∩ {z | ℓ z ≤ 0}) ∩ (K ∩ {z | 0 ≤ ℓ z})) = 0 := by
    apply measure_mono_null _ (ImportedGeometry.Grunbaum.volume_preimage_singleton_eq_zero ℓ hℓ 0)
    intro z hz
    exact le_antisymm hz.1.2 hz.2.2
  have hunion : (K ∩ {z | ℓ z ≤ 0}) ∪ (K ∩ {z | 0 ≤ ℓ z}) = K := by
    ext z
    constructor
    · rintro (hz | hz) <;> exact hz.1
    · intro hz
      rcases le_total (ℓ z) 0 with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have h := measure_union_add_inter (μ := (volume : Measure E))
    (t := K ∩ {z | 0 ≤ ℓ z}) (K ∩ {z | ℓ z ≤ 0})
    (hK.inter (measurableSet_le measurable_const ℓ.measurable))
  simpa only [hinter, hunion, add_zero] using h.symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem convex_contraction_into_negative_halfspace {K : Set E} (hK : Convex ℝ K)
    (ℓ : E →L[ℝ] ℝ) {x : E} (hx : x ∈ K) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hax : ℓ x = -a) (hbound : ∀ z ∈ K, ℓ z ≤ b) :
    (fun z => (1 - a / (a + b)) • x + (a / (a + b)) • z) '' K ⊆
      K ∩ {z | ℓ z ≤ 0} := by
  have hab : 0 < a + b := by linarith
  have ht : 0 ≤ a / (a + b) := div_nonneg ha hab.le
  have ht1 : a / (a + b) ≤ 1 := (div_le_one hab).mpr (by linarith)
  rintro z ⟨y, hy, rfl⟩
  refine ⟨hK hx hy (sub_nonneg.mpr ht1) ht (by ring), ?_⟩
  simp only [mem_setOf_eq, map_add, map_smul, smul_eq_mul, hax]
  have h := mul_le_mul_of_nonneg_left (hbound y hy) ht
  have hid : (1 - a / (a + b)) * (-a) + (a / (a + b)) * b = 0 := by
    field_simp
    ring
  linarith

theorem finite_volume_scalar_add_cancel {v : ℝ≥0∞} (hv0 : v ≠ 0) (hv : v ≠ ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ENNReal.ofReal a * v + ENNReal.ofReal b * v ≤ v) : a + b ≤ 1 := by
  rw [← add_mul, ← ENNReal.ofReal_add ha hb] at h
  have h' : ENNReal.ofReal (a + b) ≤ 1 := by
    exact (ENNReal.mul_le_mul_iff_left hv0 hv).mp (by simpa using h)
  exact (ENNReal.ofReal_le_one).mp h'

theorem halfspace_depth_scalar_asymmetry {K : Set E} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (hK0 : volume K ≠ 0) (hKf : volume K ≠ ⊤)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {x : E} (hx : x ∈ K)
    {a b κ : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hκ : 0 ≤ κ)
    (hax : ℓ x = -a) (hbound : ∀ z ∈ K, ℓ z ≤ b)
    (hdepth : ENNReal.ofReal κ * volume K ≤ volume (K ∩ {z | 0 ≤ ℓ z})) :
    κ * (a + b) ≤ (Module.finrank ℝ E : ℝ) * b := by
  have hab : 0 < a + b := by linarith
  have ht : 0 ≤ a / (a + b) := div_nonneg ha hab.le
  have hvol := measure_mono (μ := (volume : Measure E))
    (convex_contraction_into_negative_halfspace hK ℓ hx ha hb hax hbound)
  rw [addHaar_convex_contraction volume K x ht] at hvol
  have hsum := add_le_add hvol hdepth
  rw [closed_halfspace_volume_partition K hKm ℓ hℓ] at hsum
  have hscalar := finite_volume_scalar_add_cancel hK0 hKf (pow_nonneg ht _) hκ hsum
  have hbern := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ a / (a + b) by linarith)
    (Module.finrank ℝ E)
  have hstep : κ ≤ (Module.finrank ℝ E : ℝ) * (1 - a / (a + b)) := by linarith
  have heq : (Module.finrank ℝ E : ℝ) * (1 - a / (a + b)) =
      ((Module.finrank ℝ E : ℝ) * b) / (a + b) := by
    field_simp
    ring
  rw [heq] at hstep
  exact (le_div_iff₀ hab).mp hstep

end
end Nonsmooth
