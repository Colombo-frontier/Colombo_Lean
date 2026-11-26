import Bilevel.TransportedSphere

/-! Concentration for any genuine transitive isometric Haar action on a sphere. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal RealInnerProductSpace
namespace Bilevel.HomogeneousSphere
open EuclideanGaussian

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Group G] [MeasurableSpace G] [MeasurableMul G]
  [MulAction G E] [MeasurableSMul₂ G E]
  (ν : Measure G) [IsProbabilityMeasure ν] [IsMulRightInvariant ν]
  {n : ℕ} (e : E ≃ₗᵢ[ℝ] Space (n + 1))
  (rotation : G → E ≃ₗᵢ[ℝ] E) (hrotation : ∀ g x, g • x = rotation g x)
  (transitive : ∀ x y : E, ‖x‖ = ‖y‖ → ∃ g : G, g • x = y)

include transitive in
omit [MeasurableSMul₂ G E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [IsProbabilityMeasure ν] in
theorem orbit_average_eq (f : E → ℝ≥0∞) (x y : E) (hxy : ‖x‖ = ‖y‖) :
    (∫⁻ g, f (g • y) ∂ν) = ∫⁻ g, f (g • x) ∂ν := by
  obtain ⟨g, rfl⟩ := transitive x y hxy
  simp_rw [← mul_smul]
  exact lintegral_mul_right_eq_self (fun h : G => f (h • x)) g

include e rotation hrotation transitive in
theorem orbit_lintegral (f : E → ℝ≥0∞) (hf : Measurable f) (x : E) (hx : ‖x‖ = 1) :
    (∫⁻ g, f (g • x) ∂ν) = ∫⁻ y, f y ∂TransportedSphere.law e := by
  have hp : ∀ g : G, MeasurePreserving (fun y : E => g • y)
      (TransportedSphere.law e) (TransportedSphere.law e) := by
    intro g
    simpa only [hrotation] using TransportedSphere.orthogonal_invariance e (rotation g)
  calc
    _ = ∫⁻ _y, (∫⁻ g, f (g • x) ∂ν) ∂TransportedSphere.law e := by simp
    _ = ∫⁻ y, ∫⁻ g, f (g • y) ∂ν ∂TransportedSphere.law e := by
      apply lintegral_congr_ae
      filter_upwards [TransportedSphere.unit_norm_ae e] with y hy
      exact (orbit_average_eq ν transitive f x y (hx.trans hy.symm)).symm
    _ = ∫⁻ g, ∫⁻ y, f (g • y) ∂TransportedSphere.law e ∂ν := by
      apply lintegral_lintegral_swap
      exact (hf.comp (measurable_snd.smul measurable_fst)).aemeasurable
    _ = _ := InvariantAdaptation.lintegral_action_average ν _ hp f hf

include rotation hrotation transitive in
theorem orbit_preserving (x : E) (hx : ‖x‖ = 1) :
    MeasurePreserving (fun g : G => g • x) ν (TransportedSphere.law e) := by
  have hm : Measurable (fun g : G => g • x) := measurable_id.smul measurable_const
  refine ⟨hm, ?_⟩
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  rw [lintegral_map hf hm]
  exact orbit_lintegral ν e rotation hrotation transitive f hf x hx

include e rotation hrotation transitive in
theorem directional_tail (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w x : E) (hw : ‖w‖ = 1) (hx : ‖x‖ = 1) :
    ν.real {g : G | t ≤ ⟪w, (g • x : E)⟫ ^ 2} ≤ 2 * Real.exp (-(n : ℝ) * t / 8) := by
  have hs : MeasurableSet {y : E | t ≤ ⟪w, y⟫ ^ 2} :=
    measurableSet_le measurable_const ((continuous_const.inner continuous_id).measurable.pow_const 2)
  change ν.real ((fun g : G => g • x) ⁻¹' {y | t ≤ ⟪w, y⟫ ^ 2}) ≤ _
  rw [SphericalGaussian.measureReal_preimage
    (orbit_preserving ν e rotation hrotation transitive x hx) _ hs]
  exact TransportedSphere.directional_tail e t ht ht2 w hw

include e rotation hrotation transitive in
theorem directional_tail_unit_ball (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w x : E) (hw : ‖w‖ = 1) (hx : ‖x‖ ≤ 1) :
    ν.real {g : G | t ≤ ⟪w, (g • x : E)⟫ ^ 2} ≤ 2 * Real.exp (-(n : ℝ) * t / 8) := by
  by_cases hz : x = 0
  · subst x
    have he : {g : G | t ≤ ⟪w, (g • (0 : E) : E)⟫ ^ 2} = ∅ := by
      ext g
      simp only [Set.mem_setOf_eq, hrotation, map_zero, inner_zero_right, zero_pow (by decide : 2 ≠ 0),
        Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr ht
    rw [he, measureReal_empty]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hz
  let u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, Real.norm_eq_abs, abs_of_pos hn, hn.ne']
  have hsub : {g : G | t ≤ ⟪w, (g • x : E)⟫ ^ 2} ⊆
      {g : G | t ≤ ⟪w, (g • u : E)⟫ ^ 2} := by
    intro g hg
    have hr : ‖x‖ • (g • u : E) = g • x := by
      simp [hrotation, u, smul_smul, hn.ne']
    have hinner : ⟪w, (g • x : E)⟫ ^ 2 = ‖x‖ ^ 2 * ⟪w, (g • u : E)⟫ ^ 2 := by
      rw [← hr, real_inner_smul_right, mul_pow]
    have hnorm : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hmul := mul_le_mul_of_nonneg_right hnorm (sq_nonneg ⟪w, (g • u : E)⟫)
    change t ≤ ⟪w, (g • u : E)⟫ ^ 2
    change t ≤ ⟪w, (g • x : E)⟫ ^ 2 at hg
    rw [hinner] at hg
    nlinarith
  exact (measureReal_mono hsub).trans
    (directional_tail ν e rotation hrotation transitive t ht ht2 w u hw hu)

end Bilevel.HomogeneousSphere
