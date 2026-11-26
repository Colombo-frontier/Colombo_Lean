import HeavyTail.InteriorQuery
import HeavyTail.ProbabilityTools
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Projection

/-! Relative-interior queries and tangent subgradient bounds in the original
ambient space, including lower-dimensional feasible sets. -/
noncomputable section
open Set MeasureTheory AffineSubspace
open scoped InnerProductSpace Topology
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem intrinsicInterior_ball_iff {X : Set E} {w : E} :
    w ∈ intrinsicInterior ℝ X ↔ w ∈ affineSpan ℝ X ∧
      ∃ ε > 0, ∀ u ∈ affineSpan ℝ X, ‖u - w‖ < ε → u ∈ X := by
  constructor
  · intro hw
    obtain ⟨w', hw', rfl⟩ := mem_intrinsicInterior.mp hw
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hw')
    refine ⟨w'.property, ε, hε, ?_⟩
    intro u hu hnear
    apply hball (a := (⟨u, hu⟩ : affineSpan ℝ X))
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hnear
  · rintro ⟨hw, ε, hε, hball⟩
    apply mem_intrinsicInterior.mpr
    refine ⟨⟨w, hw⟩, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
    apply Metric.mem_nhds_iff.mpr
    refine ⟨ε, hε, ?_⟩
    intro u hu
    apply hball u u.property
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hu

/-- Every positive convex interpolation toward a relative-interior anchor
belongs to the relative interior; no ambient full-dimensionality is assumed. -/
theorem convex_relativeInterior_interpolation {X : Set E} (hX : Convex ℝ X)
    {y anchor : E} (hy : y ∈ X) (ha : anchor ∈ intrinsicInterior ℝ X)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    y + t • (anchor - y) ∈ intrinsicInterior ℝ X := by
  obtain ⟨haA, r, hr, hball⟩ := intrinsicInterior_ball_iff.mp ha
  have hyA : y ∈ affineSpan ℝ X := subset_affineSpan ℝ X hy
  let w := y + t • (anchor - y)
  have hwA : w ∈ affineSpan ℝ X := by
    simpa only [w, vsub_eq_sub, vadd_eq_add, add_comm] using
      (affineSpan ℝ X).smul_vsub_vadd_mem t haA hyA hyA
  apply intrinsicInterior_ball_iff.mpr
  refine ⟨hwA, t * r, mul_pos ht hr, ?_⟩
  intro u huA hnear
  let v := anchor + t⁻¹ • (u - w)
  have hvA : v ∈ affineSpan ℝ X := by
    simpa only [v, vsub_eq_sub, vadd_eq_add, add_comm] using
      (affineSpan ℝ X).smul_vsub_vadd_mem t⁻¹ huA hwA haA
  have hvdist : ‖v - anchor‖ = ‖u - w‖ / t := by
    have hvsub : v - anchor = t⁻¹ • (u - w) := by dsimp [v]; abel
    rw [hvsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    ring
  have hv : v ∈ X := hball v hvA (by
    rw [hvdist]
    apply (div_lt_iff₀ ht).mpr
    nlinarith only [hnear])
  have hcombo := hX hy hv (by linarith : 0 ≤ 1 - t) ht.le (by ring : 1 - t + t = 1)
  have hvscale : t • v = t • anchor + (u - w) := by
    dsimp only [v]
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have heq : (1 - t) • y + t • v = u := by
    rw [hvscale]
    dsimp only [w]
    simp only [sub_smul, one_smul, smul_sub]
    abel
  exact heq ▸ hcombo

theorem relativeInteriorQuery_mem {X : Set E} (hX : Convex ℝ X) {anchor y : E}
    (ha : anchor ∈ intrinsicInterior ℝ X) (hy : y ∈ X) {ε : ℝ} (hε : 0 < ε) :
    interiorQuery ε anchor y ∈ intrinsicInterior ℝ X :=
  convex_relativeInterior_interpolation hX hy ha
    (interiorQueryWeight_mem hε anchor y).1 (interiorQueryWeight_mem hε anchor y).2

theorem relativeInterior_subgradient_direction_upper {X : Set E} {f : E → ℝ}
    {w g v : E} {G : ℝ} (hw : w ∈ intrinsicInterior ℝ X)
    (hv : v ∈ (affineSpan ℝ X).direction) (hv1 : ‖v‖ = 1)
    (hsub : ∀ u ∈ X, ⟪g, u - w⟫_ℝ ≤ f u - f w)
    (hlip : ∀ u ∈ X, f u - f w ≤ G * ‖u - w‖) : ⟪g, v⟫_ℝ ≤ G := by
  obtain ⟨hwA, r, hr, hball⟩ := intrinsicInterior_ball_iff.mp hw
  let u := w + (r / 2) • v
  have huA : u ∈ affineSpan ℝ X := by
    simpa only [u, vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction ((affineSpan ℝ X).direction.smul_mem (r / 2) hv) hwA
  have husub : u - w = (r / 2) • v := by dsimp [u]; abel
  have hdist : ‖u - w‖ = r / 2 := by
    rw [husub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hv1, mul_one]
  have hu : u ∈ X := hball u huA (by rw [hdist]; linarith)
  have h := (hsub u hu).trans (hlip u hu)
  rw [husub, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < r / 2), hv1, mul_one] at h
  apply (mul_le_mul_left (by positivity : 0 < r / 2)).mp
  nlinarith only [h]

theorem relativeInterior_subgradient_direction_bound {X : Set E} {f : E → ℝ}
    {w g v : E} {G : ℝ} (hw : w ∈ intrinsicInterior ℝ X)
    (hv : v ∈ (affineSpan ℝ X).direction) (hv1 : ‖v‖ = 1)
    (hsub : ∀ u ∈ X, ⟪g, u - w⟫_ℝ ≤ f u - f w)
    (hlip : ∀ u ∈ X, f u - f w ≤ G * ‖u - w‖) : |⟪g, v⟫_ℝ| ≤ G := by
  have hup := relativeInterior_subgradient_direction_upper hw hv hv1 hsub hlip
  have hlo := relativeInterior_subgradient_direction_upper hw
    ((affineSpan ℝ X).direction.neg_mem hv) (by simpa using hv1) hsub hlip
  rw [inner_neg_right] at hlo
  exact abs_le.mpr ⟨by linarith only [hlo], hup⟩

theorem relativeInterior_projected_subgradient_norm [FiniteDimensional ℝ E]
    {X : Set E} {f : E → ℝ} {w g : E} {G : ℝ} (hG : 0 ≤ G)
    (hw : w ∈ intrinsicInterior ℝ X)
    (hsub : ∀ u ∈ X, ⟪g, u - w⟫_ℝ ≤ f u - f w)
    (hlip : ∀ u ∈ X, f u - f w ≤ G * ‖u - w‖) :
    ‖(affineSpan ℝ X).direction.orthogonalProjection g‖ ≤ G := by
  apply norm_le_of_unit_inner_bound hG
  intro v hv
  rw [Submodule.inner_orthogonalProjection_eq_of_mem_left, real_inner_comm]
  exact relativeInterior_subgradient_direction_bound hw v.property hv hsub hlip

end HeavyTail
