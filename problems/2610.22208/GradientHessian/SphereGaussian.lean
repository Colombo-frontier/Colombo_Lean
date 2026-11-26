import GradientHessian.GaussianLinear

/-! # A genuine rotational sphere law and an exponential linear tail

The law is the radial projection of the actual standard Gaussian. We prove
unit-sphere support and invariance under every linear isometry. The tail here
has a Gaussian radial-error term; it is a usable exponential estimate, but is
not the sharper spherical MGF estimate stated in source `eq:sphere`.
-/

namespace GradientHessian.SphereGaussian
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def direction (z : E) : E := ‖z‖⁻¹ • z

theorem direction_measurable : Measurable (direction (E := E)) :=
  measurable_id.norm.inv.smul measurable_id

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem direction_norm {z : E} (hz : z ≠ 0) : ‖direction z‖ = 1 := by
  simp [direction, norm_smul, hz]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem direction_isometry (e : E ≃ₗᵢ[ℝ] E) (z : E) :
    e (direction z) = direction (e z) := by simp [direction]

def sphereLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure E :=
  (GaussianHilbert.euclideanGaussianLaw E).map direction

instance : IsProbabilityMeasure (sphereLaw E) :=
  isProbabilityMeasure_map direction_measurable.aemeasurable

theorem sphereLaw_isometry (e : E ≃ₗᵢ[ℝ] E) : (sphereLaw E).map e = sphereLaw E := by
  rw [sphereLaw, Measure.map_map e.continuous.measurable direction_measurable]
  have he : (fun z => e (direction z)) = fun z => direction (e z) :=
    funext (direction_isometry e)
  change (GaussianHilbert.euclideanGaussianLaw E).map (fun z => e (direction z)) = _
  rw [he]
  change (GaussianHilbert.euclideanGaussianLaw E).map (direction ∘ e) = _
  rw [← Measure.map_map direction_measurable e.continuous.measurable,
    GaussianHilbert.euclideanGaussian_isometry]

theorem sphereLaw_unit [Nontrivial E] : ∀ᵐ z ∂sphereLaw E, ‖z‖ = 1 := by
  have hn : ∀ᵐ z ∂GaussianHilbert.euclideanGaussianLaw E, z ≠ 0 := by
    rw [ae_iff]
    simpa using GaussianHilbert.euclideanGaussian_no_atom_zero E
  apply (ae_map_iff direction_measurable.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  filter_upwards [hn] with z hz
  exact direction_norm hz

/-- An explicit exponential bound derived from Gaussian linear and radial
concentration. It is valid for every positive threshold and every nonzero test
vector, with no algorithmic assumptions. -/
theorem sphereLaw_linear_tail [Nontrivial E] (y : E) (hy : y ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    (sphereLaw E).real {z | a ≤ |⟪y,z⟫_ℝ|} ≤
      Real.exp (-(Module.finrank ℝ E : ℝ)/16) +
      2 * Real.exp (-(Module.finrank ℝ E : ℝ)*a^2/(4*‖y‖^2)) := by
  let m : ℝ := Module.finrank ℝ E
  let μ := GaussianHilbert.euclideanGaussianLaw E
  have hm : 0 < m := Nat.cast_pos.mpr Module.finrank_pos
  have hq : 0 < Real.sqrt (m/2) := Real.sqrt_pos.mpr (by positivity)
  have hq2 : Real.sqrt (m/2)^2 = m/2 := Real.sq_sqrt (by positivity)
  have hmeas : MeasurableSet {z : E | a ≤ |⟪y,z⟫_ℝ|} := by
    apply measurableSet_le measurable_const
    fun_prop
  rw [measureReal_def, sphereLaw, Measure.map_apply direction_measurable hmeas]
  let lower : Set E := {z | ‖z‖^2 ≤ m/2}
  let linear : Set E := {z | a*Real.sqrt (m/2) ≤ |⟪y,z⟫_ℝ|}
  have hsub : direction ⁻¹' {z : E | a ≤ |⟪y,z⟫_ℝ|} ⊆ lower ∪ linear := by
    intro z hz
    by_cases hl : z ∈ lower
    · exact Or.inl hl
    · right
      have hlarge : m/2 < ‖z‖^2 := lt_of_not_ge hl
      have hnorm : 0 < ‖z‖ := by nlinarith [norm_nonneg z]
      have hqnorm : Real.sqrt (m/2) ≤ ‖z‖ := by nlinarith [norm_nonneg z]
      change a ≤ |⟪y, direction z⟫_ℝ| at hz
      simp only [direction, inner_smul_right, abs_mul, abs_inv, abs_norm] at hz
      have hmul : a*‖z‖ ≤ |⟪y,z⟫_ℝ| :=
        (le_div_iff₀ hnorm).mp (by simpa only [div_eq_mul_inv, mul_comm] using hz)
      exact (mul_le_mul_of_nonneg_left hqnorm ha.le).trans hmul
  have hlow : μ.real lower ≤ Real.exp (-m/16) := by
    have h := GaussianHilbert.norm_square_lower_tail E (by norm_num : (0:ℝ)<1/2)
    convert h using 1 <;> simp [lower, μ, m] <;> ring_nf
  have hlin : μ.real linear ≤ 2*Real.exp (-m*a^2/(4*‖y‖^2)) := by
    have h := GaussianHilbert.euclideanGaussian_inner_two_sided E y hy (mul_pos ha hq)
    convert h using 1
    rw [mul_pow, hq2]
    congr 2
    ring
  calc
    _ ≤ μ.real (lower ∪ linear) := measureReal_mono hsub
    _ ≤ μ.real lower + μ.real linear := measureReal_union_le _ _
    _ ≤ _ := add_le_add hlow hlin

end
end GradientHessian.SphereGaussian
