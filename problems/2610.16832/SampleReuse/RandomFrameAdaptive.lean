import SampleReuse.RandomFrameSphere
import RandomizedFO2003.ResidualRotation

/-! Haar stabilizer averaging gives the hidden-column tail for every measurable
query depending only on exposed columns. The residual uniformity is derived
from Haar invariance, rather than supplied as a conditional-law assumption. -/

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory RandomizedFO2003 Rotations
open scoped InnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem residual_projection_identity (L : Submodule ℝ E) (U : Rotation E)
    (V : Rotation Lᗮ) (e : Lᗮ) (x : E) :
    ⟪x, isometry E (U * extendComplement L V) e⟫_ℝ =
      ⟪Lᗮ.orthogonalProjection ((isometry E U).symm x), isometry Lᗮ V e⟫_ℝ := by
  rw [isometry_mul, extendComplement_on_orthogonal,
    Submodule.inner_orthogonalProjection_eq_of_mem_right]
  have hi := (isometry E U).inner_map_map ((isometry E U).symm x)
    (isometry Lᗮ V e : E)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hi

/-- A bounded measurable query invariant under rotations fixing the revealed
subspace has the sharp exponential projection tail for each hidden unit vector.
This applies to an arbitrary query/output function of the revealed frame. -/
theorem invariant_query_projection_tail (L : Submodule ℝ E) (e : Lᗮ)
    (he : ‖e‖ = 1) (Q : Rotation E → E) (hQ : Measurable Q)
    (hknown : ∀ U V, Q (U * extendComplement L V) = Q U)
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (hbound : ∀ U, ‖Q U‖ ≤ R) :
    (haarLaw E).real {U | t ≤ |⟪Q U, isometry E U e⟫_ℝ|} ≤
      2 * Real.exp (-(Module.finrank ℝ Lᗮ : ℝ) * t ^ 2 / (2 * R ^ 2)) := by
  haveI : Nontrivial Lᗮ := ⟨⟨e, 0, by intro hz; simp [hz] at he⟩⟩
  let B : ℝ := 2 * Real.exp (-(Module.finrank ℝ Lᗮ : ℝ) * t ^ 2 / (2 * R ^ 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let s : Set (Rotation E) := {U | t ≤ |⟪Q U, isometry E U e⟫_ℝ|}
  have hs : MeasurableSet s := by
    apply measurableSet_le measurable_const
    exact ((continuous_fst.inner continuous_snd).measurable.comp
      (hQ.prodMk (measurable_orbit E e))).abs
  let f : Rotation E × Rotation Lᗮ → Rotation E :=
    fun p => p.1 * extendComplement L p.2
  have hf : Measurable f :=
    (continuous_fst.mul ((continuous_extendComplement L).comp continuous_snd)).measurable
  have hprod : ((haarLaw E).prod (haarLaw Lᗮ)) (f ⁻¹' s) = haarLaw E s := by
    rw [Measure.prod_apply_symm (hf hs)]
    calc
      _ = ∫⁻ _V : Rotation Lᗮ, haarLaw E s ∂haarLaw Lᗮ := by
        apply lintegral_congr
        intro V
        exact (haar_right E (extendComplement L V)).measure_preimage hs.nullMeasurableSet
      _ = _ := by simp
  have hfiber (U : Rotation E) :
      haarLaw Lᗮ ((fun V => f (U, V)) ⁻¹' s) ≤ ENNReal.ofReal B := by
    let y := Lᗮ.orthogonalProjection ((isometry E U).symm (Q U))
    have hy : ‖y‖ ≤ R := by
      calc
        ‖y‖ ≤ 1 * ‖(isometry E U).symm (Q U)‖ :=
          Lᗮ.orthogonalProjection.le_of_opNorm_le Lᗮ.orthogonalProjection_norm_le _
        _ ≤ R := by simpa only [one_mul, LinearIsometryEquiv.norm_map] using hbound U
    have htai := haar_projection_tail e y he hR ht hy
    have heq : ((fun V => f (U, V)) ⁻¹' s) =
        {V : Rotation Lᗮ | t ≤ |⟪y, isometry Lᗮ V e⟫_ℝ|} := by
      ext V
      simp only [Set.mem_preimage, Set.mem_setOf_eq, s, f, hknown,
        residual_projection_identity, y]
    rw [heq]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).mpr htai
  have hmeasure : haarLaw E s ≤ ENNReal.ofReal B := by
    rw [← hprod, Measure.prod_apply (hf hs)]
    calc
      _ ≤ ∫⁻ _U : Rotation E, ENNReal.ofReal B ∂haarLaw E := lintegral_mono hfiber
      _ = _ := by simp
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).mp hmeasure

end SampleReuse.RandomFrame
