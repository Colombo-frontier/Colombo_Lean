import GradientHessian.GaussianCone
import GradientHessian.SphereGaussian

/-! Small support of a Euclidean ball on the actual uniform sphere law.
The Gaussian cone argument avoids an unproved surface-area formula. -/

namespace GradientHessian.SphereSmallBall
open MeasureTheory ProbabilityTheory GaussianHilbert GaussianSquare SphereGaussian
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def cone (u : E) (ρ : ℝ) : Set E := {z | (1-ρ^2)*‖z‖^2≤⟪u,z⟫_ℝ^2}

omit [FiniteDimensional ℝ E] in
theorem cone_measurable (u : E) (ρ : ℝ) : MeasurableSet (cone u ρ) := by
  apply measurableSet_le <;> fun_prop

theorem cone_rotation (u v : E) (huv : ‖u‖=‖v‖) (ρ : ℝ) :
    (euclideanGaussianLaw E).real (cone u ρ)=(euclideanGaussianLaw E).real (cone v ρ) := by
  let U : E ≃ₗᵢ[ℝ] E := (Submodule.span ℝ {u-v})ᗮ.reflection
  have hU : U u=v := Submodule.reflection_sub huv
  have hmap := congrArg (fun μ : Measure E => μ.real (cone v ρ)) (euclideanGaussian_isometry E U)
  dsimp only at hmap
  simp only [measureReal_def] at hmap
  rw [Measure.map_apply U.continuous.measurable (cone_measurable v ρ)] at hmap
  have he : U ⁻¹' cone v ρ=cone u ρ := by
    ext z
    simp only [cone,Set.mem_preimage,Set.mem_setOf_eq,U.norm_map]
    rw [←hU,U.inner_map_map]
  rw [he] at hmap
  exact hmap

theorem gaussian_cone_bound [Nontrivial E] (u : E) (hu : ‖u‖=1)
    {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) :
    (euclideanGaussianLaw E).real (cone u ρ)≤2*(2*ρ)^(Module.finrank ℝ E-1) := by
  let i₀ : Fin (Module.finrank ℝ E) := ⟨0,Module.finrank_pos⟩
  let e := stdOrthonormalBasis ℝ E i₀
  have he : ‖e‖=1 := (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i₀
  rw [cone_rotation u e (hu.trans he.symm)]
  rw [measureReal_def,euclideanGaussianLaw,
    Measure.map_apply (gaussianSynthesis_continuous E).measurable (cone_measurable e ρ)]
  have hset : gaussianSynthesis E ⁻¹' cone e ρ=
      {z : Fin (Module.finrank ℝ E) → ℝ | (1-ρ^2)*energy z≤(z i₀)^2} := by
    ext z
    simp only [cone,Set.mem_preimage,Set.mem_setOf_eq,gaussianSynthesis_norm_square]
    rw [gaussianSynthesis_coordinate]
  rw [hset]
  exact GaussianCone.coordinate_cone_bound i₀ hρ hρ1

theorem sphere_cone_bound [Nontrivial E] (u : E) (hu : ‖u‖=1)
    {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) :
    (sphereLaw E).real {z | 1-ρ^2≤⟪u,z⟫_ℝ^2}≤2*(2*ρ)^(Module.finrank ℝ E-1) := by
  have hm : MeasurableSet {z : E | 1-ρ^2≤⟪u,z⟫_ℝ^2} := by
    apply measurableSet_le measurable_const
    fun_prop
  rw [measureReal_def,sphereLaw,Measure.map_apply direction_measurable hm]
  have hsub : direction ⁻¹' {z : E | 1-ρ^2≤⟪u,z⟫_ℝ^2} ⊆ cone u ρ := by
    intro z hz
    change 1-ρ^2≤⟪u,direction z⟫_ℝ^2 at hz
    by_cases hn : z=0
    · subst z
      simp [direction,abs_of_pos hρ] at hz
      have hp : 0<1-ρ^2 := by nlinarith
      linarith
    · have hnpos : 0<‖z‖ := norm_pos_iff.mpr hn
      simp only [direction,inner_smul_right,mul_pow,inv_pow] at hz
      have hmul := mul_le_mul_of_nonneg_left hz (sq_nonneg ‖z‖)
      have he : ‖z‖^2*((‖z‖^2)⁻¹*⟪u,z⟫_ℝ^2)=⟪u,z⟫_ℝ^2 := by field_simp
      rw [he] at hmul
      change (1-ρ^2)*‖z‖^2≤⟪u,z⟫_ℝ^2
      nlinarith
  exact (measureReal_mono hsub).trans (gaussian_cone_bound u hu hρ hρ1)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem ball_implies_cone (u v : E) (hu : u≠0) (hv : ‖v‖=1) {R ε : ℝ}
    (hR : 0<R) (_hε : 0≤ε) (hball : ‖u-R•v‖≤ε) :
    1-(ε/R)^2≤⟪direction u,v⟫_ℝ^2 := by
  have hn : 0<‖u‖ := norm_pos_iff.mpr hu
  have hnorm := norm_sub_sq_real u (R•v)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hv,mul_one,inner_smul_right] at hnorm
  have hsq : ‖u-R•v‖^2≤ε^2 := pow_le_pow_left₀ (norm_nonneg _) hball 2
  have hinner : ⟪u,v⟫_ℝ=‖u‖*⟪direction u,v⟫_ℝ := by
    simp only [direction,real_inner_smul_left]
    field_simp
  rw [hinner] at hnorm
  have hperp := sq_nonneg (‖u‖-R*⟪direction u,v⟫_ℝ)
  have hmul : (R:ℝ)^2*(1-⟪direction u,v⟫_ℝ^2)≤ε^2 := by nlinarith
  have hR2 : 0<R^2 := sq_pos_of_pos hR
  have hdiv := (le_div_iff₀ hR2).mpr (by nlinarith : (1-⟪direction u,v⟫_ℝ^2)*R^2≤ε^2)
  rw [←div_pow] at hdiv
  linarith

theorem positive_radius_small_ball [Nontrivial E] (u : E) {R ε : ℝ}
    (hR : 0<R) (hε : 0<ε) (hεR : ε<R) :
    (sphereLaw E).real {v | ‖u-R•v‖≤ε}≤2*(2*ε/R)^(Module.finrank ℝ E-1) := by
  by_cases hu : u=0
  · have hzero : (sphereLaw E).real {v | ‖u-R•v‖≤ε}=0 := by
      apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr
      have he : ∀ᵐ v ∂sphereLaw E,¬(‖u-R•v‖≤ε) := by
        filter_upwards [sphereLaw_unit (E := E)] with v hv
        simp only [hu,zero_sub,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hv,mul_one]
        exact not_le.mpr hεR
      simpa only [not_not] using ae_iff.mp he
    rw [hzero]
    positivity
  · have hsub : ∀ᵐ v ∂sphereLaw E, v ∈ {v : E | ‖u-R•v‖≤ε} →
        v ∈ {v | 1-(ε/R)^2≤⟪direction u,v⟫_ℝ^2} := by
      filter_upwards [sphereLaw_unit (E := E)] with v hv
      exact ball_implies_cone u v hu hv hR hε.le
    have hmono : (sphereLaw E).real {v | ‖u-R•v‖≤ε} ≤
        (sphereLaw E).real {v | 1-(ε/R)^2≤⟪direction u,v⟫_ℝ^2} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    have h := hmono.trans
      (sphere_cone_bound (direction u) (direction_norm hu) (div_pos hε hR)
        ((div_lt_one hR).mpr hεR))
    convert h using 1
    ring

theorem zero_radius_small_ball (hdim : 2≤Module.finrank ℝ E) (u : E) {R : ℝ} (hR : 0<R) :
    (sphereLaw E).real {v | ‖u-R•v‖≤0}=0 := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank ℝ E)
  apply le_antisymm ?_ measureReal_nonneg
  apply le_of_forall_pos_le_add
  intro η hη
  let ρ : ℝ := min (1/4) (η/8)
  have hρ : 0<ρ := lt_min (by norm_num) (by positivity)
  have hρ4 : ρ≤1/4 := min_le_left _ _
  have hρη : ρ≤η/8 := min_le_right _ _
  have hρ1 : ρ<1 := by linarith
  have he := positive_radius_small_ball u hR (mul_pos hR hρ)
    (show R*ρ<R by nlinarith)
  have hsub : {v : E | ‖u-R•v‖≤0}⊆{v | ‖u-R•v‖≤R*ρ} := by
    intro v hv
    exact hv.trans (mul_pos hR hρ).le
  have hb : (sphereLaw E).real {v | ‖u-R•v‖≤0}≤2*(2*ρ)^(Module.finrank ℝ E-1) := by
    have heq : 2*(R*ρ)/R=2*ρ := by field_simp; ring
    rw [heq] at he
    exact (measureReal_mono hsub).trans he
  have hp : (2*ρ)^(Module.finrank ℝ E-1)≤2*ρ := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by positivity : 0≤2*ρ)
      (by linarith : 2*ρ≤1) (by omega : 1≤Module.finrank ℝ E-1)
  linarith

/-- Source small-ball estimate for all nonnegative support widths, including
the zero-width endpoint. The positive source radius is explicit. -/
theorem small_support (hdim : 2≤Module.finrank ℝ E) (u : E) {R w : ℝ}
    (hR : 0<R) (hw : 0≤w) (hRw : 16*w≤R) :
    (sphereLaw E).real {v | ‖u-R•v‖≤3*w}≤2*(6*w/R)^(Module.finrank ℝ E-1) := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank ℝ E)
  by_cases hw0 : w=0
  · simp only [hw0,mul_zero,zero_div]
    rw [zero_radius_small_ball hdim u hR]
    positivity
  · have hwp : 0<w := lt_of_le_of_ne hw (Ne.symm hw0)
    have he := positive_radius_small_ball u hR (show 0<3*w by positivity) (show 3*w<R by linarith)
    convert he using 1
    ring

theorem manuscript_small_ball {p : ℕ} (hp : 2≤p) (u : EuclideanSpace ℝ (Fin p)) {R w : ℝ}
    (hR : 0<R) (hw : 0≤w) (hRw : 16*w≤R) :
    (sphereLaw (EuclideanSpace ℝ (Fin p))).real {v | ‖u-R•v‖≤3*w}≤2*(6*w/R)^(p-1) := by
  simpa using small_support (E := EuclideanSpace ℝ (Fin p)) (by simpa using hp) u hR hw hRw

end
end GradientHessian.SphereSmallBall
