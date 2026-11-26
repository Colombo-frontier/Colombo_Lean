import Bilevel.ProjectionGeometry

/-! Deterministic transport-observer linear algebra on actual subspaces.
The angle premise is a bound on the old-space projection, not a supplied
energy-update conclusion. Conditional Haar/protocol arguments must establish
that premise separately. No interchange of conditionings is made here. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open ProjectionGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem project_add (W : Submodule ℝ E) (u v : E) :
    project W (u+v) = project W u+project W v := by
  exact congrArg Subtype.val (map_add W.orthogonalProjection u v)

theorem project_sub (W : Submodule ℝ E) (u v : E) :
    project W (u-v) = project W u-project W v := by
  exact congrArg Subtype.val (map_sub W.orthogonalProjection u v)

theorem project_self (W : Submodule ℝ E) {u : E} (hu : u ∈ W) : project W u = u :=
  congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self (⟨u,hu⟩ : W))

theorem project_nested {W T : Submodule ℝ E} (hWT : W ≤ T) (u : E) :
    project W (project T u) = project W u :=
  congrArg Subtype.val (Submodule.orthogonalProjection_orthogonalProjection_of_le hWT u)

theorem project_self_adjoint (W : Submodule ℝ E) (u v : E) :
    ⟪u,project W v⟫ = ⟪project W u,v⟫ :=
  (inner_project W u v).trans (project_inner W u v).symm

theorem inner_project_mem (W : Submodule ℝ E) (u v : E) (hv : v ∈ W) :
    ⟪u,v⟫ = ⟪project W u,v⟫ := by
  have hh := Submodule.orthogonalProjection_inner_eq_zero u v hv
  change ⟪u-project W u,v⟫ = 0 at hh
  rw [inner_sub_left] at hh
  linarith

theorem energy_nested_difference {W T : Submodule ℝ E} (hWT : W ≤ T) (z : E) :
    energy T z-energy W z = ‖project T z-project W z‖^2 := by
  have hh : ⟪project T z,project W z⟫ = ‖project W z‖^2 := by
    rw [inner_project,project_nested hWT,real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real,hh]
  unfold energy
  ring

/-- A genuine projection-angle bound gives a lower singular-value bound on
the innovation of every vector in the transported input subspace. -/
theorem innovation_lower_bound (W R : Submodule ℝ E)
    (hangle : ∀ v ∈ R, ‖project W v‖ ≤ ‖v‖/2) (v : E) (hv : v ∈ R) :
    ‖v‖/2 ≤ ‖residual W v‖ := by
  have ht : ‖v‖ ≤ ‖residual W v‖+‖project W v‖ := by
    have hh := norm_add_le (residual W v) (project W v)
    simpa only [ProjectionGeometry.residual,sub_add_cancel] using hh
  linarith [hangle v hv]

/-- Pointwise frame-energy increment after adding an entire transported
subspace. The proof uses the actual orthogonal residual projection. -/
theorem energy_add_subspace (W R : Submodule ℝ E)
    (hangle : ∀ v ∈ R, ‖project W v‖ ≤ ‖v‖/2) (z : E) :
    energy (W ⊔ R) z-energy W z ≤ 8*(energy R z+energy W z) := by
  let p := project (W ⊔ R) z-project W z
  have hpT : p ∈ W ⊔ R := (W ⊔ R).sub_mem (project_mem _ _)
    ((show W ≤ W ⊔ R from le_sup_left) (project_mem W z))
  have hp0 : project W p = 0 := by
    dsimp [p]
    rw [project_sub,project_nested le_sup_left,project_self W (project_mem W z),sub_self]
  obtain ⟨w,hw,v,hv,hp⟩ := Submodule.mem_sup.mp hpT
  have hpv : p = residual W v := by
    have hh := congrArg (project W) hp
    rw [project_add,project_self W hw,hp0] at hh
    dsimp [ProjectionGeometry.residual]
    rw [← hp]
    have hw' : w = -project W v := eq_neg_of_add_eq_zero_left hh
    rw [hw']
    abel
  have hvnorm : ‖v‖ ≤ 2*‖p‖ := by
    have hh := innovation_lower_bound W R hangle v hv
    rw [← hpv] at hh
    linarith
  have henergy : energy (W ⊔ R) z-energy W z = ‖p‖^2 :=
    energy_nested_difference le_sup_left z
  have hinner : ⟪z,p⟫ = ‖p‖^2 := by
    have hT := inner_project (W ⊔ R) z z
    have hW := inner_project W z z
    rw [real_inner_self_eq_norm_sq] at hT hW
    dsimp [p]
    rw [inner_sub_right,hT,hW]
    exact henergy
  have hbound : ‖p‖^2 ≤ (‖project R z‖+‖project W z‖)*‖v‖ := by
    rw [← hinner,hpv,ProjectionGeometry.residual,inner_sub_right,inner_project_mem R z v hv,project_self_adjoint]
    have h1 := real_inner_le_norm (project R z) v
    have h2 := neg_le_abs ⟪project W z,v⟫
    have h3 := abs_real_inner_le_norm (project W z) v
    nlinarith
  have hpbound : ‖p‖ ≤ 2*(‖project R z‖+‖project W z‖) := by
    have hh := mul_le_mul_of_nonneg_left hvnorm
      (add_nonneg (norm_nonneg (project R z)) (norm_nonneg (project W z)))
    by_cases hpz : ‖p‖ = 0
    · rw [hpz]
      positivity
    · have hpp : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpz)
      nlinarith
  rw [henergy]
  unfold energy
  have hs := (sq_le_sq₀ (norm_nonneg p) (by positivity : 0 ≤ 2*(‖project R z‖+‖project W z‖))).mpr hpbound
  nlinarith [sq_nonneg (‖project R z‖-‖project W z‖)]

def frameEnergy {ι : Type*} (W : Submodule ℝ E) (V : ι → E) (I : Finset ι) : ℝ :=
  ∑ i ∈ I, energy W (V i)

theorem frameEnergy_nonneg {ι : Type*} (W : Submodule ℝ E) (V : ι → E) (I : Finset ι) :
    0 ≤ frameEnergy W V I := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The coefficient-eight frame update, before specializing transported
source energy to its bound e. -/
theorem frameEnergy_add_subspace {ι : Type*} (W R : Submodule ℝ E)
    (hangle : ∀ v ∈ R, ‖project W v‖ ≤ ‖v‖/2) (V : ι → E) (I : Finset ι) :
    frameEnergy (W ⊔ R) V I-frameEnergy W V I ≤
      8*(frameEnergy R V I+frameEnergy W V I) := by
  have hh := Finset.sum_le_sum (s := I) (fun i _ => energy_add_subspace W R hangle (V i))
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,frameEnergy] using hh

theorem named_column_energy {ι : Type*} (W : Submodule ℝ E) (V : ι → E) (I : Finset ι)
    (v : E) (hv : ‖v‖ = 1) {e : ℝ} (he0 : 0 ≤ e) (he : e < 1/2)
    (hp : energy W v ≤ e) (horth : ∀ i ∈ I, ⟪V i,v⟫ = 0) :
    frameEnergy (W ⊔ Submodule.span ℝ {v}) V I ≤ (1+2*e)*frameEnergy W V I := by
  have hproj : energy W v < 1 := by linarith
  have hden : 0 < 1-energy W v := by linarith
  have hfactor : 1/(1-energy W v) ≤ 1+2*e := by
    apply (div_le_iff₀ hden).mpr
    have hh := mul_nonneg he0 (show 0 ≤ 1-2*energy W v by linarith)
    nlinarith
  have hh := Finset.sum_le_sum (s := I) (fun i hi =>
    (projection_revelation_bound W (V i) v hv hproj (horth i hi)).trans
      (show energy W (V i)/(1-energy W v) ≤ (1+2*e)*energy W (V i) from by
        have hm := mul_le_mul_of_nonneg_right hfactor (sq_nonneg ‖project W (V i)‖)
        simpa only [div_mul_eq_mul_div,one_mul,mul_comm] using hm))
  simpa only [← Finset.mul_sum,frameEnergy] using hh

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem small_energy_angle_constant {e : ℝ} (hsmall : e ≤ (1:ℝ)/4096) :
    Real.sqrt e+2*e+1/8 < 1/2 := by
  have hs : Real.sqrt e ≤ (1:ℝ)/64 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num; linarith)
  linarith

end Bilevel.TransportObserver
