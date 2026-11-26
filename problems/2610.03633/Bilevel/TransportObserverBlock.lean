import Bilevel.TransportObserverGeometry

/-! The coefficient-eight transport block update in terms of actual source
and destination spaces and an actual orthogonal map. The singular-value
assertion is expressed invariantly as a lower norm bound on the innovation
linear map. Establishing its angle premise probabilistically is separate. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open ProjectionGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem project_norm_mono {R S : Submodule ℝ E} (hRS : R ≤ S) (z : E) :
    ‖project R z‖ ≤ ‖project S z‖ := by
  calc
    ‖project R z‖ = ‖R.orthogonalProjection (project S z)‖ := by rw [← project_nested hRS z]; rfl
    _ ≤ ‖R.orthogonalProjection‖*‖project S z‖ := R.orthogonalProjection.le_opNorm _
    _ ≤ ‖project S z‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right R.orthogonalProjection_norm_le (norm_nonneg _)

theorem frameEnergy_mono {ι : Type*} {R S : Submodule ℝ E} (hRS : R ≤ S)
    (V : ι → E) (I : Finset ι) : frameEnergy R V I ≤ frameEnergy S V I :=
  Finset.sum_le_sum (fun i _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (project_norm_mono hRS (V i)))

theorem frameEnergy_mono_indices {ι : Type*} (W : Submodule ℝ E) (V : ι → E)
    {I J : Finset ι} (hIJ : I ⊆ J) : frameEnergy W V I ≤ frameEnergy W V J :=
  Finset.sum_le_sum_of_subset_of_nonneg hIJ (fun _ _ _ => sq_nonneg _)

theorem energy_transport (O : E ≃ₗᵢ[ℝ] E) (R : Submodule ℝ E) (z : E) :
    energy (R.map O.toLinearEquiv.toLinearMap) (O z) = energy R z := by
  unfold energy project
  rw [Submodule.orthogonalProjection_map_apply]
  simp only [O.symm_apply_apply,O.norm_map]

theorem frameEnergy_transport {ι : Type*} (O : E ≃ₗᵢ[ℝ] E)
    (R : Submodule ℝ E) (V : ι → E) (I : Finset ι) :
    frameEnergy (R.map O.toLinearEquiv.toLinearMap) (fun i => O (V i)) I = frameEnergy R V I := by
  unfold frameEnergy
  apply Finset.sum_congr rfl
  intro i _
  exact energy_transport O R (V i)

/-- The manuscript's energy update for every tracked subset I of the local
unprotected set J. Protected or newly disclosed destination columns need no
energy bound: only the source energy and the angle premise occur here. -/
theorem transported_frame_energy_update {ι : Type*} (O : E ≃ₗᵢ[ℝ] E)
    (W R S : Submodule ℝ E) (hRS : R ≤ S) (V : ι → E) (I J : Finset ι) (hIJ : I ⊆ J)
    {e : ℝ} (hsource : frameEnergy S V J ≤ e)
    (hangle : ∀ v ∈ R.map O.toLinearEquiv.toLinearMap, ‖project W v‖ ≤ ‖v‖/2) :
    frameEnergy (W ⊔ R.map O.toLinearEquiv.toLinearMap) (fun i => O (V i)) I-
      frameEnergy W (fun i => O (V i)) I ≤
        8*(e+frameEnergy W (fun i => O (V i)) I) := by
  have hh := frameEnergy_add_subspace W (R.map O.toLinearEquiv.toLinearMap) hangle (fun i => O (V i)) I
  rw [frameEnergy_transport] at hh
  have hs := (frameEnergy_mono hRS V I).trans ((frameEnergy_mono_indices S V hIJ).trans hsource)
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add_right hs _) (by norm_num))

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def innovationMap (W : Submodule ℝ E) (A : F →ₗᵢ[ℝ] E) : F →L[ℝ] E :=
  A.toContinuousLinearMap-(W.subtypeL.comp W.orthogonalProjection).comp A.toContinuousLinearMap

theorem innovationMap_apply (W : Submodule ℝ E) (A : F →ₗᵢ[ℝ] E) (u : F) :
    innovationMap W A u = ProjectionGeometry.residual W (A u) := rfl

theorem innovation_singular_lower_bound (W : Submodule ℝ E) (A : F →ₗᵢ[ℝ] E)
    (hangle : ∀ u, ‖project W (A u)‖ ≤ ‖u‖/2) (u : F) :
    ‖u‖/2 ≤ ‖innovationMap W A u‖ := by
  have hh : ‖u‖ ≤ ‖innovationMap W A u‖+‖project W (A u)‖ := by
    have ht := norm_add_le (innovationMap W A u) (project W (A u))
    simpa only [innovationMap_apply,ProjectionGeometry.residual,sub_add_cancel,A.norm_map] using ht
  linarith [hangle u]

theorem innovation_injective (W : Submodule ℝ E) (A : F →ₗᵢ[ℝ] E)
    (hangle : ∀ u, ‖project W (A u)‖ ≤ ‖u‖/2) : Function.Injective (innovationMap W A) := by
  intro u v huv
  have hh := innovation_singular_lower_bound W A hangle (u-v)
  rw [map_sub,huv,sub_self,norm_zero] at hh
  have hz : ‖u-v‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end Bilevel.TransportObserver
