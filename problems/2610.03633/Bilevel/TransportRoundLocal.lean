import Bilevel.TransportObserverBlock

/-! Actual local source spaces for a frozen bidirectional edge batch. The
reverse innovation is taken after enlarging the paired range by the forward
action, and lies in that edge's local updated destination space. -/
noncomputable section
namespace Bilevel.TransportRound
open ProjectionGeometry TransportObserver
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def residualMap (A : Submodule ℝ E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E-A.subtypeL.comp A.orthogonalProjection

theorem residualMap_apply (A : Submodule ℝ E) (x : E) :
    residualMap A x = ProjectionGeometry.residual A x := rfl

def residualSpace (A S : Submodule ℝ E) : Submodule ℝ E := S.map (residualMap A).toLinearMap

theorem residualSpace_perp (A S : Submodule ℝ E) : residualSpace A S ≤ Aᗮ := by
  rintro x ⟨y,hy,rfl⟩
  exact Submodule.sub_orthogonalProjection_mem_orthogonal y

theorem residualSpace_local {A S L : Submodule ℝ E} (hA : A ≤ L) (hS : S ≤ L) :
    residualSpace A S ≤ L := by
  rintro x ⟨y,hy,rfl⟩
  exact L.sub_mem (hS hy) (hA (project_mem A y))

theorem sup_residualSpace (A S : Submodule ℝ E) : A ⊔ residualSpace A S = A ⊔ S := by
  apply le_antisymm
  · exact sup_le le_sup_left (residualSpace_local le_sup_left le_sup_right)
  · apply sup_le le_sup_left
    intro x hx
    have hr : residualMap A x ∈ residualSpace A S := ⟨x,hx,rfl⟩
    have hp := (A ⊔ residualSpace A S).add_mem
      ((show A ≤ _ from le_sup_left) (project_mem A x))
      ((show residualSpace A S ≤ _ from le_sup_right) hr)
    simpa only [residualMap_apply,ProjectionGeometry.residual,add_sub_cancel] using hp

theorem transported_residual_merge (O : E ≃ₗᵢ[ℝ] E) (A S W : Submodule ℝ E)
    (hAW : A.map O.toLinearEquiv.toLinearMap ≤ W) :
    W ⊔ (residualSpace A S).map O.toLinearEquiv.toLinearMap = W ⊔ S.map O.toLinearEquiv.toLinearMap := by
  have hh := congrArg (fun R : Submodule ℝ E => R.map O.toLinearEquiv.toLinearMap) (sup_residualSpace A S)
  simp only [Submodule.map_sup] at hh
  have hw := congrArg (fun R : Submodule ℝ E => W ⊔ R) hh
  simpa only [← sup_assoc,sup_eq_left.mpr hAW] using hw

def localSource (S K : Submodule ℝ E) : Submodule ℝ E := S ⊔ K

def localDestination (O : E ≃ₗᵢ[ℝ] E) (S T K : Submodule ℝ E) : Submodule ℝ E :=
  T ⊔ K.map O.toLinearEquiv.toLinearMap ⊔ S.map O.toLinearEquiv.toLinearMap

def pairedForward (A S : Submodule ℝ E) : Submodule ℝ E := A ⊔ S

theorem forward_residual_local (A S K : Submodule ℝ E) (hA : A ≤ S ⊔ K) :
    residualSpace A S ≤ localSource S K := residualSpace_local hA le_sup_left

theorem reverse_residual_local (O : E ≃ₗᵢ[ℝ] E) (A S T K : Submodule ℝ E)
    (hA : A ≤ S ⊔ K) :
    residualSpace ((pairedForward A S).map O.toLinearEquiv.toLinearMap) T ≤ localDestination O S T K := by
  apply residualSpace_local
  · have hh : pairedForward A S ≤ S ⊔ K := sup_le hA le_sup_left
    apply (Submodule.map_mono hh).trans
    rw [Submodule.map_sup]
    exact sup_le le_sup_right (le_trans le_sup_right le_sup_left)
  · exact le_trans le_sup_left le_sup_left

theorem forward_local_energy {ι : Type*} (O : E ≃ₗᵢ[ℝ] E) (A S T K : Submodule ℝ E)
    (hA : A ≤ S ⊔ K) (hAT : A.map O.toLinearEquiv.toLinearMap ≤ T ⊔ K.map O.toLinearEquiv.toLinearMap)
    (V : ι → E) (I : Finset ι) {e : ℝ} (he : frameEnergy (localSource S K) V I ≤ e)
    (hang : ∀ x ∈ (residualSpace A S).map O.toLinearEquiv.toLinearMap,
      ‖project (T ⊔ K.map O.toLinearEquiv.toLinearMap) x‖ ≤ ‖x‖/2) :
    frameEnergy (localDestination O S T K) (fun i => O (V i)) I ≤
      8*e+9*frameEnergy (T ⊔ K.map O.toLinearEquiv.toLinearMap) (fun i => O (V i)) I := by
  have hh := transported_frame_energy_update O (T ⊔ K.map O.toLinearEquiv.toLinearMap)
    (residualSpace A S) (localSource S K) (forward_residual_local A S K hA) V I I (fun _ h => h) he hang
  rw [transported_residual_merge O A S _ hAT] at hh
  dsimp [localDestination]
  linarith

theorem reverse_local_energy {ι : Type*} (O : E ≃ₗᵢ[ℝ] E) (A S T K W : Submodule ℝ E)
    (hA : A ≤ S ⊔ K)
    (hBW : ((pairedForward A S).map O.toLinearEquiv.toLinearMap).map O.symm.toLinearEquiv.toLinearMap ≤ W)
    (V : ι → E) (I : Finset ι) {e : ℝ}
    (he : frameEnergy (localDestination O S T K) V I ≤ e)
    (hang : ∀ x ∈ (residualSpace ((pairedForward A S).map O.toLinearEquiv.toLinearMap) T).map
      O.symm.toLinearEquiv.toLinearMap, ‖project W x‖ ≤ ‖x‖/2) :
    frameEnergy (W ⊔ T.map O.symm.toLinearEquiv.toLinearMap) (fun i => O.symm (V i)) I ≤
      8*e+9*frameEnergy W (fun i => O.symm (V i)) I := by
  have hh := transported_frame_energy_update O.symm W
    (residualSpace ((pairedForward A S).map O.toLinearEquiv.toLinearMap) T)
    (localDestination O S T K) (reverse_residual_local O A S T K hA) V I I (fun _ h => h) he hang
  rw [transported_residual_merge O.symm _ T W hBW] at hh
  linarith

end Bilevel.TransportRound
