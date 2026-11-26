import Bilevel.TransportRoundFrameSpace
import Bilevel.TransportControllerFreshStore

/-! Borel projection operations for the concrete monitor subspaces. Ambient
projector columns are used only for analysis of measurability; transport
queries remain the original finite generators with their dimension bounds. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportGeneratorStore ProjectionGeometry OrthogonalAction
set_option maxHeartbeats 800000

theorem projector_columns_span {D : ℕ} (W : Submodule ℝ (Space D)) :
    span (ProjectionStore.ofSubspace D W)=W := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact project_mem W (ProjectionStore.basis D i)
  · intro x hx
    have hs : ProjectionStore.apply D (ProjectionStore.ofSubspace D W) x∈span (ProjectionStore.ofSubspace D W) := by
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (generator_mem _ i)
    rw [ProjectionStore.apply_subspace,TransportObserver.project_self W hx] at hs
    exact hs

theorem span_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {D m : ℕ}
    (v : Ω → Fin m → Space D) (hv : Measurable v) :
    Measurable (fun ω => ProjectionStore.ofSubspace D (span (v ω))) := by
  have he : (fun ω => ProjectionStore.ofSubspace D (span (v ω)))=(fun ω => projector D (v ω)) := by
    funext ω
    exact (projector_correct D m (v ω)).symm
  rw [he]
  exact (projector_measurable D m).comp hv

theorem sup_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ}
    (W V : Ω → Submodule ℝ (Space D))
    (hW : Measurable (fun ω => ProjectionStore.ofSubspace D (W ω)))
    (hV : Measurable (fun ω => ProjectionStore.ofSubspace D (V ω))) :
    Measurable (fun ω => ProjectionStore.ofSubspace D (W ω⊔V ω)) := by
  have he : (fun ω => ProjectionStore.ofSubspace D (W ω⊔V ω))=
      (fun ω => projector D (Fin.append (ProjectionStore.ofSubspace D (W ω)) (ProjectionStore.ofSubspace D (V ω)))) := by
    funext ω
    rw [projector_correct,span_append,projector_columns_span,projector_columns_span]
  rw [he]
  exact (projector_measurable D (D+D)).comp ((append_measurable D D D).comp (hW.prodMk hV))

theorem residualSpace_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ}
    (W V : Ω → Submodule ℝ (Space D))
    (hW : Measurable (fun ω => ProjectionStore.ofSubspace D (W ω)))
    (hV : Measurable (fun ω => ProjectionStore.ofSubspace D (V ω))) :
    Measurable (fun ω => ProjectionStore.ofSubspace D (residualSpace (W ω) (V ω))) := by
  have he : (fun ω => ProjectionStore.ofSubspace D (residualSpace (W ω) (V ω)))=
      (fun ω => projector D (residualFamily (ProjectionStore.ofSubspace D (W ω)) (ProjectionStore.ofSubspace D (V ω)))) := by
    funext ω
    rw [projector_correct,residualFamily_span,projector_columns_span]
  rw [he]
  exact (projector_measurable D D).comp ((residualFamily_measurable D D).comp (hW.prodMk hV))

theorem map_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ}
    (W : Ω → Submodule ℝ (Space D)) (hW : Measurable (fun ω => ProjectionStore.ofSubspace D (W ω)))
    (O : Ω → OrthogonalHaar.Group D) (hO : Measurable O) :
    Measurable (fun ω => ProjectionStore.ofSubspace D ((W ω).map (isometry D (O ω)).toLinearEquiv.toLinearMap)) := by
  have he : (fun ω => ProjectionStore.ofSubspace D ((W ω).map (isometry D (O ω)).toLinearEquiv.toLinearMap))=
      (fun ω => projector D (fun i => O ω • ProjectionStore.ofSubspace D (W ω) i)) := by
    funext ω
    have hs : span (fun i => O ω • ProjectionStore.ofSubspace D (W ω) i)=
        (W ω).map (isometry D (O ω)).toLinearEquiv.toLinearMap := by
      change span (fun i => (isometry D (O ω)) (ProjectionStore.ofSubspace D (W ω) i))=_
      rw [transported_span,projector_columns_span]
    rw [projector_correct,hs]
  rw [he]
  apply (projector_measurable D D).comp
  apply measurable_pi_lambda
  intro i
  exact hO.smul ((measurable_pi_apply i).comp hW)

def protectedGenerators {D T : ℕ} (V : Fin T → Space D) (K : Finset (Fin T)) : Fin T → Space D :=
  fun i => if i∈K then V i else 0

theorem protectedGenerators_span {D T : ℕ} (V : Fin T → Space D) (K : Finset (Fin T)) :
    span (protectedGenerators V K)=protectedSpace V K := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    by_cases hi : i∈K
    · simp only [protectedGenerators,if_pos hi]
      exact protectedSpace_mem V K i hi
    · simp only [protectedGenerators,if_neg hi]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    have hif : i∈K := hi
    have hh := generator_mem (protectedGenerators V K) i
    simpa only [protectedGenerators,if_pos hif] using hh

theorem protectedSpace_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {D T : ℕ}
    (V : Ω → Fin T → Space D) (hV : Measurable V) (K : Finset (Fin T)) :
    Measurable (fun ω => ProjectionStore.ofSubspace D (protectedSpace (V ω) K)) := by
  have hg : Measurable (fun ω => protectedGenerators (V ω) K) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i∈K
    · simpa only [protectedGenerators,if_pos hi] using (measurable_pi_apply i).comp hV
    · simp only [protectedGenerators,if_neg hi]
      exact measurable_const
  have hh := span_projector_measurable _ hg
  simpa only [protectedGenerators_span] using hh

end Bilevel.TransportRound
