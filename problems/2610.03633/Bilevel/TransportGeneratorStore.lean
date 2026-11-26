import Bilevel.ProjectionStore
import Bilevel.ProjectionQuery
import Mathlib.Data.Fin.Tuple.Basic

/-! A Borel projector store with a fixed finite vector generator family.
Transporting the generators gives the whole-space action, while the number of
probes is independent of the ambient dimension. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportGeneratorStore
open EuclideanGaussian ProjectionGeometry

abbrev State (D m : ℕ) := ProjectionStore.Store D × (Fin m → Space D)

def span {D m : ℕ} (v : Fin m → Space D) : Submodule ℝ (Space D) :=
  Submodule.span ℝ (Set.range v)

def Consistent {D m : ℕ} (s : State D m) : Prop := s.1 = ProjectionStore.ofSubspace D (span s.2)

def empty (D : ℕ) : State D 0 := (ProjectionStore.ofSubspace D ⊥,Fin.elim0)

def insert {D m : ℕ} (s : State D m) (q : Space D) : State D (m+1) :=
  (ProjectionStore.insert D s.1 q,Fin.cons q s.2)

theorem span_cons {D m : ℕ} (v : Fin m → Space D) (q : Space D) :
    span (Fin.cons q v) = span v ⊔ Submodule.span ℝ {q} := by
  rw [span,Fin.range_cons,Submodule.span_insert]
  exact sup_comm _ _

theorem empty_consistent (D : ℕ) : Consistent (empty D) := by
  have he : Set.range (Fin.elim0 : Fin 0 → Space D) = ∅ := by ext x; simp
  simp only [Consistent,empty,span,he,Submodule.span_empty]

theorem insert_consistent {D m : ℕ} (s : State D m) (hs : Consistent s) (q : Space D) :
    Consistent (insert s q) := by
  change ProjectionStore.insert D s.1 q = ProjectionStore.ofSubspace D (span (Fin.cons q s.2))
  rw [hs,span_cons,ProjectionStore.insert_subspace]

theorem generator_mem {D m : ℕ} (v : Fin m → Space D) (i : Fin m) : v i ∈ span v :=
  Submodule.subset_span ⟨i,rfl⟩

theorem span_rank_le {D m : ℕ} (v : Fin m → Space D) : Module.finrank ℝ (span v) ≤ m := by
  induction m with
  | zero =>
    have he : Set.range v = ∅ := by ext x; simp
    simp [span,he]
  | succ m ih =>
    have hv : v = Fin.cons (v 0) (fun i : Fin m => v i.succ) := by ext i; cases i using Fin.cases <;> rfl
    rw [hv,span_cons]
    exact (ProjectionQuery.finrank_insert_le _ _).trans (Nat.add_le_add_right (ih _) 1)

theorem insert_measurable (D m : ℕ) :
    Measurable (fun p : State D m × Space D => insert p.1 p.2) := by
  apply Measurable.prodMk
  · exact ProjectionStore.insert_measurable D _ (measurable_fst.comp measurable_fst) _ measurable_snd
  · apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => exact measurable_snd
    | succ i => exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)

theorem residual_measurable (D m : ℕ) :
    Measurable (fun p : State D m × Space D => ProjectionStore.residual D p.1.1 p.2) :=
  ProjectionStore.residual_measurable D _ (measurable_fst.comp measurable_fst) _ measurable_snd

theorem direction_measurable (D m : ℕ) :
    Measurable (fun p : State D m × Space D => ProjectionStore.direction D p.1.1 p.2) :=
  ProjectionStore.direction_measurable D _ (measurable_fst.comp measurable_fst) _ measurable_snd

theorem residual_correct {D m : ℕ} (s : State D m) (hs : Consistent s) (q : Space D) :
    ProjectionStore.residual D s.1 q = ProjectionGeometry.residual (span s.2) q := by
  rw [hs,ProjectionStore.residual_subspace]

theorem direction_correct {D m : ℕ} (s : State D m) (hs : Consistent s) (q : Space D) :
    ProjectionStore.direction D s.1 q = revelationDirection (span s.2) q := by
  rw [hs,ProjectionStore.direction_subspace]

theorem transported_span {D m : ℕ} (v : Fin m → Space D) (O : Space D ≃ₗᵢ[ℝ] Space D) :
    span (fun i => O (v i)) = (span v).map O.toLinearEquiv.toLinearMap := by
  rw [span,span,Submodule.map_span]
  congr 1
  exact Set.range_comp O v

end Bilevel.TransportGeneratorStore
