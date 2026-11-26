import Bilevel.TransportGeneratorStore

/-! A measurable finite-generator controller store. The projector is rebuilt
from the declared finite family; ambient-coordinate columns are never used as
transport probes. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportGeneratorStore
open EuclideanGaussian ProjectionGeometry

def projector (D : ℕ) : {m : ℕ} → (Fin m → Space D) → ProjectionStore.Store D
  | 0, _ => ProjectionStore.ofSubspace D ⊥
  | m+1, v => ProjectionStore.insert D (projector D (fun i : Fin m => v i.succ)) (v 0)

theorem projector_correct (D m : ℕ) (v : Fin m → Space D) :
    projector D v = ProjectionStore.ofSubspace D (span v) := by
  induction m with
  | zero =>
    have he : Set.range v = ∅ := by ext x; simp
    simp [projector,span,he]
  | succ m ih =>
    have hv : v = Fin.cons (v 0) (fun i : Fin m => v i.succ) := by
      ext i; cases i using Fin.cases <;> rfl
    have he : span v = span (fun i : Fin m => v i.succ) ⊔ Submodule.span ℝ {v 0} := by
      conv_lhs => rw [hv,span_cons]
    rw [projector,ih,ProjectionStore.insert_subspace,he]

theorem projector_measurable (D m : ℕ) :
    Measurable (fun v : Fin m → Space D => projector D v) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    exact ProjectionStore.insert_measurable D _
      (ih.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ))) _
      (measurable_pi_apply 0)

def fromGenerators {D m : ℕ} (v : Fin m → Space D) : State D m := (projector D v,v)

theorem fromGenerators_consistent {D m : ℕ} (v : Fin m → Space D) :
    Consistent (fromGenerators v) := projector_correct D m v

theorem fromGenerators_measurable (D m : ℕ) :
    Measurable (fromGenerators : (Fin m → Space D) → State D m) :=
  (projector_measurable D m).prodMk measurable_id

theorem span_append {D m k : ℕ} (v : Fin m → Space D) (w : Fin k → Space D) :
    span (Fin.append v w) = span v ⊔ span w := by
  have he : Set.range (Fin.append v w) = Set.range v ∪ Set.range w := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      refine Fin.addCases ?_ ?_ i
      · intro j
        exact Or.inl ⟨j,Fin.append_left v w j |>.symm⟩
      · intro j
        exact Or.inr ⟨j,Fin.append_right v w j |>.symm⟩
    · rintro (⟨i,rfl⟩ | ⟨i,rfl⟩)
      · exact ⟨Fin.castAdd k i,Fin.append_left v w i⟩
      · exact ⟨Fin.natAdd m i,Fin.append_right v w i⟩
  rw [span,he,Submodule.span_union]
  rfl

theorem append_measurable (D m k : ℕ) :
    Measurable (fun p : (Fin m → Space D) × (Fin k → Space D) => Fin.append p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left]
    exact (measurable_pi_apply j).comp measurable_fst
  · intro j
    simp only [Fin.append_right]
    exact (measurable_pi_apply j).comp measurable_snd

end Bilevel.TransportGeneratorStore
