import GradientHessian.HierarchyParameters

/-! The canonical finite product measurable structure on hierarchy
coefficients agrees with the Borel structure of its normed product. -/

noncomputable section
namespace GradientHessian.HierarchyParameters
universe u
variable (Y E : Type u) (H : ℕ → Type u) (m : ℕ)
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [MeasurableSpace Y] [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

def parameterMeasurable : (t : ℕ) → MeasurableSpace (Parameters Y E H m t)
  | 0 => by
    letI : MeasurableSpace (Y →L[ℝ] Y) := borel _
    exact inferInstanceAs (MeasurableSpace ((Fin 8 → Leaf.MatrixMarks Y E (m+1)) ×
      (Fin 8 → Fin (FirstHeight.depth (m+1)+2) → E)))
  | t+1 => by
    letI := parameterMeasurable t
    exact inferInstanceAs (MeasurableSpace ((Fin 8 → Parameters Y E H m t) × (Fin 8 → H t)))
attribute [instance] parameterMeasurable

variable [BorelSpace Y] [BorelSpace E] [∀ t, BorelSpace (H t)]
  [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E] [∀ t, FiniteDimensional ℝ (H t)]

def parameterBorel : (t : ℕ) → BorelSpace (Parameters Y E H m t)
  | 0 => by
    letI : MeasurableSpace (Y →L[ℝ] Y) := borel _
    letI : BorelSpace (Y →L[ℝ] Y) := ⟨rfl⟩
    haveI : BorelSpace (Leaf.Marks Y E (m+1)) := inferInstance
    haveI : BorelSpace (Leaf.MatrixMarks Y E (m+1)) := inferInstance
    haveI : BorelSpace (Fin 8 → Leaf.MatrixMarks Y E (m+1)) := inferInstance
    haveI : BorelSpace (Fin 8 → Fin (FirstHeight.depth (m+1)+2) → E) := inferInstance
    exact inferInstanceAs (BorelSpace ((Fin 8 → Leaf.MatrixMarks Y E (m+1)) ×
      (Fin 8 → Fin (FirstHeight.depth (m+1)+2) → E)))
  | t+1 => by
    letI := parameterBorel t
    exact inferInstanceAs (BorelSpace ((Fin 8 → Parameters Y E H m t) × (Fin 8 → H t)))
attribute [instance] parameterBorel

end GradientHessian.HierarchyParameters
