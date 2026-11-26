import GradientHessian.HigherHierarchyFunctions
import GradientHessian.LeafJointOracle

/-! A normed product of actual finite hierarchy coefficients. Readout
assembly into this space is measurable; physical jets are continuous here. -/

noncomputable section
namespace GradientHessian.HierarchyParameters
universe u
open HigherHierarchy

variable (Y E : Type u) (H : ℕ → Type u) (m : ℕ)
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Parameters : ℕ → Type u
  | 0 => (Fin 8 → Leaf.MatrixMarks Y E (m+1)) × (Fin 8 → Fin (FirstHeight.depth (m+1)+2) → E)
  | t+1 => (Fin 8 → Parameters t) × (Fin 8 → H t)

variable [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def parameterNormed : (t : ℕ) → NormedAddCommGroup (Parameters Y E H m t)
  | 0 => inferInstanceAs (NormedAddCommGroup ((Fin 8 → Leaf.MatrixMarks Y E (m+1)) ×
      (Fin 8 → Fin (FirstHeight.depth (m+1)+2) → E)))
  | t+1 => by
    letI := parameterNormed t
    exact inferInstanceAs (NormedAddCommGroup ((Fin 8 → Parameters Y E H m t) × (Fin 8 → H t)))
attribute [instance] parameterNormed

def parameterNormedSpace : (t : ℕ) → NormedSpace ℝ (Parameters Y E H m t)
  | 0 => inferInstanceAs (NormedSpace ℝ ((Fin 8 → Leaf.MatrixMarks Y E (m+1)) ×
      (Fin 8 → Fin (FirstHeight.depth (m+1)+2) → E)))
  | t+1 => by
    letI := parameterNormedSpace t
    exact inferInstanceAs (NormedSpace ℝ ((Fin 8 → Parameters Y E H m t) × (Fin 8 → H t)))
attribute [instance] parameterNormedSpace

variable {Y E H m}

def decode : (t : ℕ) → Parameters Y E H m t → Data Y E H m t
  | 0, p => {
      A := fun i => (p.1 i).1
      b := fun i => (p.1 i).2.1
      a := fun i => (p.1 i).2.2.1
      innerDirections := fun i => (p.1 i).2.2.2
      outerDirections := p.2 }
  | t+1, p => ⟨fun i => decode t (p.1 i), p.2⟩

def scalarJoint (K : ℝ) (t : ℕ) (p : Parameters Y E H m t × Space Y E H m t) : ℝ :=
  scalar K t (decode t p.1) p.2
def outgoingJoint (K : ℝ) (t : ℕ) (p : Parameters Y E H m t × Space Y E H m t) : ℝ :=
  outgoing K t (decode t p.1) p.2

variable [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E] [∀ t, FiniteDimensional ℝ (H t)]

def parameterFiniteDimensional : (t : ℕ) → FiniteDimensional ℝ (Parameters Y E H m t)
  | 0 => inferInstanceAs (FiniteDimensional ℝ ((Fin 8 → Leaf.MatrixMarks Y E (m+1)) ×
      (Fin 8 → Fin (FirstHeight.depth (m+1)+2) → E)))
  | t+1 => by
    letI := parameterFiniteDimensional t
    exact inferInstanceAs (FiniteDimensional ℝ ((Fin 8 → Parameters Y E H m t) × (Fin 8 → H t)))
attribute [instance] parameterFiniteDimensional

end GradientHessian.HierarchyParameters
