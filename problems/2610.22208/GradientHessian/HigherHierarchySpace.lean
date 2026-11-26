import GradientHessian.HigherHierarchyCoordinates

/-! The finite physical prefix at auxiliary height t (source height t+1).
Each new height has its own Hilbert space H t, allowing heterogeneous
dimensions, and all child nodes use the same lower prefix. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u

variable (Y E : Type u) (H : ℕ → Type u) (m : ℕ)
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Space : ℕ → Type u
  | 0 => FirstHeight.SourceSpace Y E m
  | t + 1 => Layer (Space t) (H t)

variable [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def spaceNormed : (t : ℕ) → NormedAddCommGroup (Space Y E H m t)
  | 0 => inferInstanceAs (NormedAddCommGroup (FirstHeight.SourceSpace Y E m))
  | t + 1 => by
    letI := spaceNormed t
    exact inferInstanceAs (NormedAddCommGroup (Layer (Space Y E H m t) (H t)))
attribute [instance] spaceNormed

def spaceInnerProduct : (t : ℕ) → InnerProductSpace ℝ (Space Y E H m t)
  | 0 => inferInstanceAs (InnerProductSpace ℝ (FirstHeight.SourceSpace Y E m))
  | t + 1 => by
    letI := spaceInnerProduct t
    exact inferInstanceAs (InnerProductSpace ℝ (Layer (Space Y E H m t) (H t)))
attribute [instance] spaceInnerProduct

abbrev spaceNormedSpace (t : ℕ) : NormedSpace ℝ (Space Y E H m t) :=
  (spaceInnerProduct Y E H m t).toNormedSpace

variable [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)]

def spaceComplete : (t : ℕ) → CompleteSpace (Space Y E H m t)
  | 0 => inferInstanceAs (CompleteSpace (FirstHeight.SourceSpace Y E m))
  | t + 1 => by
    letI := spaceComplete t
    exact inferInstanceAs (CompleteSpace (Layer (Space Y E H m t) (H t)))
attribute [instance] spaceComplete

end GradientHessian.HigherHierarchy
