import MatchingBounds1005.AccessibleReferenceCompiler

/-! Deterministic calendar conditions are preserved by the accessible compiler. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.AccessibleReferenceCompiler
open ScheduledHaar

universe u
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type u} [MeasurableSpace S]

def ColumnsAt (I : ℕ → Submodule ℝ E) :
    (w : List SourceKind) → Machine (E := E) (S := S) w → ℕ → Prop
  | [], _, _ => True
  | .disclose :: w, M, start => M.1.1 ∈ I start ∧ ColumnsAt I w M.2 start
  | .query :: w, M, start => ColumnsAt I w M.2 (start + 1)
  | .candidate :: w, M, start => ColumnsAt I w M.2 (start + 1)

theorem compile_columnsAt (I : ℕ → Submodule ℝ E) (w : List SourceKind)
    (M : Machine (E := E) (S := S) w) (start : ℕ) (hc : ColumnsAt I w M start)
    {H : Type u} [MeasurableSpace H] (view : H → S) (hv : Measurable view) :
    (compile w M view hv).ColumnsAt I w start := by
  induction w generalizing start H with
  | nil => trivial
  | cons kind w ih =>
      cases kind with
      | disclose => exact ⟨hc.1, ih M.2 start hc.2 _ _⟩
      | query => exact ih M.2 (start + 1) hc _ _
      | candidate => exact ih M.2 (start + 1) hc _ _

end MatchingBounds1005.AccessibleReferenceCompiler
