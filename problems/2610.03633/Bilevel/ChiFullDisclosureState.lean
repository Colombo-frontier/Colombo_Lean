import Bilevel.ChiOriginalBorelMean

/-! The complete-column state associated with an actual family of frames.
This is a representation of the original instance, not an algorithmic store. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive
variable {E F A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def fullFrameState (M : Node E) (D : Geometry F)
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (a : A) : VirtualState M D := (0,frameData M D UM U a)

theorem frame_columns_gram (n r : ℕ) (U : Space n →ₗᵢ[ℝ] E) :
    PrefixGram n r (fun k => U (basis k)) := by
  intro i j _ _
  simp [U.inner_map_map,basis,EuclideanSpace.inner_single_left,EuclideanSpace.single_apply]

theorem fullFrameState_valid (M : Node E) (D : Geometry F)
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (a : A) : ValidState M D (fun _ => M.n+1) (fun _ => fullCounts D)
      (fullFrameState M D UM U a) :=
  ⟨frame_columns_gram M.n (M.n+1) (UM a),
    fun j I => frame_columns_gram (D j I).n ((D j I).n+1) (U a j I)⟩

variable [MeasurableSpace A] [MeasurableSpace E] [MeasurableSpace F]

theorem fullFrameState_measurable (M : Node E) (D : Geometry F)
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (hdata : Measurable (frameData M D UM U)) :
    Measurable (fullFrameState M D UM U) := measurable_const.prodMk hdata

end Bilevel.ChiPrefixEvaluation
