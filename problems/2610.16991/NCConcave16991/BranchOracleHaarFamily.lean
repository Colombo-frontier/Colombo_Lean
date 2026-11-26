import NCConcave16991.MixedHaarNativeCoordinates
import NCConcave16991.MixedHaarVertexInitial
import NCConcave16991.MixedHaarWordRank
import NCConcave16991.MixedHaarTapeWordReservoir
import NCConcave16991.BranchOracleRequest
import NCConcave16991.BranchOracleBorel
import NCConcave16991.BranchOracleProblem

/-! # The actual finite static Haar family at the public branch dimensions -/

noncomputable section

open MeasureTheory

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean MixedHaar

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

variable (n M m D : ℕ)

abbrev HaarVertexSpace (t : Vertex M m) := FormalLayer (ι := Fin n) (Space D) t.val
abbrev HaarVertexDimension (t : Vertex M m) := Module.finrank ℝ (HaarVertexSpace n M m D t)
abbrev HaarParameter := NativeOrthogonal (HaarVertexSpace n M m D)

def staticHaarLaw : Measure (HaarParameter n M m D) := vertexHaarLaw (HaarVertexDimension n M m D)

instance staticHaarLaw_probability : IsProbabilityMeasure (staticHaarLaw n M m D) := by
  unfold staticHaarLaw
  infer_instance

def haarRotations (θ : HaarParameter n M m D) (t : ℕ) :
    FormalLayer (ι := Fin n) (Space D) t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) (Space D) t :=
  if ht : t < M * (m + 1) + 1 then
    nativeVertexOperator (HaarVertexSpace n M m D) θ ⟨t,ht⟩
  else LinearIsometryEquiv.refl ℝ _

theorem haarRotations_vertex (θ : HaarParameter n M m D) (t : Vertex M m) :
    haarRotations n M m D θ t.val = nativeVertexOperator (HaarVertexSpace n M m D) θ t := by
  unfold haarRotations
  rw [dif_pos t.isLt]

theorem haarRotations_forward_measurable (t : Vertex M m) : Measurable
    (fun p : HaarParameter n M m D × HaarVertexSpace n M m D t ↦ haarRotations n M m D p.1 t.val p.2) := by
  simp_rw [haarRotations_vertex]
  exact nativeVertexOperator_action_measurable (HaarVertexSpace n M m D) t

theorem haarRotations_inverse_measurable (t : Vertex M m) : Measurable
    (fun p : HaarParameter n M m D × HaarVertexSpace n M m D t ↦ (haarRotations n M m D p.1 t.val).symm p.2) := by
  simp_rw [haarRotations_vertex]
  exact nativeVertexOperator_inverse_measurable (HaarVertexSpace n M m D) t

theorem initial_staticHaar_preserving :
    MeasurePreserving (vertexFrameComplete (HaarVertexDimension n M m D)
      (initialVertexFrame (HaarVertexDimension n M m D)))
      (vertexFrameTapeLaw (HaarVertexDimension n M m D)) (staticHaarLaw n M m D) :=
  initial_vertexFrameComplete_preserving _

theorem haarGaussian_coordinates_preserving :
    MeasurePreserving (fun g : GaussianVertexBlock n (M * (m + 1)) D ↦
      fun t : Vertex M m ↦ nativeCoordinates (HaarVertexSpace n M m D) t (g t))
      (gaussianVertexLaw n (M * (m + 1)) D)
      (Measure.pi (fun t : Vertex M m ↦ ProbabilityTheory.stdGaussian
        (EuclideanSpace ℝ (Fin (HaarVertexDimension n M m D t))))) :=
  nativeGaussian_coordinates_preserving (HaarVertexSpace n M m D)

def haarSource (hD : 0 < D) : Space D := Haar.basisVector ⟨0,hD⟩

theorem haarSource_unit (hD : 0 < D) : ‖haarSource D hD‖ = 1 := by
  simp [haarSource,Haar.basisVector]

def haarPaperProblem (hn : 0 < n) (hM : 0 < M) (hD : 0 < D) (θ : HaarParameter n M m D) :
    Problem (paperParameters n hn M hM m) (primalDimension (MacroSpaces (ι := Fin n) (Space D) M m))
      (dualDimension (MacroSpaces (ι := Fin n) (Space D) M m))
      (paperDualDomain (MacroSpaces (ι := Fin n) (Space D) M m) hn) :=
  staticPaperProblem (Space D) hn hM (haarRotations n M m D θ) (haarSource D hD) (haarSource_unit D hD)

theorem haarPaperProblem_individualSmooth (hn : 0 < n) (hM : 0 < M) (hD : 0 < D)
    (θ : HaarParameter n M m D) : (haarPaperProblem n M m D hn hM hD θ).individualSmooth :=
  staticPaperProblem_individualSmooth (Space D) hn hM (haarRotations n M m D θ)
    (haarSource D hD) (haarSource_unit D hD)

theorem haarPaperProblem_initial (hn : 0 < n) (hM : 0 < M) (hD : 0 < D)
    (θ : HaarParameter n M m D) : (haarPaperProblem n M m D hn hM hD θ).initialPoint = 0 := rfl

end NCConcave16991.BranchOracle
