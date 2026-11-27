import Nonsmooth.GaussianPolytopeCuts
import Nonsmooth.GaussianPriorIdentity
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite affine geometry and a positive Gaussian conditioning event. The
coordinate space may shrink after a winner observation. -/
structure GaussianPolytopeModel where
  Space : Type
  [spaceNorm : NormedAddCommGroup Space]
  [spaceInner : InnerProductSpace ℝ Space]
  [spaceMeasurable : MeasurableSpace Space]
  [spaceBorel : BorelSpace Space]
  [spaceFinite : FiniteDimensional ℝ Space]
  [spaceNontrivial : Nontrivial Space]
  Index : Type
  [indexFinite : Fintype Index]
  embedding : Space →ₗᵢ[ℝ] E
  origin : E
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  normal : Index → Space
  bound : Index → ℝ
  positive : euclideanGaussianLaw Space (gaussianBallPolytope radius normal bound) ≠ 0

attribute [instance] GaussianPolytopeModel.spaceNorm GaussianPolytopeModel.spaceInner
  GaussianPolytopeModel.spaceMeasurable GaussianPolytopeModel.spaceBorel
  GaussianPolytopeModel.spaceFinite GaussianPolytopeModel.spaceNontrivial
  GaussianPolytopeModel.indexFinite

variable {E} [MeasurableSpace E] [BorelSpace E]

def gaussianPolytopeModelMap (s : ℝ) (M : GaussianPolytopeModel E) (z : M.Space) : E :=
  M.origin + s • M.embedding z

theorem gaussianPolytopeModelMap_measurable (s : ℝ) (M : GaussianPolytopeModel E) :
    Measurable (gaussianPolytopeModelMap s M) :=
  (continuous_const.add (continuous_const.smul M.embedding.continuous)).measurable

def gaussianPolytopeModelLaw (s : ℝ) (M : GaussianPolytopeModel E) : Measure E :=
  ((euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]).map
    (gaussianPolytopeModelMap s M)

instance gaussianPolytopeModelLaw_probability (s : ℝ) (M : GaussianPolytopeModel E) :
    IsProbabilityMeasure (gaussianPolytopeModelLaw s M) := by
  letI := cond_isProbabilityMeasure M.positive
  exact Measure.isProbabilityMeasure_map (gaussianPolytopeModelMap_measurable s M).aemeasurable

/-- A posterior row is either fully determined or has a concrete affine
Gaussian ball-polytope representation at the original common scale. -/
def GaussianPolytopeRow (s : ℝ) (ν : Measure E) : Prop :=
  (∃ x : E, ν = Measure.dirac x) ∨ ∃ M : GaussianPolytopeModel E, ν = gaussianPolytopeModelLaw s M

variable [FiniteDimensional ℝ E] [Nontrivial E]

def gaussianPolytopeInitialModel : GaussianPolytopeModel E where
  Space := E
  Index := Fin 0
  embedding := LinearIsometry.id
  origin := 0
  radius := 2 * Real.sqrt (Module.finrank ℝ E)
  radius_nonneg := by positivity
  normal := Fin.elim0
  bound := Fin.elim0
  positive := by
    simpa [gaussianBallPolytope] using
      (euclideanGaussianLaw_truncation_positive (E := E)).ne'

theorem gaussianPolytopeInitialModel_law (s : ℝ) :
    gaussianPolytopeModelLaw s (gaussianPolytopeInitialModel (E := E)) =
      (truncatedGaussianLaw E).map (fun z : E => s • z) := by
  simp [gaussianPolytopeModelLaw, gaussianPolytopeModelMap, gaussianPolytopeInitialModel,
    gaussianBallPolytope, truncatedGaussianLaw, Set.inter_univ]
  congr 1
  funext z
  simp [gaussianPolytopeModelMap]
  all_goals exact congrArg (fun A : Set E => (euclideanGaussianLaw E)[|A]) (Set.inter_univ _)

theorem gaussianAmbientRow_polytope :
    GaussianPolytopeRow ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹) (gaussianAmbientRowLaw E) := by
  refine Or.inr ⟨gaussianPolytopeInitialModel, ?_⟩
  rw [gaussianPolytopeInitialModel_law]
  exact gaussianSupportRowLaw_map

end
end Nonsmooth
