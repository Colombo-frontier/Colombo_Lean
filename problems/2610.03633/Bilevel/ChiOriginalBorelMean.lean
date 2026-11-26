import Bilevel.ChiFullDisclosureObjective
import Bilevel.ChiCanonicalSourceData

/-! Joint Borel mean-gradient loss for the actual frame-indexed objective.
The formula is explicit and does not refer to a chosen Primitive witness. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E F A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def frameData (M : Node E) (D : Geometry F)
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (a : A) : HierarchyData M D :=
  ((fun k => UM a (basis k)),fun j I k => U a j I (basis k))

theorem virtualJointOuter_frame_eq (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ)
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (a : A) (z : Joint E (Blocks m F)) :
    virtualJointOuter m M ν D ρ R d K (M.n+1) (fullCounts D)
      (frameData M D UM U a).1 (frameData M D UM U a).2 z=
      jointOuter m (reframeNode M (UM a)) ν (reframeGeometry D (U a)) ρ R d K z := by
  rw [← virtualJointOuter_reframe m M (UM a) ν D (U a)]
  exact virtualJointOuter_full m (reframeNode M (UM a)) ν (reframeGeometry D (U a)) ρ R d K z

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace A]

theorem original_mean_loss_measurable (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ)
    [MeasurableSpace (Joint E (Blocks m F))] [BorelSpace (Joint E (Blocks m F))]
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (hdata : Measurable (frameData M D UM U)) :
    Measurable (fun p : A × Joint E (Blocks m F) =>
      ‖gradient (jointOuter m (reframeNode M (UM p.1)) ν (reframeGeometry D (U p.1)) ρ R d K) p.2‖) := by
  letI : SecondCountableTopology (Blocks m F) := inferInstance
  letI : SecondCountableTopology (Joint E (Blocks m F)) := inferInstance
  letI : BorelSpace (HierarchyData M D) := inferInstance
  letI : SecondCountableTopology (HierarchyData M D) := inferInstance
  have hg := ParametricGradient.gradient_measurable
    (fun a : HierarchyData M D => virtualJointOuter m M ν D ρ R d K (M.n+1) (fullCounts D) a.1 a.2)
    (virtualJointOuter_continuous m M ν D ρ R d K (M.n+1) (fullCounts D))
  have harg : Measurable (fun p : A × Joint E (Blocks m F) => (frameData M D UM U p.1,p.2)) :=
    (hdata.comp measurable_fst).prodMk measurable_snd
  have he := (hg.comp harg).norm
  convert he using 1
  funext p
  congr 1
  exact congrArg (fun f : Joint E (Blocks m F) → ℝ => gradient f p.2)
    (funext (fun z => (virtualJointOuter_frame_eq m M ν D ρ R d K UM U p.1 z).symm))

end Bilevel.ChiPrefixEvaluation
