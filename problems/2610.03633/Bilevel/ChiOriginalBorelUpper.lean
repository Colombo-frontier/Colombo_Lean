import Bilevel.ChiOriginalPotential

/-! The original upper response is jointly Borel, including the nonlinear
macro, release correction, selected carrier, and public bowl. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension ChiUpper PartialLegendre
variable {E F A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem stateUpperBase_full_frame (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ)
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F) (a : A) :
    stateUpperBase m M ν D d ρ R (fun _ => M.n+1) (fun _ => fullCounts D)
      (fullFrameState M D UM U a)=
    upperBase m (reframeNode M (UM a)) ν (reframeGeometry D (U a)) d ρ R := by
  rw [← stateUpperBase_reframe m M (UM a) ν D (U a)]
  funext z
  exact virtualUpperBase_full m (reframeNode M (UM a)) ν (reframeGeometry D (U a)) d ρ R z

theorem complete_upper_reply_eq_original (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (s : ℕ) (b : Normals s)
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F) (a : A)
    (q : FullNormalVariables E (Blocks m F) (Normals s)) :
    virtualUpperGradient m M ν D d ρ R (fun _ => M.n+1) (fun _ => fullCounts D) s b
      (fullFrameState M D UM U a,q)=
    gradient (fullUpper (upperBase m (reframeNode M (UM a)) ν (reframeGeometry D (U a)) d ρ R) b) q := by
  apply virtualUpperGradient_eq_original
  · exact (upperBase_contDiff m (reframeNode M (UM a)) ν (reframeGeometry D (U a)) d ρ R).differentiable (by norm_num)
  · rw [stateUpperBase_full_frame]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace A]

theorem original_upper_reply_measurable (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (s : ℕ)
    [MeasurableSpace (Joint E (Blocks m F))] [BorelSpace (Joint E (Blocks m F))]
    [MeasurableSpace (FullNormalVariables E (Blocks m F) (Normals s))]
    [BorelSpace (FullNormalVariables E (Blocks m F) (Normals s))]
    (b : Normals s) (UM : A → Space M.n →ₗᵢ[ℝ] E)
    (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F) (hdata : Measurable (frameData M D UM U)) :
    Measurable (fun p : A × FullNormalVariables E (Blocks m F) (Normals s) =>
      gradient (fullUpper (upperBase m (reframeNode M (UM p.1)) ν
        (reframeGeometry D (U p.1)) d ρ R) b) p.2) := by
  have hstate := fullFrameState_measurable M D UM U hdata
  have harg : Measurable (fun p : A × FullNormalVariables E (Blocks m F) (Normals s) =>
      (fullFrameState M D UM U p.1,p.2)) := (hstate.comp measurable_fst).prodMk measurable_snd
  have hm := (virtualUpperGradient_measurable m M ν D d ρ R (fun _ => M.n+1)
    (fun _ => fullCounts D) s b).comp harg
  convert hm using 1
  funext p
  exact (complete_upper_reply_eq_original m M ν D d ρ R s b UM U p.1 p.2).symm

end Bilevel.ChiPrefixEvaluation
