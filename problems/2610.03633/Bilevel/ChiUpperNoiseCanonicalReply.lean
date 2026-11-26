import Bilevel.ChiUpperNoiseCanonicalGerm
import Bilevel.ChiUpperNoiseSourceResponse
import Bilevel.ChiCanonicalSourceReframe

/-! Exact direct upper-noise original SFO pair from the actual finite
same-query energy event. The evaluator uses a fixed public template. -/
noncomputable section
set_option maxHeartbeats 700000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry ChiUpperNoise

variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim)
  (sc : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)


variable (hl : 0<sc.curvature) (hw : 0<sc.width)
  (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
  (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
  (q : ℕ) (p : Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
  (hE : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,GenieProtocol.BoundedEnergy
    (sharedKnown (sourceCounts macroN cn ratios resolutions) 0 dim q (columns hAll a) (Submodule.span ℝ (Set.range (upperNoiseVectors p))))
    (prefixSet (retained (sourceCounts macroN cn ratios resolutions) 0 q i)) (columns hAll a i)
      (sourcePublicCap macroN 0 sc ratios resolutions weight CR ζ Km (((sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) 0 []).width/2)))

include hl hw hr hη hη1 hweight hζ hCR hKm hE

theorem sourceCanonical_upperNoise_reply_from_energy (ν : ℝ) (ρ R : ℕ → ℝ)
    (g : Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)) → ℝ)
    (π : ℝ) (coin : Bool) :
    finiteDirectEvaluate (sourceCounts macroN cn ratios resolutions) 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) rfl (fun _ _ => rfl) ρ R g π p
      (actual (sourceCounts macroN cn ratios resolutions) 0 q (columns hAll a)) (actual (sourceCounts macroN cn ratios resolutions) 0 (q+if coin then 1 else 0) (columns hAll a)) coin=
      sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
        ν ρ R g π a p coin := by
  let V := Submodule.span ℝ (Set.range (upperNoiseVectors p))
  have hp : ∀ k,upperNoiseVectors p k∈V := fun k => Submodule.subset_span ⟨k,rfl⟩
  change twoStorePair
    (stateDirectCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R (finiteMacroCounter (sourceCounts macroN cn ratios resolutions) 0) (canonicalCounter (sourceCounts macroN cn ratios resolutions) 0))
    (stateDirectInactive 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R (finiteMacroCounter (sourceCounts macroN cn ratios resolutions) 0) (canonicalCounter (sourceCounts macroN cn ratios resolutions) 0))
    g π p ((sourceCanonicalState macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km) q) ((sourceCanonicalState macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km) (q+if coin then 1 else 0)) coin=
      (ChiConservative.sampleGradient (fullCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R) (fullInactiveCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R) π coin p,gradient g p)
  apply twoStorePair_eq_original
  · exact (sourceCanonical_upperNoise_inactive_germ macroN dim cn ratios resolutions hdim hAll a sc weight
      A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q V p hp hE ν ρ R).symm
  · intro hc
    subst coin
    exact (sourceCanonical_upperNoise_active_germ macroN dim cn ratios resolutions hdim hAll a sc weight
      A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q V p hp hE ν ρ R).symm

theorem sourceCanonical_upperNoise_template_reply_from_energy
    (a₀ : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim) (ν : ℝ) (ρ R : ℕ → ℝ)
    (g : Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)) → ℝ)
    (π : ℝ) (coin : Bool) :
    finiteDirectEvaluate (sourceCounts macroN cn ratios resolutions) 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a₀ sc Km) ν
      (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a₀ sc weight A Kminus ζ CR)
      rfl (fun _ _ => rfl) ρ R g π p (actual (sourceCounts macroN cn ratios resolutions) 0 q (columns hAll a))
      (actual (sourceCounts macroN cn ratios resolutions) 0 (q+if coin then 1 else 0) (columns hAll a)) coin=
      sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
        ν ρ R g π a p coin := by
  have h := sourceCanonical_upperNoise_reply_from_energy macroN dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q p hE ν ρ R g π coin
  have he := finiteDirectEvaluate_reframe (sourceCounts macroN cn ratios resolutions) 1
    (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a₀ sc Km) ν
    (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a₀ sc weight A Kminus ζ CR)
    rfl (fun _ _ => rfl) (frame hAll a (Sum.inl ())) (canonicalFamily hdim a)
    ρ R g π p (actual (sourceCounts macroN cn ratios resolutions) 0 q (columns hAll a))
    (actual (sourceCounts macroN cn ratios resolutions) 0 (q+if coin then 1 else 0) (columns hAll a)) coin
  exact he.symm.trans h

end Bilevel.ChiHierarchyHaar

