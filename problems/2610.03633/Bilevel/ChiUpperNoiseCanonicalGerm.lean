import Bilevel.ChiUpperNoiseCanonicalProjection
import Bilevel.ChiUpperNoisePrefixGerm
import Bilevel.ChiUpperNoiseVirtualEvaluator

/-! Both direct upper-noise scalar germs from the same finite precoin
energy event. The current coin controls only the next retained prefix. -/
noncomputable section
set_option maxHeartbeats 600000
open scoped Topology
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
  (q : ℕ) (V : Submodule ℝ (EuclideanGaussian.Space dim))
  (p : Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
  (hp : ∀ k,upperNoiseVectors p k∈V)
  (hE : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,GenieProtocol.BoundedEnergy
    (sharedKnown (sourceCounts macroN cn ratios resolutions) 0 dim q (columns hAll a) V)
    (prefixSet (retained (sourceCounts macroN cn ratios resolutions) 0 q i)) (columns hAll a i)
      (sourcePublicCap macroN 0 sc ratios resolutions weight CR ζ Km (((sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) 0 []).width/2)))

include hl hw hr hη hη1 hweight hζ hCR hKm hp hE

theorem sourceCanonical_upperNoise_inactive_germ (ν : ℝ) (ρ R : ℕ → ℝ) :
    fullInactiveCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R =ᶠ[𝓝 p]
      stateDirectInactive 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R (finiteMacroCounter (sourceCounts macroN cn ratios resolutions) 0) (canonicalCounter (sourceCounts macroN cn ratios resolutions) 0) ((sourceCanonicalState macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km) q) := by
  have geo := sourceCanonical_geometry macroN 0 dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have proj := sourceCanonical_upperNoise_projection macroN dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q V p hp hE
  have bk := sourceCanonical_bookkeeping macroN 0 dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km q
  have hlocal := direct_inactive_core_eventuallyEq_virtual 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R
    (counter (sourceCounts macroN cn ratios resolutions) 1 q 0 []) (canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 q) ((sourceCanonicalState macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km) q).2.1 ((sourceCanonicalState macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km) q).2.2
    (sourceCanonicalState_macro_prefix macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km q)
    (sourceCanonicalState_inner_prefix macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km q 0)
    geo.1 (fun I => (geo.2.2.1 0 I).1)
    (fun I => (geo.2.2.1 0 I).2.2.2.1) (fun I => (geo.2.2.1 0 I).2.2.2.2)
    (geo.2.2.2 0) bk.2.2.1 (queryProjection p) proj.1 proj.2 geo.2.1
    (fun I => (geo.2.2.1 0 I).2.1) (min (((sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km)).width/16) (((sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) 0 []).width/32))
    (lt_min (div_pos geo.1 (by norm_num)) (div_pos (geo.2.2.1 0 []).1 (by norm_num)))
    (min_le_left _ _) (min_le_right _ _)
  exact hlocal.comp_tendsto (queryProjection (E:=EuclideanGaussian.Space dim)
    (U:=Blocks 1 (EuclideanGaussian.Space dim))).continuous.continuousAt

theorem sourceCanonical_upperNoise_active_germ (ν : ℝ) (ρ R : ℕ → ℝ) :
    fullCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R =ᶠ[𝓝 p]
      stateDirectCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R (finiteMacroCounter (sourceCounts macroN cn ratios resolutions) 0) (canonicalCounter (sourceCounts macroN cn ratios resolutions) 0) ((sourceCanonicalState macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km) (q+1)) := by
  have geo := sourceCanonical_geometry macroN 0 dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have proj := sourceCanonical_upperNoise_projection macroN dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q V p hp hE
  have bk := sourceCanonical_bookkeeping macroN 0 dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km q
  have bkn := sourceCanonical_bookkeeping macroN 0 dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km (q+1)
  have hb : ∀ I,∀ k : Fin (((sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) 0 I).n+1),canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 q 0 I≤k.val →
      |((sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) 0 I).coordinates (block 1 0 p.snd) k|≤3*((sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) 0 I).width/16 := by
    intro I k hk
    have h := proj.2 I k hk
    rw [geo.2.2.2 0 I]
    linarith [(geo.2.2.1 0 []).1]
  have hlocal := direct_core_eventuallyEq_virtual 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R
    (counter (sourceCounts macroN cn ratios resolutions) 1 q 0 []) (counter (sourceCounts macroN cn ratios resolutions) 1 (q+1) 0 [])
    (canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 q) (canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 (q+1)) ((sourceCanonicalState macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km) (q+1)).2.1 ((sourceCanonicalState macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km) (q+1)).2.2
    (sourceCanonicalState_macro_prefix macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km (q+1))
    (sourceCanonicalState_inner_prefix macroN 0 dim cn ratios resolutions hdim hAll a sc weight A Kminus ζ CR Km (q+1) 0)
    bk.1 (fun I => bk.2.1 0 I) geo.1 (fun I => (geo.2.2.1 0 I).1)
    (fun I => (geo.2.2.1 0 I).2.2.2.1) (fun I => (geo.2.2.1 0 I).2.2.2.2)
    bkn.2.2.1 bk.2.2.2.2 (queryProjection p) proj.1 hb geo.2.1
    (fun I => (geo.2.2.1 0 I).2.1) (min (((sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km)).width/16) (((sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) 0 []).width/32))
    (lt_min (div_pos geo.1 (by norm_num)) (div_pos (geo.2.2.1 0 []).1 (by norm_num)))
    (min_le_left _ _) (by
      intro I
      apply (min_le_right _ _).trans
      rw [geo.2.2.2 0 I]
      linarith [(geo.2.2.1 0 []).1])
  exact hlocal.comp_tendsto (queryProjection (E:=EuclideanGaussian.Space dim)
    (U:=Blocks 1 (EuclideanGaussian.Space dim))).continuous.continuousAt

end Bilevel.ChiHierarchyHaar

