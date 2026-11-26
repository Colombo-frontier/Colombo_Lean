import Bilevel.ChiCanonicalSourceCertificate
import Bilevel.ChiVirtualUpperProjection
import Bilevel.ChiFiniteVirtualJointReply

/-! The actual old-store upper reply, derived from the finite same-query
energy event. The macro chain and release correction cancel jointly, even
at zero successful lower-oracle coins. -/
noncomputable section
open scoped Topology
set_option maxHeartbeats 1200000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry ChiExtension

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

local notation "Cts" => sourceCounts macroN cn ratios resolutions
local notation "M" => sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km
local notation "G" => sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR
local notation "st" => sourceCanonicalState macroN J dim cn ratios resolutions hdim hAll a initial weight A Kminus ζ CR Km

theorem sourceCanonical_upper_germ_from_energy
    (hJ : 0<J) (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v)
    (q s : ℕ) (V : Submodule ℝ (EuclideanGaussian.Space dim))
    (p : PartialLegendre.FullNormalVariables (EuclideanGaussian.Space dim)
      (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))
    (hp : ∀ k,originalVectors p k∈V)
    (hE : ∀ i : FrameIndex Cts J,GenieProtocol.BoundedEnergy
      (sharedKnown Cts J dim q (columns hAll a) V)
      (prefixSet (retained Cts J q i)) (columns hAll a i)
        (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km
          (ZeroChainSchedule.width c (G J []).width v (ZeroChainSchedule.levels v))))
    (ν ρ R : ℝ) :
    upperBase (J+1) M ν G J ρ R =ᶠ[𝓝 (ChiUpper.baseProjection p)]
      stateUpperBase (J+1) M ν G J ρ R (finiteMacroCounter Cts J) (canonicalCounter Cts J) (st q) := by
  let τ := ZeroChainSchedule.width c (G J []).width v (ZeroChainSchedule.levels v)
  let W := sharedKnown Cts J dim q (columns hAll a) V
  have geo := sourceCanonical_geometry macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have widths := sourceCanonical_finest_geometry macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km hl hw hr hη hη1 c v hc hcs hv
  have loc := sourceCanonical_locality_from_energy macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q V τ widths.1 hE
  have qi := sourceCanonical_query_inclusion macroN J dim cn ratios resolutions hAll a q s V p hp
  have bk := sourceCanonical_bookkeeping macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km q
  change upperBase (J+1) M ν G J ρ R =ᶠ[𝓝 (ChiUpper.baseProjection p)]
    virtualUpperBase (J+1) M ν G J ρ R (counter Cts (J+1) q 0 []) (canonicalCounter Cts J q)
      (st q).2.1 (st q).2.2
  apply actual_upperBase_eventuallyEq_virtual (δ:=τ/16) (J+1) M ν G J hJ ρ R
    (counter Cts (J+1) q 0 []) (canonicalCounter Cts J q) (st q).2.1 (st q).2.2
    (sourceCanonicalState_macro_prefix macroN J dim cn ratios resolutions hdim hAll a initial weight A Kminus ζ CR Km q)
    (sourceCanonicalState_inner_prefix macroN J dim cn ratios resolutions hdim hAll a initial weight A Kminus ζ CR Km q)
    geo.1 (fun j I _ => (geo.2.2.1 j I).1)
    (fun j I _ => (geo.2.2.1 j I).2.2.2.1) (fun j I _ => (geo.2.2.1 j I).2.2.2.2)
    bk.2.2.1 (bk.2.2.2.1 0 hJ) (ChiUpper.baseProjection p)
  · intro k hk
    have hb := ((M).coordinate_projection_bound geo.2.1 W ⟨p.fst.fst,qi.1⟩ k).trans (loc.2.1 k hk)
    change |(M).coordinates p.fst.fst k|≤3*(M).width/16
    linarith [geo.1]
  · intro j I hj k hk
    have hjm : j<J+1 := by omega
    have hb := ((G j I).coordinate_projection_bound (geo.2.2.1 j I).2.1 W
      ⟨p.snd.fst ⟨j,hjm⟩,qi.2 ⟨j,hjm⟩⟩ k).trans (loc.2.2.1 j I hj k hk)
    change |(G j I).coordinates (block (J+1) j p.snd.fst) k|≤3*(G j I).width/16
    rw [block,dif_pos hjm,PiLp.proj_apply]
    linarith [(geo.2.2.1 j I).1]
  · exact geo.2.1
  · exact fun j I _ => (geo.2.2.1 j I).2.1
  · exact widths.2.2.2.1
  · exact widths.2.2.2.2.1
  · exact widths.2.2.2.2.2

end Bilevel.ChiHierarchyHaar
