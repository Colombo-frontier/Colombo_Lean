import Bilevel.ChiCanonicalSourceCertificate
import Bilevel.ChiUpperNoiseQueryVectors

/-! The direct upper-noise source's stronger inactive blind interval is
paid by the same finite frame energy event. All original query blocks are
inserted before the coin; no inverse or response-graph restriction occurs. -/
noncomputable section
set_option maxHeartbeats 400000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry ChiUpperNoise

variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim)
  (sc : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

local notation "Cts" => sourceCounts macroN cn ratios resolutions
local notation "M" => sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km
local notation "G" => sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR

theorem sourceCanonical_upperNoise_projection
    (hl : 0<sc.curvature) (hw : 0<sc.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (q : ℕ) (V : Submodule ℝ (EuclideanGaussian.Space dim))
    (p : Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
    (hp : ∀ k,upperNoiseVectors p k∈V)
    (hE : ∀ i : FrameIndex Cts 0,GenieProtocol.BoundedEnergy
      (sharedKnown Cts 0 dim q (columns hAll a) V)
      (prefixSet (retained Cts 0 q i)) (columns hAll a i)
        (sourcePublicCap macroN 0 sc ratios resolutions weight CR ζ Km ((G 0 []).width/2))) :
    (∀ k : Fin ((M).n+1),counter Cts 1 q 0 []≤k.val →
      |(M).coordinates p.fst.fst k|≤3*(M).width/16) ∧
    (∀ I,∀ k : Fin ((G 0 I).n+1),canonicalCounter Cts 0 q 0 I≤k.val →
      |(G 0 I).coordinates (block 1 0 p.snd) k|≤(G 0 []).width/32) := by
  let W := sharedKnown Cts 0 dim q (columns hAll a) V
  have geo := sourceCanonical_geometry macroN 0 dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have hτ : 0<(G 0 []).width/2 := div_pos (geo.2.2.1 0 []).1 (by norm_num)
  have loc := sourceCanonical_locality_from_energy macroN 0 dim cn ratios resolutions hdim hAll a sc weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q V ((G 0 []).width/2) hτ hE
  have hraw : ∀ k,upperNoiseVectors p k∈W := fun k => Submodule.mem_sup_left (hp k)
  have hm := upperNoiseVectors_macro_mem p W hraw
  have hn := upperNoiseVectors_lower_mem p W hraw
  constructor
  · intro k hk
    have hb := ((M).coordinate_projection_bound geo.2.1 W ⟨p.fst.fst,hm⟩ k).trans (loc.2.1 k hk)
    linarith [geo.1]
  · intro I k hk
    have hb := ((G 0 I).coordinate_projection_bound (geo.2.2.1 0 I).2.1 W
      ⟨p.snd ⟨0,by omega⟩,hn ⟨0,by omega⟩⟩ k).trans (loc.2.2.2.1 I k hk)
    rw [block,dif_pos (by omega : 0<1),PiLp.proj_apply]
    convert hb using 1
    ring

end Bilevel.ChiHierarchyHaar
