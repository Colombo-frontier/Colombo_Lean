import Bilevel.ChiCanonicalSourceCertificate
import Bilevel.ChiVirtualActiveReply
import Bilevel.ChiFiniteVirtualJointReply

/-! Exact active full lower reply from the finite precoin energy event
and the actual finite disclosed store. No small-hidden-force premise is used. -/
noncomputable section
set_option maxHeartbeats 1600000
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

theorem sourceCanonical_active_reply_from_energy
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(G J []).width) (hv : 1≤v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (rad R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (hwidth : ∀ i : Fin J,0<(G (i.val+1) []).width)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyExtension (J+1) M G J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension (J+1) M G J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (h2 : ∀ p : {p : VirtualState M G | ValidState M G (finiteMacroCounter Cts J) (canonicalCounter Cts J) p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential true (J+1) M G J (finiteMacroCounter Cts J) (canonicalCounter Cts J)
        c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (q : ℕ) (V : Submodule ℝ (EuclideanGaussian.Space dim))
    (p : PartialLegendre.FullNormalVariables (EuclideanGaussian.Space dim)
      (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))
    (hp : ∀ k,originalVectors p k∈V)
    (hE : ∀ i : FrameIndex Cts J,GenieProtocol.BoundedEnergy
      (sharedKnown Cts J dim q (columns hAll a) V)
      (prefixSet (retained Cts J q i)) (columns hAll a i)
        (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km
          (ZeroChainSchedule.width c (G J []).width v (ZeroChainSchedule.levels v))))
    (μ L : ℝ) :
    virtualFullGradient true (J+1) M G J (finiteMacroCounter Cts J) (canonicalCounter Cts J)
      c v hc hβ hv s index radialIndex fineIndex rad R dn hR hwidth h2 μ L (st (q+1),p)=
    gradient (fullExtensionLower
      (hierarchyExtension (J+1) M G J c v hc hβ hv s index radialIndex fineIndex rad R dn)
      (hierarchyExtension_contDiff (J+1) M G J c v hc hβ hv s index radialIndex fineIndex rad R dn hwidth)
      (1/12) ha (by change (1/12:ℝ)<1;norm_num) μ L) p := by
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
  let Wnew := sharedKnown Cts J dim (q+1) (columns hAll a) V
  have bknew := sourceCanonical_bookkeeping macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km (q+1)
  have valid := sourceCanonicalState_valid macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km (q+1)
  have hg := statePotential_contDiff true (J+1) M G J (finiteMacroCounter Cts J) (canonicalCounter Cts J)
    c v hc hβ hv s index radialIndex fineIndex rad R dn hR hwidth (st (q+1)) valid
  have he := hierarchy_active_inverse_reply_eq_virtual M G J (by omega)
    (fun _ : Fin (J+1) => W) (fun _ : Fin (J+1) => Wnew) (fun _ => loc.2.2.2.2.1)
    (canonicalCounter Cts J q) loc.1
    (fun t _ I => (geo.2.2.1 (t+1) I).2.2.2.1)
    (fun t _ I => (geo.2.2.1 (t+1) I).2.2.2.2) bk.2.2.2.1
    c v hc hcs hβ hv (fun I => (geo.2.2.1 J I).2.2.1.le) (geo.2.2.2 J)
    (fun I k hk => (loc.2.2.2.1 I k hk).trans (by have := widths.1;dsimp only [τ] at *;linarith))
    s index radialIndex fineIndex rad R dn hR loc.2.2.1 widths.2.2.1 ha hi p.fst.fst ⟨p.snd,qi.2⟩
    (counter Cts (J+1) q 0 []) (counter Cts (J+1) (q+1) 0 []) (canonicalCounter Cts J (q+1))
    (st (q+1)).2.1 (st (q+1)).2.2
    (sourceCanonicalState_macro_prefix macroN J dim cn ratios resolutions hdim hAll a initial weight A Kminus ζ CR Km (q+1))
    (sourceCanonicalState_inner_prefix macroN J dim cn ratios resolutions hdim hAll a initial weight A Kminus ζ CR Km (q+1))
    bk.1 bk.2.1 geo.1 geo.2.1
    (fun k hk => ((M).coordinate_projection_bound geo.2.1 W ⟨p.fst.fst,qi.1⟩ k).trans (loc.2.1 k hk))
    (widths.2.1.trans (by have := geo.1;linarith)) bknew.2.2.2.1 bk.2.2.2.2 loc.2.2.2.2.2 hg
    (1/12) (by change (1/12:ℝ)<1;norm_num) (h2 ⟨st (q+1),valid⟩)
  rw [virtualFullGradient_eq true (J+1) M G J (finiteMacroCounter Cts J) (canonicalCounter Cts J)
    c v hc hβ hv s index radialIndex fineIndex rad R dn hR hwidth h2 μ L (st (q+1),p) valid]
  exact (he.2 μ L p.fst.snd).symm

end Bilevel.ChiHierarchyHaar
