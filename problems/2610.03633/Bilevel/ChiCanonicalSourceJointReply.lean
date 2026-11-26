import Bilevel.ChiCanonicalSourceActiveReply
import Bilevel.ChiCanonicalSourceInactiveReply
import Bilevel.ChiCanonicalSourceUpper

/-! Exact complete SFO pair at one query, from the actual finite energy
event. Upper and inactive replies use the old store; the active reply uses
the success-updated store. No reply equality is assumed. -/
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

theorem sourceCanonical_joint_reply_from_energy
    (hJ : 0<J) (hl : 0< initial.curvature) (hw : 0< initial.width)
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
    (h2 : ∀ active : Bool,∀ p : {p : VirtualState M G | ValidState M G (finiteMacroCounter Cts J) (canonicalCounter Cts J) p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active (J+1) M G J (finiteMacroCounter Cts J) (canonicalCounter Cts J)
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
    (μ L π ν ρ₀ R₀ : ℝ) (b : Normals s) (coin : Bool) :
    let g := fullExtensionLower
      (hierarchyExtension (J+1) M G J c v hc hβ hv s index radialIndex fineIndex rad R dn)
      (hierarchyExtension_contDiff (J+1) M G J c v hc hβ hv s index radialIndex fineIndex rad R dn hwidth)
      (1/12) ha (by change (1/12:ℝ)<1;norm_num) μ L
    let g₀ := fullExtensionLower
      (hierarchyInactiveExtension (J+1) M G J c v hc hβ hv s index radialIndex fineIndex rad R dn)
      (hierarchyInactiveExtension_contDiff (J+1) M G J c v hc hβ hv s index radialIndex fineIndex rad R dn hwidth)
      (1/12) hi (by change (1/12:ℝ)<1;norm_num) μ L
    virtualJointEvaluate Cts J (J+1) M G rfl (fun _ _ => rfl) c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hwidth h2 μ L π ν ρ₀ R₀ b p
      (actual Cts J q (columns hAll a))
      (actual Cts J (q+if coin then 1 else 0) (columns hAll a)) coin=
      (gradient (ChiUpper.fullUpper (upperBase (J+1) M ν G J ρ₀ R₀) b) p,
        ChiConservative.sampleGradient g g₀ π coin p) := by
  dsimp only
  apply virtualJointEvaluate_eq_original Cts J (J+1) M G rfl (fun _ _ => rfl) c v hc hβ hv s
    index radialIndex fineIndex rad R dn hR hwidth h2 μ L π ν ρ₀ R₀ b p
    (actual Cts J q (columns hAll a)) (actual Cts J (q+if coin then 1 else 0) (columns hAll a)) coin
    (upperBase (J+1) M ν G J ρ₀ R₀) ((upperBase_contDiff (J+1) M ν G J ρ₀ R₀).differentiable (by norm_num))
  · exact (sourceCanonical_upper_germ_from_energy macroN J dim cn ratios resolutions hdim hAll a initial weight
      A Kminus ζ CR Km hJ hl hw hr hη hη1 hweight hζ hCR hKm c v hc hcs hv q s V p hp hE ν ρ₀ R₀).gradient_eq.symm
  · exact sourceCanonical_inactive_reply_from_energy macroN J dim cn ratios resolutions hdim hAll a initial weight
      A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm c v hc hcs hβ hv s index radialIndex fineIndex
      rad R dn hR hwidth hi (h2 false) q V p hp hE μ L
  · intro hcoin
    subst coin
    exact sourceCanonical_active_reply_from_energy macroN J dim cn ratios resolutions hdim hAll a initial weight
      A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm c v hc hcs hβ hv s index radialIndex fineIndex
      rad R dn hR hwidth ha hi (h2 true) q V p hp hE μ L

end Bilevel.ChiHierarchyHaar
