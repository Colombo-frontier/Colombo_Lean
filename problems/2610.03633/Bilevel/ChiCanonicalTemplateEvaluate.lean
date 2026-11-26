import Bilevel.ChiCanonicalSourceReframe
import Bilevel.ChiFiniteVirtualJointReply

/-! Exact complete SFO pair at one query, from the actual finite energy
event. Upper and inactive replies use the old store; the active reply uses
the success-updated store. No reply equality is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
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

theorem sourceCanonical_evaluate_template
    (c v : ℝ) (hc : 0<c) (hβ : 0<(G J []).width) (hv : 1≤v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (rad R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (hwidth : ∀ i : Fin J,0<(G (i.val+1) []).width)
    (h2 : ∀ active : Bool,∀ p : {p : VirtualState M G | ValidState M G (finiteMacroCounter Cts J) (canonicalCounter Cts J) p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active (J+1) M G J (finiteMacroCounter Cts J) (canonicalCounter Cts J)
        c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (a₀ : Orientations Cts J dim)
    (h2₀ : ∀ active : Bool,∀ p : {p : VirtualState
        (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a₀ initial Km)
        (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a₀ initial weight A Kminus ζ CR) |
        ValidState (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a₀ initial Km)
          (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a₀ initial weight A Kminus ζ CR)
          (finiteMacroCounter Cts J) (canonicalCounter Cts J) p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active (J+1)
        (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a₀ initial Km)
        (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a₀ initial weight A Kminus ζ CR)
        J (finiteMacroCounter Cts J) (canonicalCounter Cts J)
        c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (μ L π ν ρ₀ R₀ : ℝ) (b : Normals s)
    (p : PartialLegendre.FullNormalVariables (EuclideanGaussian.Space dim)
      (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))
    (old new : Store Cts J (EuclideanGaussian.Space dim)) (coin : Bool) :
    virtualJointEvaluate Cts J (J+1) M G rfl (fun _ _ => rfl) c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hwidth h2 μ L π ν ρ₀ R₀ b p old new coin=
    virtualJointEvaluate Cts J (J+1)
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a₀ initial Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a₀ initial weight A Kminus ζ CR)
      rfl (fun _ _ => rfl) c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hwidth h2₀ μ L π ν ρ₀ R₀ b p old new coin := by
  have hM := sourceCanonicalMacro_reframe macroN J dim cn ratios resolutions hAll a a₀ initial Km
  have hG := sourceCanonicalGeometry_reframe macroN J dim cn ratios resolutions hdim a a₀ initial weight A Kminus ζ CR
  simp only [hM,hG] at h2 ⊢
  exact virtualJointEvaluate_reframe Cts J (J+1)
    (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a₀ initial Km)
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a₀ initial weight A Kminus ζ CR)
    rfl (fun _ _ => rfl) c v hc hβ hv s index radialIndex fineIndex rad R dn hR hwidth h2₀
    (frame hAll a (Sum.inl ())) (canonicalFamily hdim a) h2 μ L π ν ρ₀ R₀ b p old new coin

end Bilevel.ChiHierarchyHaar
