import Bilevel.ChiCanonicalSourceQuery
import Bilevel.ChiCanonicalSourceCap
import Bilevel.ChiSourcePublicCap

/-! Literal source locality inputs from one finite same-query energy event.
The common positive cap is constructed from public source parameters;
there is no desired projection bound or nonlinear reply premise. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiExtensionCalibration

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

local notation "Cts" => sourceCounts macroN cn ratios resolutions
local notation "M" => sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km
local notation "G" => sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR

theorem sourceCanonical_finest_geometry
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v) :
    let τ := ZeroChainSchedule.width c (G J []).width v (ZeroChainSchedule.levels v)
    0<τ ∧ τ≤(M).width/128 ∧ (∀ j I,j≤J → τ≤(G j I).width/128) ∧
      0<τ/16 ∧ τ/16≤(M).width/16 ∧ ∀ j I,j≤J → τ/16≤(G j I).width/16 := by
  have h := source_finest_uniform_widths initial ratios resolutions weight A Kminus ζ cn CR Km macroN
    (frame hAll a (Sum.inl ())) (canonicalFamily hdim a) hl hw hr hη hη1 J c v hc hcs hv
  have hd := source_uniform_germ_radius initial ratios resolutions weight A Kminus ζ cn CR Km macroN
    (frame hAll a (Sum.inl ())) (canonicalFamily hdim a) hl hw hr hη hη1 J c v hc hcs hv
  exact ⟨h.1,h.2.1,h.2.2,hd.1,hd.2.1,hd.2.2⟩

theorem sourceCanonical_locality_from_energy
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (q : ℕ) (V : Submodule ℝ (EuclideanGaussian.Space dim)) (τ : ℝ) (hτ : 0<τ)
    (hE : ∀ i : FrameIndex Cts J,GenieProtocol.BoundedEnergy
      (sharedKnown Cts J dim q (columns hAll a) V)
      (prefixSet (retained Cts J q i)) (columns hAll a i)
        (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ)) :
    let W := sharedKnown Cts J dim q (columns hAll a) V
    let Wnew := sharedKnown Cts J dim (q+1) (columns hAll a) V
    TreeProjection G 0 J (by omega) (fun _ : Fin (J+1) => W) (canonicalCounter Cts J q) ∧
    (∀ k : Fin ((M).n+1),counter Cts (J+1) q 0 []≤k.val →
      (M).radius*‖W.orthogonalProjection ((M).frame (basis k))‖≤(M).width/8) ∧
    (∀ j I,j≤J → ∀ k : Fin ((G j I).n+1),canonicalCounter Cts J q j I≤k.val →
      (G j I).radius*‖W.orthogonalProjection ((G j I).frame (basis k))‖≤(G j I).width/8) ∧
    (∀ I,∀ k : Fin ((G J I).n+1),canonicalCounter Cts J q J I≤k.val →
      (G J I).radius*‖W.orthogonalProjection ((G J I).frame (basis k))‖≤τ/16) ∧
    W≤Wnew ∧
    (∀ I,∀ k : Fin ((G J I).n+1),k.val<canonicalCounter Cts J (q+1) J I →
      (G J I).frame (basis k)∈Wnew) := by
  have hcap := sourceCanonical_cap_certificate macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm τ hτ
  have hE' : ∀ i : FrameIndex Cts J,GenieProtocol.BoundedEnergy
      (sharedKnown Cts J dim q (columns hAll a) V)
      (prefixSet (retained Cts J q i)) (columns hAll a i) (sourceProjectionCap M G J τ) := by
    rw [sourceCanonical_cap_eq_public]
    exact hE
  exact sourceCanonical_tree_from_energy macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q V (sourceProjectionCap M G J τ) τ hcap.1.le hE'
    hcap.2.2.1 hcap.2.2.2.1 hcap.2.2.2.2

end Bilevel.ChiHierarchyHaar
