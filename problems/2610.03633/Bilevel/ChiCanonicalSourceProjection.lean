import Bilevel.ChiCanonicalSourceColumns

/-! Finite energy caps give the exact all-list analytic projection margins
for the sampled source geometry. Public scalar radius/width inequalities
remain explicit; no inverse or oracle equality is assumed here. -/
noncomputable section
set_option maxHeartbeats 200000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

local notation "Cts" => sourceCounts macroN cn ratios resolutions
local notation "M" => sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km
local notation "G" => sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR


theorem sourceCanonical_geometry
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km) :
    0<(M).width ∧ 0<(M).radius ∧
    (∀ j I,0<(G j I).width ∧ 0<(G j I).radius ∧ 0<(G j I).ell ∧
      0<(G j I).parentWidth ∧ (G j I).width≤(G j I).parentWidth) ∧
    (∀ j I,(G j I).width=(G j []).width) :=
  source_inverse_geometry initial ratios resolutions weight A Kminus ζ cn CR Km macroN
    (frame hAll a (Sum.inl ())) (canonicalFamily hdim a) hl hw hr hη hη1 hweight hζ hCR hKm


theorem sourceCanonical_projection_margins (q : ℕ) (W : Submodule ℝ (EuclideanGaussian.Space dim))
    (cap τ : ℝ) (hcap : 0≤cap)
    (hE : ∀ i : FrameIndex Cts J,GenieProtocol.BoundedEnergy W
      (ChiHierarchyExecution.prefixSet (retained Cts J q i)) (columns hAll a i) cap)
    (hmR : 0≤(M).radius) (hR : ∀ j,j≤J → 0≤(G j []).radius)
    (hmBudget : (M).radius*Real.sqrt cap≤(M).width/8)
    (hBudget : ∀ j,j≤J → (G j []).radius*Real.sqrt cap≤(G j []).width/8)
    (hfBudget : (G J []).radius*Real.sqrt cap≤τ/16) :
    (∀ k : Fin ((M).n+1),counter Cts (J+1) q 0 []≤k.val →
      (M).radius*‖W.orthogonalProjection ((M).frame (basis k))‖≤(M).width/8) ∧
    (∀ j I,j≤J → ∀ k : Fin ((G j I).n+1),canonicalCounter Cts J q j I≤k.val →
      (G j I).radius*‖W.orthogonalProjection ((G j I).frame (basis k))‖≤(G j I).width/8) ∧
    (∀ I,∀ k : Fin ((G J I).n+1),canonicalCounter Cts J q J I≤k.val →
      (G J I).radius*‖W.orthogonalProjection ((G J I).frame (basis k))‖≤τ/16) := by
  constructor
  · intro k hk
    have hp := frame_projection_norm_bound (D:=dim) (T:=macroN+1) W (retained Cts J q (Sum.inl ()))
      (columns hAll a (Sum.inl ())) cap hcap (hE (Sum.inl ())) k hk
    change (M).radius*‖W.orthogonalProjection (frame hAll a (Sum.inl ()) (basis k))‖≤_
    rw [frame_basis]
    exact (mul_le_mul_of_nonneg_left hp hmR).trans hmBudget
  have hri (j : ℕ) (I : List ℕ) : (G j I).radius=(G j []).radius := by
    rw [sourceCanonicalGeometry_radius,sourceCanonicalGeometry_radius]
  have hwi (j : ℕ) (I : List ℕ) : (G j I).width=(G j []).width := by
    rw [sourceCanonicalGeometry_width,sourceCanonicalGeometry_width]
  constructor
  · intro j I hj k hk
    have hp := sourceCanonical_inner_projection macroN J dim cn ratios resolutions hdim hAll a initial weight
      A Kminus ζ CR q W cap hcap hE j hj I k hk
    have hpos : 0≤(G j I).radius := by rw [hri];exact hR j hj
    have hbound := mul_le_mul_of_nonneg_left hp hpos
    exact hbound.trans (by rw [hri,hwi];exact hBudget j hj)
  · intro I k hk
    have hp := sourceCanonical_inner_projection macroN J dim cn ratios resolutions hdim hAll a initial weight
      A Kminus ζ CR q W cap hcap hE J le_rfl I k hk
    have hpos : 0≤(G J I).radius := by rw [hri];exact hR J le_rfl
    have hbound := mul_le_mul_of_nonneg_left hp hpos
    exact hbound.trans (by rw [hri];exact hfBudget)



theorem sourceCanonical_known_columns (q : ℕ) (V : Submodule ℝ (EuclideanGaussian.Space dim)) :
    (∀ k : Fin ((M).n+1),k.val<counter Cts (J+1) q 0 [] →
      (M).frame (basis k)∈sharedKnown Cts J dim q (columns hAll a) V) ∧
    (∀ j I,j≤J → ∀ k : Fin ((G j I).n+1),k.val<canonicalCounter Cts J q j I →
      (G j I).frame (basis k)∈sharedKnown Cts J dim q (columns hAll a) V) := by
  constructor
  · intro k hk
    change frame hAll a (Sum.inl ()) (basis k)∈_
    rw [frame_basis]
    exact sharedKnown_column_mem Cts J dim q (columns hAll a) V (Sum.inl ()) k hk
  · intro j I hj k hk
    exact canonical_shared_column_mem (counts:=Cts) (J:=J) (D:=dim) hdim hAll a q V j hj I k hk

end Bilevel.ChiHierarchyHaar
