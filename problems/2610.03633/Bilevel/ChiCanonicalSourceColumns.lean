import Bilevel.ChiCanonicalSourceFields

/-! Column projection bounds for the literal source records, with each
dependent frame conversion isolated from the subsequent scalar arithmetic. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive

theorem sourceCanonical_inner_projection (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)
    (q : ℕ) (W : Submodule ℝ (EuclideanGaussian.Space dim)) (cap : ℝ) (hcap : 0≤cap)
    (hE : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,
      GenieProtocol.BoundedEnergy W (prefixSet (retained (sourceCounts macroN cn ratios resolutions) J q i))
        (columns hAll a i) cap)
    (j : ℕ) (hj : j≤J) (I : List ℕ) (k : Fin (sourceChainIndex cn (ratios j) (resolutions j)+1))
    (hk : canonicalCounter (sourceCounts macroN cn ratios resolutions) J q j I≤k.val) :
    ‖W.orthogonalProjection
      ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).frame
        (basis k))‖≤Real.sqrt cap := by
  rw [sourceCanonicalGeometry_frame]
  exact canonical_projection_norm (counts:=sourceCounts macroN cn ratios resolutions) (J:=J) (D:=dim)
    hdim hAll a q W cap hcap hE j hj I k hk

end Bilevel.ChiHierarchyHaar
