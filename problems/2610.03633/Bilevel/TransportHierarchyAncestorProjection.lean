import Bilevel.TransportHierarchySourceProjection
import Bilevel.TransportPublicCapBounds

/-! Actual ancestor auxiliary-frame energy bounds imply the ordinary
weighted projection margins used by the physical inverse certificate. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyHaar ChiHierarchyExecution TransportRound TransportNetwork EndpointTransportResponse
set_option maxHeartbeats 1000000

theorem physicalFamily_ancestor_projection {counts : ℕ → ℕ} {J n D : ℕ}
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D) (hA : auxiliaryCapacity counts J+1≤D)
    (s : PhysicalSample counts J n D) (q j : ℕ) (hj : j<J) (I : List ℕ)
    (W : Submodule ℝ (EuclideanGaussian.Space D)) (cap : ℝ) (hcap : 0≤cap)
    (hE : GenieProtocol.BoundedEnergy W (prefixSet (canonicalCounter counts J q j I))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA
        (enumerate counts J (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I))) s) cap)
    (k : Fin (counts (j+1)+1)) (hk : canonicalCounter counts J q j I≤k.val) :
    ‖W.orthogonalProjection (physicalFamily hdim hT s j I (basis k))‖≤Real.sqrt cap := by
  have hh := frame_projection_norm_bound W _ _ cap hcap hE
    (auxiliaryColumnIndex counts J (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I)) k) hk
  rw [auxiliary_column_nested hAll hA s] at hh
  rw [physicalFamily_ancestor hdim hT hAll s j hj I]
  exact hh

theorem sourcePhysical_ancestor_projection (macroN J n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
    (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)
    (q j : ℕ) (hj : j<J) (I : List ℕ) (W : Submodule ℝ (EuclideanGaussian.Space D))
    (cap : ℝ) (hcap : 0≤cap)
    (hE : GenieProtocol.BoundedEnergy W
      (prefixSet (canonicalCounter (sourceCounts macroN cn ratios resolutions) J q j I))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1) hA
        (enumerate (sourceCounts macroN cn ratios resolutions) J
          (Sum.inr (canonicalNode (sourceCounts macroN cn ratios resolutions) J ⟨j,Nat.lt_succ_of_lt hj⟩ I))) s) cap)
    (hR : 0≤(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).radius)
    (hbudget : (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).radius*
      Real.sqrt cap≤(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).width/8)
    (k : Fin (sourceChainIndex cn (ratios j) (resolutions j)+1))
    (hk : canonicalCounter (sourceCounts macroN cn ratios resolutions) J q j I≤k.val) :
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).radius*
      ‖W.orthogonalProjection ((sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).frame (basis k))‖≤
      (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).width/8 := by
  exact (mul_le_mul_of_nonneg_left
    (physicalFamily_ancestor_projection hdim hT hAll hA s q j hj I W cap hcap hE k hk) hR).trans hbudget

end Bilevel.TransportHierarchy
