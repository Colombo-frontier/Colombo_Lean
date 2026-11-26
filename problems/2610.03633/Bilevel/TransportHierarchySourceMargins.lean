import Bilevel.TransportHierarchySourceProjection
import Bilevel.TransportPublicCapBounds

/-! Public source quantities supply one uniform germ radius and the macro
query-tail margin. Neither quantity depends on an ambient frame choice. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  ChiHierarchyHaar ChiHierarchyExecution TransportRound TransportNetwork EndpointTransportResponse
set_option maxHeartbeats 1000000

variable (macroN J n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

theorem sourcePhysical_uniform_germ_radius
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1) :
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km
    let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
    let δ := (parentScale initial ratios resolutions (J+1)).width/16
    0<δ ∧ δ≤M.width/16 ∧ ∀ j I,j≤J → δ≤(G j I).width/16 := by
  have hp := parentScale_positive initial ratios resolutions hl hw hr hη
  have hm := parentScale_width_antitone initial ratios resolutions hl hw hr hη hη1
  dsimp only
  refine ⟨div_pos (hp (J+1)).2 (by norm_num),?_,?_⟩
  · change (parentScale initial ratios resolutions (J+1)).width/16≤
      (parentScale initial ratios resolutions 0).width/16
    exact div_le_div_of_nonneg_right (hm (Nat.zero_le (J+1))) (by norm_num)
  · intro j I hj
    change (parentScale initial ratios resolutions (J+1)).width/16≤
      (parentScale initial ratios resolutions (j+1)).width/16
    exact div_le_div_of_nonneg_right (hm (by omega)) (by norm_num)

theorem sourcePhysical_macro_blind
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ : ℝ) (hτ : 0<τ) (q : ℕ) (W : Submodule ℝ (EuclideanGaussian.Space D))
    (x : EuclideanGaussian.Space D) (hx : x∈W)
    (hE : GenieProtocol.BoundedEnergy W
      (prefixSet (counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 []))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1) hA
        (enumerate (sourceCounts macroN cn ratios resolutions) J (Sum.inl ())) s)
      (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ)) :
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km
    ∀ k : Fin (M.n+1),counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 []≤k.val →
      |M.coordinates x k|≤M.width/8 := by
  dsimp only
  intro k hk
  let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km
  have hR : 0<M.radius := by
    change 0<Km*initial.width*Real.sqrt ((macroN:ℝ)+1)
    positivity
  have cap := sourcePublicCap_budgets macroN J initial ratios resolutions weight CR ζ Km τ
    hl hw hr hη hweight hCR hζ hKm hτ
  exact (M.coordinate_projection_bound hR W ⟨x,hx⟩ k).trans
    (sourcePhysical_macro_projection macroN J n D cn ratios resolutions hAll hA s initial Km W q _ cap.1.le
      hE hR.le (cap.2.2 (Sum.inl ())) k hk)

end Bilevel.TransportHierarchy
