import Bilevel.ChiCanonicalSourceExpected
import Bilevel.ChiCanonicalPublicData
import Bilevel.ChiSourceDeterministicWitness

/-! The analytic input of the actual expected-query theorem, with one
public collection of normal parameters for the entire orientation family.
The fields concern constructed potentials and the actual mean gradient;
they contain no information or query-complexity premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration

structure CanonicalQueryCertificate (macroN J dim : ℕ) (cn : ℝ)
    (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
    (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (hJ : 1≤J)
    (v : ℝ) (rad R : ℕ → ℝ) (L K ε : ℝ) : Prop where
  fine_ge_one : 1≤v
  width_pos : ∀ j I,0<(sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight 3 1 ζ CR j I).width
  actual : ∀ (active : Bool) (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim) z,
    ‖iteratedFDeriv ℝ 2 (originalPotential active (J+1)
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)
      J (1/128) v (by norm_num)
      (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim sc weight 3 1 ζ CR (width_pos J []) a)
      fine_ge_one (2*J) (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ)
      rad R (normalCoefficient L J)) z‖≤1/12
  virtual : ∀ (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
    (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
    (p : VirtualState (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)),
    ValidState (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR) rM r p → ∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active (J+1)
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)
      J rM r (1/128) v (2*J) (sourceCoarseNormal J) (sourceRadialNormal J)
      (sourceFineNormal J hJ) rad R (normalCoefficient L J) p) z‖≤1/12
  barrier : ∀ (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
    (x : Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim))),
    (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km).coordinates x.fst (Fin.last macroN)<sc.width →
    8*ε≤sourceOriginalLoss macroN J dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
      (J+1) (sc.curvature/24) rad R J K a x

variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}

theorem CanonicalQueryCertificate.regular
    (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)
    (active : Bool) (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim) :
    ContDiff ℝ 3 (originalPotential active (J+1)
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)
      J (1/128) v (by norm_num)
      (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim sc weight 3 1 ζ CR (H.width_pos J []) a)
      H.fine_ge_one (2*J) (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ)
      rad R (normalCoefficient L J)) := by
  have hw (j : ℕ) (I : List ℕ) :
      0<(sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR j I).width := H.width_pos j I
  cases active with
  | false => exact hierarchyInactiveExtension_contDiff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun i => hw (i.val+1) [])
  | true => exact hierarchyExtension_contDiff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun i => hw (i.val+1) [])

def sourceBranchBound (active : Bool) : NNReal :=
  if active then ⟨1/12,by norm_num⟩ else ⟨1/4,by norm_num⟩

theorem sourceBranchBound_lt_one (active : Bool) : sourceBranchBound active<1 := by
  cases active <;> change (_:ℝ)<1 <;> norm_num [sourceBranchBound]

theorem CanonicalQueryCertificate.actual_branch_bound
    (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)
    (active : Bool) (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim) z :
    ‖iteratedFDeriv ℝ 2 (originalPotential active (J+1)
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)
      J (1/128) v (by norm_num)
      (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim sc weight 3 1 ζ CR (H.width_pos J []) a)
      H.fine_ge_one (2*J) (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ)
      rad R (normalCoefficient L J)) z‖≤(sourceBranchBound active:ℝ) := by
  have h := H.actual active a z
  cases active <;> norm_num [sourceBranchBound] at *
  · linarith
  · exact h

end Bilevel.ChiHierarchyHaar
