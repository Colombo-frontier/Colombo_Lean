import FreshGradientMinimax.AcceleratedPhysicalModel
import FreshGradientMinimax.AcceleratedStageMasks
import FreshGradientMinimax.JointGradientLocality

/-! Scalar objectives and their actual gradients on arbitrary linear
coordinate readings, including colliding coordinate labels. Full ambient
norms are retained in both radial terms. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
variable {n k dx dy : ℕ}

def acceleratedRawProtected (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (δ : ℝ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) : ℝ :=
  acceleratedPrimal n k δ u - robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2 -
    smoothMaximum (acceleratedDualRadius n k ^ 2) (robinMultiEnergy n k δ u (B y))
      (ambientAcceleratedWall n k y)

def acceleratedRawObjective (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (δ : ℝ) (x : Euclid dx) (y : Euclid dy) : ℝ :=
  acceleratedRawProtected B δ (A (radialCompression (acceleratedPrimalRadius k) x)) y +
    primalRidgeConstant / 2 * ‖x‖ ^ 2

def acceleratedRawPhysical (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (L ε : ℝ) (x : Euclid dx) (y : Euclid dy) : ℝ :=
  acceleratedValueScale L ε * acceleratedRawObjective A B (acceleratedThreshold n k)
    ((acceleratedLengthScale L ε)⁻¹ • x) ((acceleratedLengthScale L ε)⁻¹ • y)

def acceleratedPrefixObjective (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (L ε : ℝ) (t : ℕ) : Euclid dx → Euclid dy → ℝ :=
  acceleratedRawPhysical ((acceleratedPrimalPrefix n k t).comp A) ((acceleratedDualPrefix n k t).comp B) L ε

def acceleratedPrefixReply (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (L ε : ℝ) (t : ℕ) : Joint dx dy → Joint dx dy :=
  actualJointGradient (acceleratedPrefixObjective A B L ε t)

theorem acceleratedRawProtected_contDiff (B : Euclid dy →L[ℝ] Euclid (k * (n + 2)))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Joint (k * 2 + 1) dy => acceleratedRawProtected B δ z.1 z.2) := by
  let C : Joint (k * 2 + 1) dy →L[ℝ] Joint (k * 2 + 1) (k * (n + 2)) :=
    (ContinuousLinearMap.fst ℝ (Euclid (k * 2 + 1)) (Euclid dy)).prod
      (B.comp (ContinuousLinearMap.snd ℝ (Euclid (k * 2 + 1)) (Euclid dy)))
  have hQ : ContDiff ℝ 1 (fun z : Joint (k * 2 + 1) dy => robinMultiEnergy n k δ z.1 (B z.2)) :=
    (robinMultiEnergy_joint_contDiff n k hδ).comp_continuousLinearMap (g := C)
  have hW : ContDiff ℝ 1 (fun z : Joint (k * 2 + 1) dy => ambientAcceleratedWall n k z.2) :=
    contDiff_const.mul (((contDiff_norm_sq ℝ).comp contDiff_snd).sub contDiff_const)
  exact (((acceleratedPrimal_contDiff n k hδ).comp contDiff_fst).sub
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd))).sub
      ((smoothMaximum_contDiff (sq_pos_of_pos (acceleratedDualRadius_pos n k))).comp (hQ.prodMk hW))

theorem acceleratedRawObjective_contDiff (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Joint dx dy => acceleratedRawObjective A B δ z.1 z.2) :=
  ((acceleratedRawProtected_contDiff B hδ).comp
    ((A.contDiff.comp ((radialCompression_contDiff _).comp contDiff_fst)).prodMk contDiff_snd)).add
      (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst))

theorem acceleratedRawPhysical_contDiff (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (hk : 0 < k) (L ε : ℝ) :
    ContDiff ℝ 1 (fun z : Joint dx dy => acceleratedRawPhysical A B L ε z.1 z.2) := by
  let C : Joint dx dy →L[ℝ] Joint dx dy :=
    (acceleratedLengthScale L ε)⁻¹ • ContinuousLinearMap.id ℝ (Joint dx dy)
  have hc := (acceleratedRawObjective_contDiff A B (acceleratedThreshold_pos n hk).le).comp_continuousLinearMap (g := C)
  have hm : ContDiff ℝ 1 (fun z : Joint dx dy => acceleratedValueScale L ε *
      acceleratedRawObjective A B (acceleratedThreshold n k) (C z).1 (C z).2) := contDiff_const.mul hc
  simpa only [acceleratedRawPhysical, C, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Prod.smul_fst, Prod.smul_snd] using hm

theorem acceleratedPrefixReply_continuous (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (hk : 0 < k) (L ε : ℝ) (t : ℕ) :
    Continuous (acceleratedPrefixReply A B L ε t) :=
  actualJointGradient_continuous (acceleratedRawPhysical_contDiff _ _ hk L ε)

theorem acceleratedPrefixReply_measurable (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (hk : 0 < k) (L ε : ℝ) (t : ℕ) :
    Measurable (acceleratedPrefixReply A B L ε t) :=
  (acceleratedPrefixReply_continuous A B hk L ε t).measurable

theorem acceleratedRawObjective_frame (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy) (δ : ℝ) :
    acceleratedRawObjective (frameCoordinates U) (frameCoordinates V) δ = acceleratedCompressedObjective U V δ := by
  funext x y
  simp only [acceleratedRawObjective, acceleratedRawProtected, acceleratedCompressedObjective,
    compressedObjective, compressedCoordinates, inv_one, one_smul, framedAcceleratedProtected,
    framedAcceleratedCap, framedRobinEnergy]

theorem acceleratedRawPhysical_frame (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy) (hn : 10 ≤ n + 2) (hk : 0 < k)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) :
    acceleratedRawPhysical (frameCoordinates U) (frameCoordinates V) L ε =
      (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).f := by
  funext x y
  rw [acceleratedRawPhysical, acceleratedRawObjective_frame, acceleratedPhysicalModel_formula]

theorem acceleratedPrefixReply_congr
    (A A' : Euclid dx →L[ℝ] Euclid (k * 2 + 1))
    (B B' : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (L ε : ℝ) (t : ℕ)
    (hA : ∀ j, acceleratedPrimalStage n j ≤ t → ∀ x, A x j = A' x j)
    (hB : ∀ j, acceleratedDualStage n j ≤ t → ∀ y, B y j = B' y j) :
    acceleratedPrefixReply A B L ε t = acceleratedPrefixReply A' B' L ε t := by
  have ha := stageMask_comp_congr (acceleratedPrimalStage n) t A A' hA
  have hb := stageMask_comp_congr (acceleratedDualStage n) t B B' hB
  unfold acceleratedPrefixReply acceleratedPrefixObjective acceleratedPrimalPrefix acceleratedDualPrefix
  rw [ha, hb]

end FreshGradientMinimax
