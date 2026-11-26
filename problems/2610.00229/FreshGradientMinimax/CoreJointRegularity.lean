import FreshGradientMinimax.MaskedCoreSmooth

/-! Joint C1 regularity of the actual capped formula. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

theorem weightedCoreSeed_contDiff {n : ℕ} {m : ℕ∞} (w : Euclid n) :
    ContDiff ℝ m (weightedCoreSeed w) := by
  have hp (i : Fin (n + 1)) : ContDiff ℝ m (fun u : Euclid (n + 1) => u i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  apply ((coreTheta_contDiff.comp (hp 0)).neg).sub
  apply contDiff_const.mul
  apply ContDiff.sum
  intro e _
  exact contDiff_const.mul (coreGate_contDiff.comp (hp e.castSucc))

theorem coreInteraction_joint_contDiff {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a R : ℝ) (mask : Fin (n + n) → ℝ) :
    ContDiff ℝ 2 (fun z : Euclid (n + 1) × Euclid dy => coreInteraction V a R mask z.1 z.2) := by
  have hu : ContDiff ℝ 2 (fun z : Euclid (n + 1) × Euclid dy => coreLinks z.1) :=
    coreLinks_contDiff.comp contDiff_fst
  have hy : ContDiff ℝ 2 (fun z : Euclid (n + 1) × Euclid dy =>
      coordinateMultiplier mask (clipVector R (frameCoordinates V z.2))) :=
    (coordinateMultiplier mask).contDiff.comp ((clipVector_contDiff R).comp
      ((frameCoordinates V).contDiff.comp contDiff_snd))
  exact contDiff_const.mul (hy.inner ℝ hu)

theorem maskedCore_joint_contDiff {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (w : Euclid n) (mask : Fin (n + n) → ℝ) :
    ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => maskedCoreObjective V μ t w mask z.1 z.2) := by
  have hn : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => ‖z.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_snd
  have hΓ := (coreInteraction_joint_contDiff V (2 * μ * t) (32 * t) mask).of_le (show 1 ≤ 2 by norm_num)
  have hQ : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => coreProtectedQ V μ t mask z.1 z.2) :=
    (contDiff_const.mul hn).sub hΓ
  have hW : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => coreProtectedWall n μ t z.2) :=
    (contDiff_const.mul hn).sub contDiff_const
  have hK := (smoothMaximum_contDiff (coreCapHeight_pos n hμ ht)).comp (hQ.prodMk hW)
  exact ((contDiff_const.mul ((weightedCoreSeed_contDiff w).comp contDiff_fst)).sub
    (contDiff_const.mul hn)).sub hK

end FreshGradientMinimax
