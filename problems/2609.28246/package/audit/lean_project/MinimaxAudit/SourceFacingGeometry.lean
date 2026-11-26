import MinimaxAudit.HardInstance
import MinimaxAudit.SourceGap

/-! Source-facing global admissibility and saddle-point geometry. Existing
source_scalar_residual_lower, source_tangent_residual_lower and
source_product_gap_lower are the full actual terminals for the other three
geometric lemmas; no conditional surrogate is mapped in their place. -/

open scoped ContDiff
namespace MinimaxAudit

/-- Complete source lemma admissibility: genuine global strong convexity,
strong concavity, same actual signed-gradient strong monotonicity, smoothness,
and dimension-independent highest-derivative Lipschitz constant. -/
theorem admissibility_source {n dx dy p : ℕ} (profile : GateProfile) (hp : 2 ≤ p)
    {tau lam c : ℝ} (htau : 0 < tau) (hlam : 0 < lam)
    {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) :
    let phi := minimaxHardPotential profile tau lam (balancedQ n) c hU hV
    let mu := lam * (1 - balancedQ n)
    0 < chainSmoothnessConstant p profile ∧ ContDiff ℝ ∞ phi ∧
    (∀ y : Dual dy, StrongConvexOn Set.univ mu (fun x => phi (joinBlocks x y))) ∧
    (∀ x : Primal dx, StrongConcaveOn Set.univ mu (fun y => phi (joinBlocks x y))) ∧
    (∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w)) ∧
    (∀ z w, ‖iteratedFDeriv ℝ p phi z - iteratedFDeriv ℝ p phi w‖ ≤
      (lam * chainSmoothnessConstant p profile * tau ^ (1 - (p : ℤ))) * ‖z - w‖) := by
  let phi := minimaxHardPotential profile tau lam (balancedQ n) c hU hV
  let mu := lam * (1 - balancedQ n)
  have hc : ContDiff ℝ ∞ phi := framedHardPotential_contDiff profile htau.ne'
    lam (balancedQ n) c (euclideanSaddleSign dx dy) (blockPairedFrame_orthonormal hU hV) (Fin.last n)
  have hd : Differentiable ℝ phi := fun z =>
    (framedHardPotential_hasFDerivAt profile htau.ne' lam (balancedQ n) c (euclideanSaddleSign dx dy)
      (euclideanSaddleSign_involutive dx dy) (blockPairedFrame_orthonormal hU hV) (Fin.last n) z).differentiableAt
  have hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w) :=
    minimaxHardPotential_strong_monotone profile (c := c) htau.ne' (balancedQ_nonneg n) hlam.le hU hV
  have hsc := saddle_strong_convex_concave phi hd mu hs
  refine ⟨chainSmoothnessConstant_pos p profile, hc, hsc.1, hsc.2, hs, ?_⟩
  intro z w
  have h := minimaxHardPotential_high_derivative_lipschitz profile hp htau lam (balancedQ n) c hU hV w z
  rw [abs_of_nonneg hlam.le, abs_of_nonneg (balancedQ_nonneg n)] at h
  have hcoef : lam * balancedQ n * chainDerivativeConstant p profile tau ≤
      lam * chainDerivativeConstant p profile tau :=
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hlam.le (balancedQ_le_one n))
      (chainDerivativeConstant_nonneg p profile htau)
  have hout := h.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (z - w)))
  simpa only [chainDerivativeConstant_scale, mul_assoc] using hout

section Saddle
variable {n dx dy : ℕ} {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
variable (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)

/-- The fixed point has no inactive orthogonal component. This is proved from
the concrete signed frame invariance, rather than assuming a range predicate. -/
theorem source_fixed_projection_identity (profile : GateProfile) (tau q c : ℝ)
    (z : SaddleSpace dx dy) (hfix : sourceTransport hU hV profile tau q c z = z) :
    frameSynthesis (blockPairedFrame_orthonormal hU hV)
      (frameAnalysis (blockPairedFrame_orthonormal hU hV) z) = z := by
  let W := blockPairedFrame U V
  let hW : Orthonormal ℝ W := blockPairedFrame_orthonormal hU hV
  let P : SaddleSpace dx dy →L[ℝ] SaddleSpace dx dy :=
    (frameSynthesis hW).toContinuousLinearMap.comp (frameAnalysis hW)
  have hsingle (i : Fin (n + 1) × Fin 2) :
      frameSynthesis hW (EuclideanSpace.single i 1) = W i := by
    simp [frameSynthesis, frameSynthesisLinear]
  have hPv (i : Fin (n + 1) × Fin 2) : P (W i) = W i := by
    rw [← hsingle i]
    change frameSynthesis hW (frameAnalysis hW (frameSynthesis hW (EuclideanSpace.single i 1))) = _
    rw [frameAnalysis_synthesis]
  have hPS (i : Fin (n + 1) × Fin 2) :
      P (euclideanSaddleSign dx dy (W i)) = euclideanSaddleSign dx dy (W i) := by
    let k := (blockPairedIndex (n + 1)).symm ((blockPairedIndex (n + 1) i).swap)
    have heq : euclideanSaddleSign dx dy (W i) = W k := by
      change euclideanSaddleSign dx dy (pairedFrame U V (blockPairedIndex (n + 1) i)) =
        pairedFrame U V (blockPairedIndex (n + 1) k)
      rw [saddle_sign_paired_frame]
      dsimp [k]
      rw [Equiv.apply_symm_apply]
    rw [heq]
    exact hPv k
  have hPg (g : EuclideanSpace ℝ (Fin (n + 1) × Fin 2)) :
      P (euclideanSaddleSign dx dy (frameSynthesis hW g)) =
        euclideanSaddleSign dx dy (frameSynthesis hW g) := by
    change P (euclideanSaddleSign dx dy (∑ i, g i • W i)) =
      euclideanSaddleSign dx dy (∑ i, g i • W i)
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hPS i]
  have h := hPg (chainBlockGradient profile tau q c (Fin.last n) (frameAnalysis hW z))
  change P (sourceTransport hU hV profile tau q c z) = sourceTransport hU hV profile tau q c z at h
  rw [hfix] at h
  exact h

/-- Complete source saddle-point statement in the actual orthogonal block
ordering: unique active fixed point, all coordinate bounds, active norm bound,
and zero inactive component of the unique ambient scalar saddle zero. -/
theorem saddlepoint_source (profile : GateProfile) {tau lam c : ℝ}
    (htau : 0 < tau) (hlam : 0 < lam) (hc : 0 ≤ c) :
    let hW := blockPairedFrame_orthonormal hU hV
    let phi := minimaxHardPotential profile tau lam (balancedQ n) c hU hV
    let T := fun r => frameAnalysis hW (euclideanSaddleSign dx dy (frameSynthesis hW
      (chainBlockGradient profile tau (balancedQ n) c (Fin.last n) r)))
    ∃ zstar : SaddleSpace dx dy,
      scalarSaddleOperator phi zstar = 0 ∧
      (∀ z, scalarSaddleOperator phi z = 0 → z = zstar) ∧
      frameSynthesis hW (frameAnalysis hW zstar) = zstar ∧
      (∀ i : Fin (n + 1),
        |pairedA U V i zstar| ≤ c + 2 * (n + 1 : ℝ) * tau ∧
        |pairedB U V i zstar| ≤ c + 2 * (n + 1 : ℝ) * tau) ∧
      ‖frameAnalysis hW zstar‖ ≤ Real.sqrt (2 * (n + 1 : ℝ)) * (c + 2 * (n + 1 : ℝ) * tau) ∧
      T (frameAnalysis hW zstar) = frameAnalysis hW zstar ∧
      (∀ r, T r = r → r = frameAnalysis hW zstar) := by
  let hW := blockPairedFrame_orthonormal hU hV
  let phi := minimaxHardPotential profile tau lam (balancedQ n) c hU hV
  let T := fun r => frameAnalysis hW (euclideanSaddleSign dx dy (frameSynthesis hW
      (chainBlockGradient profile tau (balancedQ n) c (Fin.last n) r)))
  have hq0 := balancedQ_nonneg n
  have hq1 := balancedQ_le_one n
  have hqlt : balancedQ n < 1 := by
    unfold balancedQ
    have hd : (0 : ℝ) < 1 / (4 * (n + 1 : ℝ)) := by positivity
    linarith
  obtain ⟨zstar, hzero, huniq⟩ := framedHardPotential_exists_unique_zero profile (c := c)
    htau.ne' hq0 hqlt hlam (euclideanSaddleSign dx dy) (euclideanSaddleSign_involutive dx dy) hW (Fin.last n)
  have hz0 : scalarSaddleOperator phi zstar = 0 := hzero
  have hfix := source_zero_is_fixed hU hV profile htau.ne' hlam zstar hz0
  refine ⟨zstar, hz0, huniq, source_fixed_projection_identity hU hV profile tau (balancedQ n) c zstar hfix,
    source_fixed_coordinate_bounds hU hV profile htau hq0 hq1 hc zstar hfix,
    (frameAnalysis_norm_le hW zstar).trans (source_fixed_norm_bound hU hV profile htau hq0 hq1 hc zstar hfix), ?_, ?_⟩
  · change frameAnalysis hW (sourceTransport hU hV profile tau (balancedQ n) c zstar) = frameAnalysis hW zstar
    rw [hfix]
  · intro r hr
    let z := euclideanSaddleSign dx dy (frameSynthesis hW
      (chainBlockGradient profile tau (balancedQ n) c (Fin.last n) r))
    have hAz : frameAnalysis hW z = r := hr
    have hzfix : sourceTransport hU hV profile tau (balancedQ n) c z = z := by
      change euclideanSaddleSign dx dy (frameSynthesis hW
        (chainBlockGradient profile tau (balancedQ n) c (Fin.last n) (frameAnalysis hW z))) = z
      rw [hAz]
    have hz : scalarSaddleOperator phi z = 0 := by
      change euclideanSaddleSign dx dy (gradient phi z) = 0
      rw [minimaxHardPotential_saddle_operator profile htau.ne' lam (balancedQ n) c hU hV]
      change lam • (z - sourceTransport hU hV profile tau (balancedQ n) c z) = 0
      rw [hzfix]
      simp
    have hzz := huniq z hz
    exact hAz.symm.trans (congrArg (frameAnalysis hW) hzz)

end Saddle

end MinimaxAudit
