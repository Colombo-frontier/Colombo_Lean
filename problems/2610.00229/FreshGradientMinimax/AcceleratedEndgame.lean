import FreshGradientMinimax.AcceleratedEndgamePair
import FreshGradientMinimax.AcceleratedCompressedValue
import FreshGradientMinimax.CompressedRidgeFactor

/-! Lemma E.2 for the actual supremum of the ambient normalized objective.
No norm bound is imposed on the output point. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {n k dx dy : ℕ}
  (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx)
  (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)

theorem acceleratedCompressedValueGradient_small (hn : 10 ≤ n + 2) (hk : 0 < k)
    (x : Euclid dx) (hx : ‖x‖ ≤ acceleratedPrimalRadius k / 2)
    (hex : ∃ i : Fin k, |compressedCoordinates U 1 (acceleratedPrimalRadius k) x (interleavedZ i)| < 1) :
    primalRidgeConstant / 2 ≤ ‖acceleratedCompressedValueGradient U V (acceleratedThreshold n k) x‖ := by
  let R := acceleratedPrimalRadius k
  let u := compressedCoordinates U 1 R x
  let g := gradient (framedAcceleratedValue V (acceleratedThreshold n k)) u
  let G := radialCompressionDerivative R x (U g) + primalRidgeConstant • x
  let a := compressionFactor (R⁻¹ • x)
  let b := compressedRidgeFactor U R primalRidgeConstant x g
  have hR : 0 < R := acceleratedPrimalRadius_pos k
  obtain ⟨i, hz, hprev⟩ := accelerated_first_small_z u hex
  let p := acceleratedNonlinearGradient (clipVector 2 u) (interleavedX i)
  let q := coreLinkTermD1 (u (interleavedZ i)) (smoothClip 2 (u (interleavedNextX i)))
  let ev := g (interleavedX i) - acceleratedIdealGradient u (interleavedX i)
  let ez := g (interleavedZ i) - acceleratedIdealGradient u (interleavedZ i)
  have ha : 4 / 5 ≤ a := compressionFactor_lower_half_ball hR x hx
  have ha1 : a ≤ 1 := compressionFactor_le_one _
  have hb := acceleratedRidgeFactor_bounds U x g hx
    (framedAcceleratedValue_gradient_bound V hn (acceleratedThreshold_pos n hk).le u)
  have hp := acceleratedNonlinearGradient_x_sign (clipVector 2 u) i
  have hps : |u (interleavedX i)| < 1 → p ≤ -primalBarrierConstant :=
    acceleratedNonlinearGradient_x_barrier u i hprev
  have hq : q ≤ 0 := coreLinkTermD1_nonpos _ _
  have he : ‖g - acceleratedIdealGradient u‖ ≤ primalRidgeConstant / 100 := by
    have h := framedAcceleratedValue_gradient_comparison V hn hk u
    rw [acceleratedIdealValue_gradient_explicit] at h
    exact h
  have hev : |ev| ≤ primalRidgeConstant / 100 :=
    (euclid_coordinate_abs_le (g - acceleratedIdealGradient u) (interleavedX i)).trans he
  have hez : |ez| ≤ primalRidgeConstant / 100 :=
    (euclid_coordinate_abs_le (g - acceleratedIdealGradient u) (interleavedZ i)).trans he
  have hJx := acceleratedIdealGradient_x u i
  rw [smoothClip_identity (by norm_num : (0 : ℝ) < 2) (show |u (interleavedZ i)| ≤ 2 by linarith only [hz])] at hJx
  have hJz := acceleratedIdealGradient_z_small u i hz
  have hgv : frameCoordinates U G (interleavedX i) =
      a * (smoothClipSlope 2 (u (interleavedX i)) * (p + 12 * (smoothClip 2 (u (interleavedX i)) - u (interleavedZ i) / 2)) + ev) + b * u (interleavedX i) := by
    rw [compressedRidgeFactor_coordinate U hR]
    change a * g (interleavedX i) + b * u (interleavedX i) = _
    dsimp only [ev, p]
    rw [hJx]
    ring
  have hgz : frameCoordinates U G (interleavedZ i) =
      a * (q - 6 * (smoothClip 2 (u (interleavedX i)) - u (interleavedZ i) / 2) + ez) + b * u (interleavedZ i) := by
    rw [compressedRidgeFactor_coordinate U hR]
    change a * g (interleavedZ i) + b * u (interleavedZ i) = _
    dsimp only [ez, q]
    rw [hJz]
    ring
  have h := accelerated_scalar_endgame ha ha1 hb.1 hb.2 hz hp.1 hp.2 hq hps hev hez hgv hgz
  have hcoord (j : Fin (k * 2 + 1)) : |frameCoordinates U G j| ≤ ‖G‖ :=
    (euclid_coordinate_abs_le (frameCoordinates U G) j).trans (frameCoordinates_norm_bound U G)
  rcases h with h | h
  · exact h.trans (hcoord (interleavedX i))
  · exact h.trans (hcoord (interleavedZ i))

theorem acceleratedCompressedValueGradient_barrier (hn : 10 ≤ n + 2) (hk : 0 < k)
    (x : Euclid dx)
    (hex : ∃ i : Fin k, |compressedCoordinates U 1 (acceleratedPrimalRadius k) x (interleavedZ i)| < 1) :
    primalRidgeConstant / 2 ≤ ‖acceleratedCompressedValueGradient U V (acceleratedThreshold n k) x‖ := by
  by_cases hx : ‖x‖ ≤ acceleratedPrimalRadius k / 2
  · exact acceleratedCompressedValueGradient_small U V hn hk x hx hex
  · exact (acceleratedCompressedValueGradient_large U V hn (acceleratedThreshold_pos n hk).le x (lt_of_not_ge hx)).le

theorem lemma_E2 (hn : 10 ≤ n + 2) (hk : 0 < k) (x : Euclid dx)
    (hlast : |compressedCoordinates U 1 (acceleratedPrimalRadius k) x
      (interleavedZ (⟨k - 1, by omega⟩ : Fin k))| ≤ 1 / 4) :
    primalRidgeConstant / 2 ≤
      ‖gradient (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le).value x‖ := by
  rw [NCObjective.true_primal_gradient, acceleratedCompressedModel_primalGradient]
  apply acceleratedCompressedValueGradient_barrier U V hn hk x
  exact ⟨⟨k - 1, by omega⟩, by linarith only [hlast]⟩

end FreshGradientMinimax

