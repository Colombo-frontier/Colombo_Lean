import FreshGradientMinimax.AcceleratedPrimalGradient

/-! The explicit actual gradient of the ideal clipped value J in (36).
Its quadratic links form disjoint pairs before clipping. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def acceleratedIdealPairGradient (x : Euclid 2) : Euclid 2 :=
  (WithLp.equiv 2 _).symm ![12 * (x 0 - x 1 / 2), -6 * (x 0 - x 1 / 2)]

theorem acceleratedIdealPair_hasFDerivAt (x : Euclid 2) :
    HasFDerivAt (fun y : Euclid 2 => 6 * (y 0 - y 1 / 2) ^ 2)
      (innerSL ℝ (acceleratedIdealPairGradient x)) x := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := x)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := x)
  have h := ((hasDerivAt_pow 2 (x 0 - (1 / 2 : ℝ) * x 1)).comp_hasFDerivAt x
    (h0.sub (h1.const_mul (1 / 2 : ℝ)))).const_mul 6
  have he : (fun y : Euclid 2 => 6 * (y 0 - y 1 / 2) ^ 2) =
      (fun y => 6 * (y 0 - (1 / 2 : ℝ) * y 1) ^ 2) := by
    funext y
    ring
  rw [he]
  apply h.congr_fderiv
  ext v
  simp [acceleratedIdealPairGradient, innerSL_apply, PiLp.inner_apply, RCLike.inner_apply',
    Fin.sum_univ_two, EuclideanSpace.proj]
  ring

def acceleratedIdealEnergyGradient {k : ℕ} (q : Euclid (k * 2 + 1)) : Euclid (k * 2 + 1) :=
  pathPadLeft (k * 2) (euclidJoin (fun i => acceleratedIdealPairGradient (euclidBlock i (euclidDropLast (k * 2) q))))

theorem acceleratedIdealEnergy_hasFDerivAt {k : ℕ} (q : Euclid (k * 2 + 1)) :
    HasFDerivAt (fun u : Euclid (k * 2 + 1) => 6 * ∑ i : Fin k, (u (interleavedX i) - u (interleavedZ i) / 2) ^ 2)
      (innerSL ℝ (acceleratedIdealEnergyGradient q)) q := by
  have h := (block_function_hasFDerivAt acceleratedIdealPair_hasFDerivAt (euclidDropLast (k * 2) q)).comp q
    (euclidDropLast (k * 2)).hasFDerivAt
  simp only [Function.comp_def, euclidBlock_apply, euclidDropLast_apply] at h
  simp only [Finset.mul_sum, interleavedX, interleavedZ]
  apply h.congr_fderiv
  ext v
  simp [acceleratedIdealEnergyGradient, ← euclidDropLast_adjoint, ContinuousLinearMap.adjoint_inner_left, innerSL_apply]

def acceleratedIdealGradient {k : ℕ} (u : Euclid (k * 2 + 1)) : Euclid (k * 2 + 1) :=
  weightedClipGradient 2 (acceleratedNonlinearGradient (clipVector 2 u) + acceleratedIdealEnergyGradient (clipVector 2 u)) u

theorem acceleratedIdealValue_hasFDerivAt {k : ℕ} (u : Euclid (k * 2 + 1)) :
    HasFDerivAt acceleratedIdealValue (innerSL ℝ (acceleratedIdealGradient u)) u := by
  have h := (acceleratedNonlinear_hasFDerivAt (clipVector 2 u)).add (acceleratedIdealEnergy_hasFDerivAt (clipVector 2 u))
  have h' : HasFDerivAt (fun q : Euclid (k * 2 + 1) => acceleratedNonlinear q +
      6 * ∑ i : Fin k, (q (interleavedX i) - q (interleavedZ i) / 2) ^ 2)
      (innerSL ℝ (acceleratedNonlinearGradient (clipVector 2 u) + acceleratedIdealEnergyGradient (clipVector 2 u))) (clipVector 2 u) := by
    apply h.congr_fderiv
    ext v
    simp [innerSL_apply, inner_add_left]
  exact clipped_scalar_hasFDerivAt (by norm_num : (0 : ℝ) < 2) u _ h'

theorem acceleratedIdealValue_gradient_explicit {k : ℕ} (u : Euclid (k * 2 + 1)) :
    gradient acceleratedIdealValue u = acceleratedIdealGradient u :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedIdealValue_hasFDerivAt u)).gradient

theorem acceleratedIdealEnergyGradient_x {k : ℕ} (q : Euclid (k * 2 + 1)) (i : Fin k) :
    acceleratedIdealEnergyGradient q (interleavedX i) = 12 * (q (interleavedX i) - q (interleavedZ i) / 2) := by
  simp only [acceleratedIdealEnergyGradient, interleavedX, interleavedZ, pathPadLeft_apply,
    Fin.snoc_castSucc, euclidJoin_apply]
  simp only [acceleratedIdealPairGradient,
    euclidBlock_apply, euclidDropLast_apply]
  rfl

theorem acceleratedIdealEnergyGradient_z {k : ℕ} (q : Euclid (k * 2 + 1)) (i : Fin k) :
    acceleratedIdealEnergyGradient q (interleavedZ i) = -6 * (q (interleavedX i) - q (interleavedZ i) / 2) := by
  simp only [acceleratedIdealEnergyGradient, interleavedX, interleavedZ, pathPadLeft_apply,
    Fin.snoc_castSucc, euclidJoin_apply]
  simp only [acceleratedIdealPairGradient,
    euclidBlock_apply, euclidDropLast_apply]
  rfl

theorem acceleratedNonlinearGradient_z {k : ℕ} (q : Euclid (k * 2 + 1)) (i : Fin k) :
    acceleratedNonlinearGradient q (interleavedZ i) = coreLinkTermD1 (q (interleavedZ i)) (q (interleavedNextX i)) := by
  rw [interleavedZ_eq_succ, acceleratedNonlinearGradient_succ, acceleratedNonlinearTail, euclidJoin_apply]
  rw [corePairGradient_zero, euclidDropFirst_block_zero, euclidDropFirst_block_one, ← interleavedZ_eq_succ]

theorem acceleratedNonlinearGradient_nextX {k : ℕ} (q : Euclid (k * 2 + 1)) (i : Fin k) :
    acceleratedNonlinearGradient q (interleavedNextX i) = coreLinkTermD2 (q (interleavedZ i)) (q (interleavedNextX i)) := by
  rw [interleavedNextX, acceleratedNonlinearGradient_succ, acceleratedNonlinearTail, euclidJoin_apply]
  rw [corePairGradient_one, euclidDropFirst_block_zero, euclidDropFirst_block_one]
  rfl

theorem acceleratedIdealGradient_x {k : ℕ} (u : Euclid (k * 2 + 1)) (i : Fin k) :
    acceleratedIdealGradient u (interleavedX i) = smoothClipSlope 2 (u (interleavedX i)) *
      (acceleratedNonlinearGradient (clipVector 2 u) (interleavedX i) +
        12 * (smoothClip 2 (u (interleavedX i)) - smoothClip 2 (u (interleavedZ i)) / 2)) := by
  change smoothClipSlope 2 (u (interleavedX i)) *
    (acceleratedNonlinearGradient (clipVector 2 u) (interleavedX i) + acceleratedIdealEnergyGradient (clipVector 2 u) (interleavedX i)) = _
  rw [acceleratedIdealEnergyGradient_x]
  rfl

theorem acceleratedIdealGradient_z {k : ℕ} (u : Euclid (k * 2 + 1)) (i : Fin k) :
    acceleratedIdealGradient u (interleavedZ i) = smoothClipSlope 2 (u (interleavedZ i)) *
      (coreLinkTermD1 (smoothClip 2 (u (interleavedZ i))) (smoothClip 2 (u (interleavedNextX i))) -
        6 * (smoothClip 2 (u (interleavedX i)) - smoothClip 2 (u (interleavedZ i)) / 2)) := by
  change smoothClipSlope 2 (u (interleavedZ i)) *
    (acceleratedNonlinearGradient (clipVector 2 u) (interleavedZ i) + acceleratedIdealEnergyGradient (clipVector 2 u) (interleavedZ i)) = _
  rw [acceleratedNonlinearGradient_z, acceleratedIdealEnergyGradient_z]
  simp only [clipVector_apply]
  ring

end FreshGradientMinimax

