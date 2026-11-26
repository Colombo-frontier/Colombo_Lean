import FreshGradientMinimax.RawTruncatedModel
import FreshGradientMinimax.PrimalNextLocality

/-! A static index calculated from exposed linear reads, including arbitrary
nonisometric reads. On the good event it equals the original static index. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory

theorem thresholdStageIndex_congr_prefix {n k : ℕ} (r : ℝ)
    (u u' : Fin (n + 1) → ℝ) (v v' : Fin (n + 1) → Bool → ℝ)
    (hk : thresholdStage r u v ≤ k) (hk' : thresholdStage r u' v' ≤ k)
    (hu : ∀ i, i.val ≤ k → u i = u' i)
    (hv : ∀ i, i.val ≤ k → ∀ b, v i b = v' i b) :
    thresholdStageIndex r u v = thresholdStageIndex r u' v' := by
  have he : thresholdActive r u v = thresholdActive r u' v' := by
    funext i
    apply propext
    by_cases hi : i.val ≤ k
    · simp only [thresholdActive, hu i hi, hv i hi]
    · have h : k < i.val := Nat.lt_of_not_ge hi
      exact iff_of_false (inactive_above_staticStage _ i (lt_of_le_of_lt hk h))
        (inactive_above_staticStage _ i (lt_of_le_of_lt hk' h))
  apply Fin.ext
  change staticStage n (thresholdActive r u v) = staticStage n (thresholdActive r u' v')
  rw [he]

def linearDualStageCoordinates {n dy : ℕ} (B : Euclid dy →L[ℝ] Euclid (n + n))
    (y : Euclid dy) : Fin (n + 1) → Bool → ℝ :=
  Fin.cases (fun _ => 0) (fun e b => if b then B y (e.castAdd n) else B y (e.natAdd n))

theorem linearDualStageCoordinates_continuous {n dy : ℕ}
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (i : Fin (n + 1)) (b : Bool) :
    Continuous (fun y => linearDualStageCoordinates B y i b) := by
  refine Fin.cases ?_ (fun e => ?_) i
  · exact continuous_const
  · cases b
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (e.natAdd n)).continuous.comp B.continuous
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (e.castAdd n)).continuous.comp B.continuous

theorem linearDualStageCoordinates_prefix {n dy : ℕ} (j : ℕ)
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (y : Euclid dy) (i : Fin (n + 1)) (b : Bool) :
    linearDualStageCoordinates (dualPrefixRead j B) y i b =
      if i.val < j then linearDualStageCoordinates B y i b else 0 := by
  refine Fin.cases ?_ (fun e => ?_) i
  · simp only [linearDualStageCoordinates, Fin.cases_zero]
    split_ifs <;> rfl
  · cases b <;>
      simp only [linearDualStageCoordinates, Fin.cases_succ, Bool.false_eq_true,
        if_false, if_true, dualPrefixRead, ContinuousLinearMap.comp_apply,
        coordinateMultiplier_apply, coreLinkPrefix, Fin.addCases_left, Fin.addCases_right,
        Fin.val_succ] <;> split_ifs <;> simp only [one_mul, zero_mul]

theorem linearCompressedCoordinates_prefix {m dx : ℕ} (j : ℕ)
    (A : Euclid dx →L[ℝ] Euclid m) (r R : ℝ) (x : Euclid dx) (i : Fin m) :
    linearCompressedCoordinates (primalPrefixRead j A) r R x i =
      if i.val < j then linearCompressedCoordinates A r R x i else 0 := by
  simp only [linearCompressedCoordinates, primalPrefixRead, ContinuousLinearMap.comp_apply,
    PiLp.smul_apply, corePrimalPrefix_apply, smul_eq_mul]
  split_ifs <;> simp only [mul_zero]

def rawStaticIndex {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R : ℝ) (k : ℕ) (z : Joint dx dy) : Fin (n + 1) :=
  thresholdStageIndex r (fun i => linearCompressedCoordinates (primalPrefixRead (k + 1) A) r R z.1 i)
    (linearDualStageCoordinates (dualPrefixRead (k + 1) B) z.2)

theorem rawStaticIndex_le {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) {r : ℝ} (hr : 0 ≤ r) (R : ℝ) (k : ℕ) (z : Joint dx dy) :
    (rawStaticIndex A B r R k z).val ≤ k := by
  apply thresholdStage_at_most
  intro i hi
  have h : ¬ i.val < k + 1 := by omega
  simp only [linearCompressedCoordinates_prefix, linearDualStageCoordinates_prefix, if_neg h, abs_zero]
  exact ⟨by norm_num, hr, hr⟩

theorem rawStaticIndex_measurable {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R : ℝ) (k : ℕ) : Measurable (rawStaticIndex A B r R k) := by
  apply thresholdStageIndex_measurable
  · intro i
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      ((linearCompressedCoordinates_contDiff _ r R (k := 1)).continuous.comp continuous_fst)).measurable
  · intro i b
    exact ((linearDualStageCoordinates_continuous _ i b).comp continuous_snd).measurable

theorem rawStaticIndex_congr {n dx dy k : ℕ}
    (A A' : Euclid dx →L[ℝ] Euclid (n + 1)) (B B' : Euclid dy →L[ℝ] Euclid (n + n))
    (r R : ℝ) (hA : primalPrefixRead (k + 1) A = primalPrefixRead (k + 1) A')
    (hB : dualPrefixRead (k + 1) B = dualPrefixRead (k + 1) B') :
    rawStaticIndex A B r R k = rawStaticIndex A' B' r R k := by
  unfold rawStaticIndex
  rw [hA, hB]

theorem rawStaticIndex_paper {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (k : ℕ) (z : Joint dx dy)
    (hu : ∀ i : Fin (n + 1), k < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4)
    (hy : ∀ e : Fin n, k ≤ e.val →
      |frameCoordinates V z.2 (e.castAdd n)| ≤ primalLengthScale L ε ∧
      |frameCoordinates V z.2 (e.natAdd n)| ≤ primalLengthScale L ε) :
    rawStaticIndex (frameCoordinates U) (frameCoordinates V) (primalLengthScale L ε)
      (primalCompressionRadius n L ε) k z = primalStaticIndex U V L ε z := by
  apply thresholdStageIndex_congr_prefix (k := k)
  · exact rawStaticIndex_le _ _ (primalLengthScale_pos hL hε).le _ k z
  · exact primalStaticIndex_le U V k z hu hy
  · intro i hi
    rw [linearCompressedCoordinates_prefix, if_pos (by omega)]
    rfl
  · intro i hi b
    rw [linearDualStageCoordinates_prefix, if_pos (by omega)]
    rfl

end FreshGradientMinimax
