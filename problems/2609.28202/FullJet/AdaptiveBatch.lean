import FullJet.FiniteBatch

open scoped BigOperators

namespace FullJet

section Definitions
variable {α E : Type*} [Fintype α] [Nonempty α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {B : ℕ}

/-- Within a batch, the component function is fixed before any batch label is read. -/
noncomputable def centeredBatchIncrement
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E)
    (t : ℕ) (past : Fin t → Fin B → α) (samples : Fin B → α) : E :=
  batchMean (X t past) samples - uniformMean (X t past)

/-- Actual accumulated sampling error with adaptive choices between batches. -/
noncomputable def adaptiveBatchError
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E)
    (t : ℕ) (samples : Fin t → Fin B → α) : E :=
  finiteMartingale (centeredBatchIncrement X) t samples

@[simp] theorem adaptiveBatchError_zero
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E) (samples : Fin 0 → Fin B → α) :
    adaptiveBatchError X 0 samples = 0 := rfl

@[simp] theorem adaptiveBatchError_snoc
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E)
    (t : ℕ) (past : Fin t → Fin B → α) (samples : Fin B → α) :
    adaptiveBatchError X (t + 1) (Fin.snoc past samples) =
      adaptiveBatchError X t past + (batchMean (X t past) samples - uniformMean (X t past)) := by
  simp [adaptiveBatchError, centeredBatchIncrement]

end Definitions

section Moments
variable {α E : Type*} [Fintype α] [Nonempty α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {B : ℕ}
  (X : (t : ℕ) → (Fin t → Fin B → α) → α → E) (hB : 0 < B)

include hB

theorem centeredBatchIncrement_mean_zero (t : ℕ) (past : Fin t → Fin B → α) :
    uniformMean (centeredBatchIncrement X t past) = 0 := by
  change uniformMean (fun samples => batchMean (X t past) samples - uniformMean (X t past)) = 0
  rw [uniformMean_sub, batchMean_unbiased _ hB, uniformMean_const, sub_self]

theorem adaptiveBatchError_mean_zero (t : ℕ) :
    uniformMean (adaptiveBatchError X t) = 0 :=
  finiteMartingale_mean_zero _ (centeredBatchIncrement_mean_zero X hB) t

theorem adaptiveBatchError_bounded_second_moment_upto (K : ℝ) (T : ℕ)
    (hK : ∀ t < T, ∀ past a, ‖X t past a‖ ≤ K) :
    uniformMean (fun samples => ‖adaptiveBatchError X T samples‖ ^ 2) ≤
      (T : ℝ) * K ^ 2 / B := by
  have h := finiteMartingale_second_moment_le_upto (centeredBatchIncrement X)
    (centeredBatchIncrement_mean_zero X hB) (fun _ => K ^ 2 / B) T
    (fun t ht past => batchMean_bounded_variance (X t past) hB K (hK t ht past))
  simpa only [adaptiveBatchError, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_div_assoc] using h

theorem adaptiveBatchError_second_moment (V : ℕ → ℝ)
    (hV : ∀ t past, uniformMean (fun a => ‖X t past a‖ ^ 2) ≤ V t) (t : ℕ) :
    uniformMean (fun samples => ‖adaptiveBatchError X t samples‖ ^ 2) ≤
      (∑ j ∈ Finset.range t, V j) / B := by
  have h := finiteMartingale_second_moment_le (centeredBatchIncrement X)
    (centeredBatchIncrement_mean_zero X hB) (fun t => V t / B)
    (fun t past => batchMean_variance_le (X t past) hB (V t) (hV t past)) t
  simpa only [adaptiveBatchError, Finset.sum_div] using h

/-- The error grows with the number of batches and shrinks with their size;
the bound has no dimension-dependent factor. -/
theorem adaptiveBatchError_bounded_second_moment (K : ℝ)
    (hK : ∀ t past a, ‖X t past a‖ ≤ K) (t : ℕ) :
    uniformMean (fun samples => ‖adaptiveBatchError X t samples‖ ^ 2) ≤
      (t : ℝ) * K ^ 2 / B := by
  have h := adaptiveBatchError_second_moment X hB (fun _ => K ^ 2)
    (fun t past => uniformMean_le_const _
      (fun a => pow_le_pow_left₀ (norm_nonneg _) (hK t past a) 2)) t
  simpa using h

theorem adaptiveBatchError_mean_norm (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t past a, ‖X t past a‖ ≤ K) (t : ℕ) :
    uniformMean (fun samples => ‖adaptiveBatchError X t samples‖) ≤
      Real.sqrt t * K / Real.sqrt B := by
  calc
    _ ≤ Real.sqrt (uniformMean (fun samples => ‖adaptiveBatchError X t samples‖ ^ 2)) :=
      pmfMean_norm_le_sqrt _ _
    _ ≤ Real.sqrt ((t : ℝ) * K ^ 2 / B) :=
      Real.sqrt_le_sqrt (adaptiveBatchError_bounded_second_moment X hB K hbound t)
    _ = _ := by
      rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)),
        Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hK]

end Moments

end FullJet
