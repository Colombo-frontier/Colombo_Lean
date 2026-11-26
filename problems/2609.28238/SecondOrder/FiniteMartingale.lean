import SecondOrder.FiniteMean

open scoped BigOperators InnerProductSpace

namespace SecondOrder

/-- Accumulate innovations on the actual tree of finite sampling histories.
The increment at time `t` may use the whole past, but only one fresh label. -/
def finiteMartingale {α E : Type*} [AddZeroClass E]
    (step : (t : ℕ) → (Fin t → α) → α → E) : (t : ℕ) → (Fin t → α) → E
  | 0, _ => 0
  | t + 1, samples => finiteMartingale step t (Fin.init samples) +
      step t (Fin.init samples) (samples (Fin.last t))

@[simp] theorem finiteMartingale_zero {α E : Type*} [AddZeroClass E]
    (step : (t : ℕ) → (Fin t → α) → α → E) (samples : Fin 0 → α) :
    finiteMartingale step 0 samples = 0 := rfl

@[simp] theorem finiteMartingale_snoc {α E : Type*} [AddZeroClass E]
    (step : (t : ℕ) → (Fin t → α) → α → E) (t : ℕ) (past : Fin t → α) (a : α) :
    finiteMartingale step (t + 1) (Fin.snoc past a) =
      finiteMartingale step t past + step t past a := by
  simp [finiteMartingale]

section Moments
variable {α E : Type*} [Fintype α] [Nonempty α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (step : (t : ℕ) → (Fin t → α) → α → E)
  (hzero : ∀ t past, uniformMean (step t past) = 0)

include hzero

/-- Adaptive sampling is unbiased because every conditional increment has mean zero. -/
theorem finiteMartingale_mean_zero (t : ℕ) :
    uniformMean (finiteMartingale step t) = 0 := by
  induction t with
  | zero => simp [uniformMean, finiteMartingale]
  | succ t ih =>
    rw [uniformMean_snoc]
    simp only [finiteMartingale_snoc, uniformMean_add, uniformMean_const, hzero, add_zero]
    exact ih

/-- Orthogonality of a fresh mean-zero increment to the whole preceding history. -/
theorem finiteMartingale_second_moment_succ (t : ℕ) :
    uniformMean (fun samples => ‖finiteMartingale step (t + 1) samples‖ ^ 2) =
      uniformMean (fun past => ‖finiteMartingale step t past‖ ^ 2) +
        uniformMean (fun past : Fin t → α => uniformMean (fun a => ‖step t past a‖ ^ 2)) := by
  rw [uniformMean_snoc]
  simp only [finiteMartingale_snoc]
  have h (past : Fin t → α) :
      uniformMean (fun a => ‖finiteMartingale step t past + step t past a‖ ^ 2) =
        ‖finiteMartingale step t past‖ ^ 2 + uniformMean (fun a => ‖step t past a‖ ^ 2) := by
    rw [uniformMean, pmfMean_norm_add_sq]
    change _ + 2 * ⟪_, uniformMean (step t past)⟫_ℝ + _ = _
    simp only [hzero, inner_zero_right, mul_zero, add_zero]
    rfl
  simp only [h, uniformMean_add]

/-- Dimension-free second-moment bound for the finite adaptive sample tree. -/
theorem finiteMartingale_second_moment_le_upto (v : ℕ → ℝ) (T : ℕ)
    (hv : ∀ t < T, ∀ past, uniformMean (fun a => ‖step t past a‖ ^ 2) ≤ v t) :
    uniformMean (fun samples => ‖finiteMartingale step T samples‖ ^ 2) ≤
      ∑ j ∈ Finset.range T, v j := by
  induction T with
  | zero => simp [finiteMartingale]
  | succ t ih =>
    rw [finiteMartingale_second_moment_succ step hzero, Finset.sum_range_succ]
    exact add_le_add (ih (fun j hj => hv j (by omega)))
      (uniformMean_le_const (v t) (hv t (by omega)))

theorem finiteMartingale_second_moment_le (v : ℕ → ℝ)
    (hv : ∀ t past, uniformMean (fun a => ‖step t past a‖ ^ 2) ≤ v t) (t : ℕ) :
    uniformMean (fun samples => ‖finiteMartingale step t samples‖ ^ 2) ≤
      ∑ j ∈ Finset.range t, v j :=
  finiteMartingale_second_moment_le_upto step hzero v t (fun j _ => hv j)

theorem finiteMartingale_mean_norm_le (v : ℕ → ℝ)
    (hv : ∀ t past, uniformMean (fun a => ‖step t past a‖ ^ 2) ≤ v t) (t : ℕ) :
    uniformMean (fun samples => ‖finiteMartingale step t samples‖) ≤
      Real.sqrt (∑ j ∈ Finset.range t, v j) := by
  exact (pmfMean_norm_le_sqrt _ _).trans
    (Real.sqrt_le_sqrt (finiteMartingale_second_moment_le step hzero v hv t))

theorem finiteMartingale_bounded_second_moment (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t past a, ‖step t past a‖ ≤ K) (t : ℕ) :
    uniformMean (fun samples => ‖finiteMartingale step t samples‖ ^ 2) ≤ (t : ℝ) * K ^ 2 := by
  have h := finiteMartingale_second_moment_le step hzero (fun _ => K ^ 2)
    (fun t past => uniformMean_le_const _ (fun a =>
      (pow_le_pow_left₀ (norm_nonneg _) (hbound t past a) 2))) t
  simpa using h

theorem finiteMartingale_bounded_mean_norm (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t past a, ‖step t past a‖ ≤ K) (t : ℕ) :
    uniformMean (fun samples => ‖finiteMartingale step t samples‖) ≤ Real.sqrt t * K := by
  calc
    _ ≤ Real.sqrt (uniformMean (fun samples => ‖finiteMartingale step t samples‖ ^ 2)) :=
      pmfMean_norm_le_sqrt _ _
    _ ≤ Real.sqrt ((t : ℝ) * K ^ 2) :=
      Real.sqrt_le_sqrt (finiteMartingale_bounded_second_moment step hzero K hK hbound t)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hK]

end Moments

end SecondOrder

