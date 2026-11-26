import SecondOrder.FiniteMartingale

open scoped BigOperators InnerProductSpace

namespace SecondOrder

/-- The empirical mean of the queried components; labels may repeat. -/
noncomputable def batchMean {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : α → E) {B : ℕ} (samples : Fin B → α) : E :=
  (B : ℝ)⁻¹ • ∑ i, X (samples i)

section Algebra
variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem batchMean_add (X Y : α → E) {B : ℕ} (samples : Fin B → α) :
    batchMean (fun a => X a + Y a) samples = batchMean X samples + batchMean Y samples := by
  simp [batchMean, Finset.sum_add_distrib, smul_add]

theorem batchMean_sub (X Y : α → E) {B : ℕ} (samples : Fin B → α) :
    batchMean (fun a => X a - Y a) samples = batchMean X samples - batchMean Y samples := by
  simp [batchMean, Finset.sum_sub_distrib, smul_sub]

theorem batchMean_const (x : E) {B : ℕ} (hB : 0 < B) (samples : Fin B → α) :
    batchMean (fun _ => x) samples = x := by
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  simp [batchMean, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hB']

theorem batchMean_linearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →ₗ[ℝ] F) (X : α → E) {B : ℕ} (samples : Fin B → α) :
    batchMean (fun a => T (X a)) samples = T (batchMean X samples) := by
  simp only [batchMean, map_sum, map_smul]

theorem finiteMartingale_independent_sum (X : α → E) (t : ℕ) (samples : Fin t → α) :
    finiteMartingale (fun _ _ => X) t samples = ∑ i, X (samples i) := by
  induction t with
  | zero => simp [finiteMartingale]
  | succ t ih =>
    rw [finiteMartingale, Fin.sum_univ_castSucc, ih]
    rfl

end Algebra

section Probability
variable {α E : Type*} [Fintype α] [Nonempty α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem batchMean_center_martingale (X : α → E) {B : ℕ} (hB : 0 < B)
    (samples : Fin B → α) :
    batchMean X samples - uniformMean X =
      (B : ℝ)⁻¹ • finiteMartingale (fun _ _ a => X a - uniformMean X) B samples := by
  rw [finiteMartingale_independent_sum]
  change _ = batchMean (fun a => X a - uniformMean X) samples
  rw [batchMean_sub, batchMean_const _ hB]

/-- Fresh independent component labels give an unbiased empirical mean. -/
theorem batchMean_unbiased (X : α → E) {B : ℕ} (hB : 0 < B) :
    uniformMean (fun samples : Fin B → α => batchMean X samples) = uniformMean X := by
  have hzero : ∀ (t : ℕ) (past : Fin t → α),
      uniformMean (fun a => X a - uniformMean X) = 0 := fun _ _ => pmfMean_center _ _
  have h := finiteMartingale_mean_zero (fun _ _ a => X a - uniformMean X) hzero B
  have hc : uniformMean (fun samples : Fin B → α => batchMean X samples - uniformMean X) = 0 := by
    simp only [batchMean_center_martingale X hB, uniformMean_smul, h, smul_zero]
  rw [uniformMean_sub, uniformMean_const, sub_eq_zero] at hc
  exact hc

/-- The second moment of a centered sum is the sum of the component variances. -/
theorem independent_sum_second_moment (X : α → E) (hX : uniformMean X = 0) (t : ℕ) :
    uniformMean (fun samples : Fin t → α => ‖∑ i, X (samples i)‖ ^ 2) =
      (t : ℝ) * uniformMean (fun a => ‖X a‖ ^ 2) := by
  have hzero : ∀ (t : ℕ) (past : Fin t → α), uniformMean ((fun _ _ => X) t past) = 0 :=
    fun _ _ => hX
  have hm (t : ℕ) :
      uniformMean (fun samples => ‖finiteMartingale (fun _ _ => X) t samples‖ ^ 2) =
        (t : ℝ) * uniformMean (fun a => ‖X a‖ ^ 2) := by
    induction t with
    | zero => simp [finiteMartingale]
    | succ t ih =>
      rw [finiteMartingale_second_moment_succ _ hzero, ih, uniformMean_const, Nat.cast_add,
        Nat.cast_one]
      ring
  simpa only [finiteMartingale_independent_sum] using hm t

/-- Exact finite-batch variance, including the cancellation of all cross terms. -/
theorem batchMean_variance (X : α → E) {B : ℕ} (hB : 0 < B) :
    uniformMean (fun samples : Fin B → α => ‖batchMean X samples - uniformMean X‖ ^ 2) =
      uniformMean (fun a => ‖X a - uniformMean X‖ ^ 2) / B := by
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  simp only [batchMean_center_martingale X hB, finiteMartingale_independent_sum,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (show (0 : ℝ) ≤ B from Nat.cast_nonneg B), mul_pow,
    uniformMean_mul]
  have hc : uniformMean (fun a => X a - uniformMean X) = 0 := pmfMean_center _ _
  rw [independent_sum_second_moment (fun a => X a - uniformMean X) hc B]
  field_simp
  ring

theorem batchMean_variance_le (X : α → E) {B : ℕ} (hB : 0 < B)
    (V : ℝ) (hV : uniformMean (fun a => ‖X a‖ ^ 2) ≤ V) :
    uniformMean (fun samples : Fin B → α => ‖batchMean X samples - uniformMean X‖ ^ 2) ≤ V / B := by
  rw [batchMean_variance X hB]
  exact div_le_div_of_nonneg_right ((pmfMean_variance_le _ X).trans hV) (Nat.cast_nonneg _)

theorem batchMean_bounded_variance (X : α → E) {B : ℕ} (hB : 0 < B)
    (K : ℝ) (hX : ∀ a, ‖X a‖ ≤ K) :
    uniformMean (fun samples : Fin B → α => ‖batchMean X samples - uniformMean X‖ ^ 2) ≤ K ^ 2 / B :=
  batchMean_variance_le X hB _ (uniformMean_le_const _
    (fun a => pow_le_pow_left₀ (norm_nonneg _) (hX a) 2))

theorem batchMean_mean_error (X : α → E) {B : ℕ} (hB : 0 < B)
    (K : ℝ) (hK : 0 ≤ K) (hX : ∀ a, ‖X a‖ ≤ K) :
    uniformMean (fun samples : Fin B → α => ‖batchMean X samples - uniformMean X‖) ≤
      K / Real.sqrt B := by
  calc
    _ ≤ Real.sqrt (uniformMean (fun samples : Fin B → α =>
        ‖batchMean X samples - uniformMean X‖ ^ 2)) := pmfMean_norm_le_sqrt _ _
    _ ≤ Real.sqrt (K ^ 2 / B) := Real.sqrt_le_sqrt (batchMean_bounded_variance X hB K hX)
    _ = _ := by rw [Real.sqrt_div (sq_nonneg K), Real.sqrt_sq hK]

end Probability

end SecondOrder

