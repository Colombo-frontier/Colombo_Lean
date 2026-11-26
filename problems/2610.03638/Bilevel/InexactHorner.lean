import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

/-!
# Inexact Horner evaluation and martingale error accumulation

The stochastic errors are genuine `Lp E 2 μ` random variables. Their
orthogonality is derived from Mathlib's L2 conditional expectation and
past measurability. No independence of adaptive errors is assumed.
The deterministic Horner recurrence is implemented and its error is
unrolled into powers of a contractive linear map. The resulting actual
integral MSE is bounded by the sum of per-call mean-square errors.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Bilevel.InexactHorner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthogonal_sum_sq {ι : Type*} (s : Finset ι) (v : ι → E)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner (𝕜 := ℝ) (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hcross : inner (𝕜 := ℝ) (v a) (∑ i ∈ s, v i) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact horth a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.sum_insert ha, norm_add_sq_real, hcross,
      ih (fun i hi j hj hij => horth i (Finset.mem_insert_of_mem hi)
        j (Finset.mem_insert_of_mem hj) hij), Finset.sum_insert ha]
    ring

section Probability
variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [CompleteSpace E]

omit [CompleteSpace E] in
theorem norm_sq_eq_integral (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem condMean_zero_inner {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (fresh past : Lp E 2 μ)
    (hzero : (condExpL2 E ℝ hm fresh : Lp E 2 μ) = 0)
    (hpast : AEStronglyMeasurable[m] past μ) :
    inner (𝕜 := ℝ) fresh past = 0 := by
  have h := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm fresh past hpast
  rw [hzero, inner_zero_left] at h
  exact h.symm

theorem transformed_condMean_zero {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (T : E →L[ℝ] E) (fresh : Lp E 2 μ)
    (hzero : (condExpL2 E ℝ hm fresh : Lp E 2 μ) = 0) :
    (condExpL2 E ℝ hm (T.compLp fresh) : Lp E 2 μ) = 0 := by
  apply Lp.ext
  have hc := condExpL2_comp_continuousLinearMap (𝕜 := ℝ) (𝕜' := ℝ) hm T fresh
  rw [hzero] at hc
  have hz : T.compLp (0 : Lp E 2 μ) = 0 := (T.compLpₗ 2 μ).map_zero
  simpa only [hz] using hc

omit [CompleteSpace E] in
theorem transformed_past_measurable {m : MeasurableSpace Ω}
    (T : E →L[ℝ] E) (past : Lp E 2 μ) (hpast : AEStronglyMeasurable[m] past μ) :
    AEStronglyMeasurable[m] (T.compLp past) μ := by
  have hc : (T.compLp past : Ω → E) =ᵐ[μ] fun ω => T (past ω) := T.coeFn_compLp past
  exact (T.continuous.comp_aestronglyMeasurable hpast).congr hc.symm

/-- Conditional mean zero implies actual L2 orthogonality after any fixed
linear transformations. Earlier errors are measurable for the later past. -/
theorem transformed_errors_orthogonal
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0)
    (η : ℕ → Lp E 2 μ) (T : ℕ → E →L[ℝ] E)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (η i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (η j) : Lp E 2 μ) = 0)
    {i j : ℕ} (hij : i ≠ j) :
    inner (𝕜 := ℝ) ((T i).compLp (η i)) ((T j).compLp (η j)) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [real_inner_comm]
    exact condMean_zero_inner (hle j) _ _
      (transformed_condMean_zero (hle j) (T j) (η j) (centered j))
      (transformed_past_measurable (T i) (η i) (adapted i j h))
  · exact condMean_zero_inner (hle i) _ _
      (transformed_condMean_zero (hle i) (T i) (η i) (centered i))
      (transformed_past_measurable (T j) (η j) (adapted j i h))

/-- Exact variance accumulation: no independence of the adaptive errors is
assumed; their conditional mean-zero and past-measurability suffice. -/
theorem transformed_errors_variance
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0)
    (η : ℕ → Lp E 2 μ) (T : ℕ → E →L[ℝ] E)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (η i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (η j) : Lp E 2 μ) = 0)
    (s : Finset ℕ) :
    ‖∑ i ∈ s, (T i).compLp (η i)‖ ^ 2 = ∑ i ∈ s, ‖(T i).compLp (η i)‖ ^ 2 :=
  orthogonal_sum_sq s _ (fun _ _ _ _ hij =>
    transformed_errors_orthogonal past hle η T adapted centered hij)

theorem transformed_errors_mse
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0)
    (η : ℕ → Lp E 2 μ) (T : ℕ → E →L[ℝ] E)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (η i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (η j) : Lp E 2 μ) = 0)
    (contractive : ∀ i, ‖T i‖ ≤ 1) (s : Finset ℕ) :
    (∫ ω, ‖(∑ i ∈ s, (T i).compLp (η i) : Lp E 2 μ) ω‖ ^ 2 ∂μ) ≤
      ∑ i ∈ s, ∫ ω, ‖η i ω‖ ^ 2 ∂μ := by
  simp only [← norm_sq_eq_integral]
  rw [transformed_errors_variance past hle η T adapted centered]
  apply Finset.sum_le_sum
  intro i _
  have hn : ‖(T i).compLp (η i)‖ ≤ ‖η i‖ :=
    ((T i).norm_compLp_le (η i)).trans (by
      simpa using mul_le_mul_of_nonneg_right (contractive i) (norm_nonneg (η i)))
  nlinarith [norm_nonneg ((T i).compLp (η i)), norm_nonneg (η i)]

/-- The propagated Horner error has a sum-of-variances MSE bound. Powers are
ordered by the actual injection times, with the last error propagated zero times. -/
theorem horner_errors_mse
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0)
    (η : ℕ → Lp E 2 μ) (K : E →L[ℝ] E) (hK : ‖K‖ ≤ 1)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (η i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (η j) : Lp E 2 μ) = 0) (m : ℕ) :
    (∫ ω, ‖(∑ i ∈ Finset.range m, (K ^ (m - 1 - i)).compLp (η i) : Lp E 2 μ) ω‖ ^ 2 ∂μ) ≤
      ∑ i ∈ Finset.range m, ∫ ω, ‖η i ω‖ ^ 2 ∂μ := by
  apply transformed_errors_mse past hle η (fun i => K ^ (m - 1 - i)) adapted centered
  intro i
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  suffices ∀ n : ℕ, ‖(K ^ n) x‖ ≤ ‖x‖ by simpa using this (m - 1 - i)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact (K.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hK (norm_nonneg _)).trans
      (by simpa using ih))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem coe_sum_ae (f : ℕ → Lp E 2 μ) (s : Finset ℕ) :
    (fun ω => (∑ i ∈ s, f i : Lp E 2 μ) ω) =ᵐ[μ] fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero E 2 μ)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with ω hadd hsum
    simp only [hadd, Pi.add_apply, hsum, Finset.sum_insert ha]

end Probability

/-- Exact and inexact Horner computations, with `a n` the coefficient vector
inserted at step `n` and `η n` the error of that step's operator action. -/
def horner (K : E →L[ℝ] E) (a η : ℕ → E) : ℕ → E
  | 0 => 0
  | n + 1 => K (horner K a η n) + a n + η n

def accumulated (K : E →L[ℝ] E) (η : ℕ → E) : ℕ → E
  | 0 => 0
  | n + 1 => K (accumulated K η n) + η n

theorem horner_difference (K : E →L[ℝ] E) (a η : ℕ → E) (n : ℕ) :
    horner K a η n - horner K a (fun _ => 0) n = accumulated K η n := by
  induction n with
  | zero => simp [horner, accumulated]
  | succ n ih =>
    simp only [horner, accumulated, ← ih, map_sub]
    module

theorem accumulated_eq_sum (K : E →L[ℝ] E) (η : ℕ → E) (n : ℕ) :
    accumulated K η n = ∑ i ∈ Finset.range n, (K ^ (n - 1 - i)) (η i) := by
  induction n with
  | zero => simp [accumulated]
  | succ n ih =>
    rw [accumulated, ih, map_sum, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, ContinuousLinearMap.one_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have he : n - i = (n - 1 - i) + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [he, pow_succ', ContinuousLinearMap.mul_apply]

theorem horner_difference_eq_sum (K : E →L[ℝ] E) (a η : ℕ → E) (n : ℕ) :
    horner K a η n - horner K a (fun _ => 0) n =
      ∑ i ∈ Finset.range n, (K ^ (n - 1 - i)) (η i) := by
  rw [horner_difference, accumulated_eq_sum]

section Probability
variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [CompleteSpace E]

/-- MSE of the actual inexact Horner recursion relative to the exact one. -/
theorem horner_mse
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0)
    (η : ℕ → Lp E 2 μ) (K : E →L[ℝ] E) (hK : ‖K‖ ≤ 1) (a : ℕ → E)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (η i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (η j) : Lp E 2 μ) = 0) (m : ℕ) :
    (∫ ω, ‖horner K a (fun i => η i ω) m - horner K a (fun _ => 0) m‖ ^ 2 ∂μ) ≤
      ∑ i ∈ Finset.range m, ∫ ω, ‖η i ω‖ ^ 2 ∂μ := by
  have hsum := coe_sum_ae (fun i => (K ^ (m - 1 - i)).compLp (η i)) (Finset.range m)
  have hmaps : ∀ᵐ ω ∂μ, ∀ i : ℕ,
      (K ^ (m - 1 - i)).compLp (η i) ω = (K ^ (m - 1 - i)) (η i ω) :=
    ae_all_iff.mpr (fun i => (K ^ (m - 1 - i)).coeFn_compLp (η i))
  have heq : (∫ ω, ‖horner K a (fun i => η i ω) m - horner K a (fun _ => 0) m‖ ^ 2 ∂μ) =
      ∫ ω, ‖(∑ i ∈ Finset.range m, (K ^ (m - 1 - i)).compLp (η i) : Lp E 2 μ) ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hsum, hmaps] with ω hsum hmaps
    rw [horner_difference_eq_sum, hsum]
    congr 2
    exact Finset.sum_congr rfl (fun i _ => (hmaps i).symm)
  rw [heq]
  exact horner_errors_mse past hle η K hK adapted centered m

/-- Allocating `r²/(16m)` to each injected error gives MSE at most `r²/16`,
the budget used in the manuscript's inexact inverse-application proof. -/
theorem horner_mse_budget
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0)
    (η : ℕ → Lp E 2 μ) (K : E →L[ℝ] E) (hK : ‖K‖ ≤ 1) (a : ℕ → E)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (η i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (η j) : Lp E 2 μ) = 0)
    (m : ℕ) (hm : 0 < m) (r : ℝ)
    (budget : ∀ i < m, (∫ ω, ‖η i ω‖ ^ 2 ∂μ) ≤ r ^ 2 / (16 * (m : ℝ))) :
    (∫ ω, ‖horner K a (fun i => η i ω) m - horner K a (fun _ => 0) m‖ ^ 2 ∂μ) ≤
      r ^ 2 / 16 := by
  calc
    _ ≤ ∑ i ∈ Finset.range m, ∫ ω, ‖η i ω‖ ^ 2 ∂μ :=
      horner_mse past hle η K hK a adapted centered m
    _ ≤ ∑ _i ∈ Finset.range m, r ^ 2 / (16 * (m : ℝ)) :=
      Finset.sum_le_sum (fun i hi => budget i (Finset.mem_range.mp hi))
    _ = r ^ 2 / 16 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hmc : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
      ring

end Probability

end Bilevel.InexactHorner
