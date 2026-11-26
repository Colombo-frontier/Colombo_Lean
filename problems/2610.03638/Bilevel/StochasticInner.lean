import Bilevel.InexactHorner

/-!
# Conditional-noise inner updates

Actual Hilbert-valued L2 random variables and L2 conditional expectations are
used throughout. The deterministic drift contraction is an explicit input;
the noise cross term is proved to vanish. The final theorem bounds the actual
expected squared error of a sequence satisfying the stochastic recursion.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Bilevel.StochasticInner

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

def risk (x : Lp E 2 μ) : ℝ := ∫ ω, ‖x ω‖ ^ 2 ∂μ

theorem risk_eq_norm_sq (x : Lp E 2 μ) : risk x = ‖x‖ ^ 2 :=
  (InexactHorner.norm_sq_eq_integral x).symm

theorem integrable_norm_sq (x : Lp E 2 μ) : Integrable (fun ω => ‖x ω‖ ^ 2) μ := by
  simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) x x

/-- Unconditional one-call identity with an actual Bochner mean-zero noise.
This is the fixed-state version used when conditioning on the current past. -/
theorem fixed_step_identity [CompleteSpace E] [IsProbabilityMeasure μ]
    (d : E) (noise : Ω → E) (η : ℝ) (hnoise : Integrable noise μ)
    (hsq : Integrable (fun ω => ‖noise ω‖ ^ 2) μ) (hmean : (∫ ω, noise ω ∂μ) = 0) :
    (∫ ω, ‖d - η • noise ω‖ ^ 2 ∂μ) = ‖d‖ ^ 2 + η ^ 2 * ∫ ω, ‖noise ω‖ ^ 2 ∂μ := by
  have hinner : Integrable (fun ω => inner (𝕜 := ℝ) d (noise ω)) μ := hnoise.const_inner d
  have hcross : (∫ ω, inner (𝕜 := ℝ) d (noise ω) ∂μ) = 0 := by
    rw [integral_inner hnoise d, hmean, inner_zero_right]
  have heq : (fun ω => ‖d - η • noise ω‖ ^ 2) =
      fun ω => (‖d‖ ^ 2 + η ^ 2 * ‖noise ω‖ ^ 2) - (2 * η) * inner (𝕜 := ℝ) d (noise ω) := by
    funext ω
    simp only [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hfirst : Integrable (fun ω => ‖d‖ ^ 2 + η ^ 2 * ‖noise ω‖ ^ 2) μ :=
    (integrable_const _).add (hsq.const_mul _)
  rw [heq, integral_sub hfirst (hinner.const_mul (2 * η)),
    integral_add (integrable_const (‖d‖ ^ 2)) (hsq.const_mul (η ^ 2))]
  simp only [integral_const_mul, hcross, mul_zero, sub_zero, integral_const,
    measureReal_univ_eq_one, one_smul]

theorem risk_update_identity [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) (drift noise : Lp E 2 μ) (η : ℝ)
    (past : AEStronglyMeasurable[m] drift μ)
    (centered : (condExpL2 E ℝ hm noise : Lp E 2 μ) = 0) :
    risk (drift - η • noise) = risk drift + η ^ 2 * risk noise := by
  have hcross : inner (𝕜 := ℝ) drift noise = 0 := by
    rw [real_inner_comm]
    exact InexactHorner.condMean_zero_inner (m0 := m0) hm noise drift centered past
  simp only [risk_eq_norm_sq, norm_sub_sq_real, real_inner_smul_right, hcross,
    mul_zero, sub_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The same one-step identity, stated as the integral of the actual pointwise
noisy update rather than the norm of an equivalence class. -/
theorem integral_update_identity [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) (drift noise : Lp E 2 μ) (η : ℝ)
    (past : AEStronglyMeasurable[m] drift μ)
    (centered : (condExpL2 E ℝ hm noise : Lp E 2 μ) = 0) :
    (∫ ω, ‖drift ω - η • noise ω‖ ^ 2 ∂μ) = risk drift + η ^ 2 * risk noise := by
  rw [← risk_update_identity hm drift noise η past centered]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub drift (η • noise), Lp.coeFn_smul η noise] with ω hsub hsmul
  simp only [hsub, Pi.sub_apply, hsmul, Pi.smul_apply]

theorem drift_risk_bound (x drift : Lp E 2 μ) {q : ℝ}
    (contraction : ∀ᵐ ω ∂μ, ‖drift ω‖ ^ 2 ≤ q * ‖x ω‖ ^ 2) :
    risk drift ≤ q * risk x := by
  have hi := integral_mono_ae (integrable_norm_sq drift)
    ((integrable_norm_sq x).const_mul q) contraction
  simpa only [integral_const_mul] using hi

/-- Fresh conditional-mean-zero noise adds only its variance to the squared
deterministic contraction. The noise can depend on all preceding iterations. -/
theorem one_step_bound [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) (x drift noise : Lp E 2 μ)
    (η q σ : ℝ) (past : AEStronglyMeasurable[m] drift μ)
    (centered : (condExpL2 E ℝ hm noise : Lp E 2 μ) = 0)
    (contraction : ∀ᵐ ω ∂μ, ‖drift ω‖ ^ 2 ≤ q * ‖x ω‖ ^ 2)
    (variance : risk noise ≤ σ ^ 2) :
    (∫ ω, ‖drift ω - η • noise ω‖ ^ 2 ∂μ) ≤ q * risk x + η ^ 2 * σ ^ 2 := by
  rw [integral_update_identity hm drift noise η past centered]
  exact add_le_add (drift_risk_bound x drift contraction)
    (mul_le_mul_of_nonneg_left variance (sq_nonneg η))

/-- Solving the finite affine recurrence with its exact transient factor. -/
theorem affine_recurrence (a : ℕ → ℝ) {q B : ℝ} (hq : 0 ≤ q)
    (step : ∀ n, a (n + 1) ≤ q * a n + (1 - q) * B) (n : ℕ) :
    a n ≤ q ^ n * a 0 + B * (1 - q ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ q * a n + (1 - q) * B := step n
      _ ≤ q * (q ^ n * a 0 + B * (1 - q ^ n)) + (1 - q) * B :=
        add_le_add_right (mul_le_mul_of_nonneg_left ih hq) _
      _ = _ := by rw [pow_succ]; ring

theorem affine_recurrence_floor (a : ℕ → ℝ) {q B : ℝ} (hq : 0 ≤ q) (hB : 0 ≤ B)
    (step : ∀ n, a (n + 1) ≤ q * a n + (1 - q) * B) (n : ℕ) :
    a n ≤ q ^ n * a 0 + B := by
  have h := affine_recurrence a hq step n
  have hn : 0 ≤ q ^ n := pow_nonneg hq _
  nlinarith

/-- Actual stochastic-iteration recurrence, with a possibly adaptive drift and
noise. The equality hypothesis specifies the update on the probability space. -/
theorem iteration_bound [CompleteSpace E]
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ t, past t ≤ m0)
    (x drift noise : ℕ → Lp E 2 μ) (η q σ : ℝ) (hq : 0 ≤ q)
    (drift_measurable : ∀ t, AEStronglyMeasurable[past t] (drift t) μ)
    (centered : ∀ t, (condExpL2 E ℝ (hle t) (noise t) : Lp E 2 μ) = 0)
    (contraction : ∀ t, ∀ᵐ ω ∂μ, ‖drift t ω‖ ^ 2 ≤ q * ‖x t ω‖ ^ 2)
    (variance : ∀ t, risk (noise t) ≤ σ ^ 2)
    (update : ∀ t, (x (t + 1) : Ω → E) =ᵐ[μ] fun ω => drift t ω - η • noise t ω)
    {B : ℝ} (floor_identity : η ^ 2 * σ ^ 2 = (1 - q) * B) (n : ℕ) :
    risk (x n) ≤ q ^ n * risk (x 0) + B * (1 - q ^ n) := by
  apply affine_recurrence (fun t => risk (x t)) hq
  intro t
  have heq : risk (x (t + 1)) = ∫ ω, ‖drift t ω - η • noise t ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [update t] with ω hω
    rw [hω]
  rw [heq, ← floor_identity]
  exact one_step_bound (hle t) (x t) (drift t) (noise t) η q σ
    (drift_measurable t) (centered t) (contraction t) (variance t)

/-- With contraction factor `1 - modulus * η`, the variance floor is
`η * σ² / modulus`, retaining the strongly-convex condition-number scale. -/
theorem strongly_convex_iteration_bound [CompleteSpace E]
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ t, past t ≤ m0)
    (x drift noise : ℕ → Lp E 2 μ) {modulus η : ℝ} (σ : ℝ)
    (hmodulus : 0 < modulus) (hstep : modulus * η ≤ 1)
    (drift_measurable : ∀ t, AEStronglyMeasurable[past t] (drift t) μ)
    (centered : ∀ t, (condExpL2 E ℝ (hle t) (noise t) : Lp E 2 μ) = 0)
    (contraction : ∀ t, ∀ᵐ ω ∂μ, ‖drift t ω‖ ^ 2 ≤ (1 - modulus * η) * ‖x t ω‖ ^ 2)
    (variance : ∀ t, risk (noise t) ≤ σ ^ 2)
    (update : ∀ t, (x (t + 1) : Ω → E) =ᵐ[μ] fun ω => drift t ω - η • noise t ω)
    (n : ℕ) :
    risk (x n) ≤ (1 - modulus * η) ^ n * risk (x 0) +
      (η * σ ^ 2 / modulus) * (1 - (1 - modulus * η) ^ n) := by
  have hfloor : η ^ 2 * σ ^ 2 = (1 - (1 - modulus * η)) * (η * σ ^ 2 / modulus) := by
    field_simp
    ring
  exact iteration_bound past hle x drift noise η (1 - modulus * η) σ (by linarith)
    drift_measurable centered contraction variance update hfloor n

theorem strongly_convex_iteration_floor [CompleteSpace E]
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ t, past t ≤ m0)
    (x drift noise : ℕ → Lp E 2 μ) {modulus η : ℝ} (σ : ℝ)
    (hmodulus : 0 < modulus) (hη : 0 ≤ η) (hstep : modulus * η ≤ 1)
    (drift_measurable : ∀ t, AEStronglyMeasurable[past t] (drift t) μ)
    (centered : ∀ t, (condExpL2 E ℝ (hle t) (noise t) : Lp E 2 μ) = 0)
    (contraction : ∀ t, ∀ᵐ ω ∂μ, ‖drift t ω‖ ^ 2 ≤ (1 - modulus * η) * ‖x t ω‖ ^ 2)
    (variance : ∀ t, risk (noise t) ≤ σ ^ 2)
    (update : ∀ t, (x (t + 1) : Ω → E) =ᵐ[μ] fun ω => drift t ω - η • noise t ω)
    (n : ℕ) :
    risk (x n) ≤ (1 - modulus * η) ^ n * risk (x 0) + η * σ ^ 2 / modulus := by
  have hb := strongly_convex_iteration_bound past hle x drift noise σ hmodulus hstep
    drift_measurable centered contraction variance update n
  have hf : 0 ≤ η * σ ^ 2 / modulus := by positivity
  have hq : 0 ≤ (1 - modulus * η) ^ n := pow_nonneg (by linarith) _
  nlinarith

end Bilevel.StochasticInner
