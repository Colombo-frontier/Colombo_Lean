import FreshGradientMinimax.PathIncidence

/-! The actual inverse of mu I + beta A* A in finite-dimensional Euclidean
space. Existence follows from coercivity, not from an assumed inverse formula. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

variable {n m : ℕ}

def normalOperator (A : Euclid n →L[ℝ] Euclid m) (μ β : ℝ) : Euclid n →L[ℝ] Euclid n :=
  μ • ContinuousLinearMap.id ℝ (Euclid n) + β • (A†).comp A

@[simp]
theorem normalOperator_apply (A : Euclid n →L[ℝ] Euclid m) (μ β : ℝ) (x : Euclid n) :
    normalOperator A μ β x = μ • x + β • (A†) (A x) := rfl

theorem normalOperator_inner (A : Euclid n →L[ℝ] Euclid m) (μ β : ℝ) (x : Euclid n) :
    ⟪normalOperator A μ β x, x⟫_ℝ = μ * ‖x‖ ^ 2 + β * ‖A x‖ ^ 2 := by
  simp only [normalOperator_apply, inner_add_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

theorem normalOperator_symmetric (A : Euclid n →L[ℝ] Euclid m) (μ β : ℝ) (x y : Euclid n) :
    ⟪normalOperator A μ β x, y⟫_ℝ = ⟪x, normalOperator A μ β y⟫_ℝ := by
  simp only [normalOperator_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

theorem normalOperator_coercive (A : Euclid n →L[ℝ] Euclid m) (μ : ℝ)
    {β : ℝ} (hβ : 0 ≤ β) (x : Euclid n) : μ * ‖x‖ ≤ ‖normalOperator A μ β x‖ := by
  apply residual_controls_distance μ (normalOperator A μ β x) x
  rw [normalOperator_inner]
  exact le_add_of_nonneg_right (by positivity)

theorem normalOperator_injective (A : Euclid n →L[ℝ] Euclid m) {μ β : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) : Function.Injective (normalOperator A μ β) := by
  intro x y hxy
  have hz : normalOperator A μ β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h := normalOperator_coercive A μ hβ (x - y)
  rw [hz, norm_zero] at h
  have hn : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

def normalEquiv (A : Euclid n →L[ℝ] Euclid m) (μ β : ℝ) (hμ : 0 < μ) (hβ : 0 ≤ β) :
    Euclid n ≃ₗ[ℝ] Euclid n :=
  LinearEquiv.ofBijective (normalOperator A μ β).toLinearMap
    ⟨normalOperator_injective A hμ hβ,
      LinearMap.surjective_of_injective (normalOperator_injective A hμ hβ)⟩

def normalInverse (A : Euclid n →L[ℝ] Euclid m) (μ β : ℝ) (hμ : 0 < μ) (hβ : 0 ≤ β) :
    Euclid n →L[ℝ] Euclid n :=
  LinearMap.toContinuousLinearMap (normalEquiv A μ β hμ hβ).symm.toLinearMap

@[simp]
theorem normalInverse_right (A : Euclid n →L[ℝ] Euclid m) {μ β : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (b : Euclid n) :
    normalOperator A μ β (normalInverse A μ β hμ hβ b) = b :=
  (normalEquiv A μ β hμ hβ).apply_symm_apply b

@[simp]
theorem normalInverse_left (A : Euclid n →L[ℝ] Euclid m) {μ β : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (x : Euclid n) :
    normalInverse A μ β hμ hβ (normalOperator A μ β x) = x :=
  (normalEquiv A μ β hμ hβ).symm_apply_apply x

theorem normalInverse_eq_of_root (A : Euclid n →L[ℝ] Euclid m) {μ β : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) {b x : Euclid n} (hx : normalOperator A μ β x = b) :
    normalInverse A μ β hμ hβ b = x := by rw [← hx, normalInverse_left]

theorem normalInverse_norm (A : Euclid n →L[ℝ] Euclid m) {μ β : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (b : Euclid n) : ‖normalInverse A μ β hμ hβ b‖ ≤ ‖b‖ / μ := by
  have h := normalOperator_coercive A μ hβ (normalInverse A μ β hμ hβ b)
  rw [normalInverse_right] at h
  exact (le_div_iff₀ hμ).mpr (by simpa only [mul_comm] using h)

theorem normalInverse_opNorm (A : Euclid n →L[ℝ] Euclid m) {μ β : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) : ‖normalInverse A μ β hμ hβ‖ ≤ 1 / μ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using normalInverse_norm A hμ hβ b

theorem normalInverse_symmetric (A : Euclid n →L[ℝ] Euclid m) {μ β : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (b c : Euclid n) :
    ⟪normalInverse A μ β hμ hβ b, c⟫_ℝ = ⟪b, normalInverse A μ β hμ hβ c⟫_ℝ := by
  have h := normalOperator_symmetric A μ β
    (normalInverse A μ β hμ hβ b) (normalInverse A μ β hμ hβ c)
  simpa only [normalInverse_right] using h.symm

theorem normalInverse_positive (A : Euclid n →L[ℝ] Euclid m) {μ β : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (b : Euclid n) : 0 ≤ ⟪b, normalInverse A μ β hμ hβ b⟫_ℝ := by
  have h := normalOperator_inner A μ β (normalInverse A μ β hμ hβ b)
  rw [normalInverse_right] at h
  rw [h]
  positivity

end FreshGradientMinimax
