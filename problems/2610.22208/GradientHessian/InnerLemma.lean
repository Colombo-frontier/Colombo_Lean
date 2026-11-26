import GradientHessian.InnerForcingDerivatives
import GradientHessian.InnerSelfDerivatives
import GradientHessian.InnerNumericalForce

/-! The complete manuscript inner interface. Every tensor and gradient is
that of the literal objective on the Euclidean direct sum of all registers.
The single constant below is independent of task count and all dimensions. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates InverseGate
open scoped InnerProductSpace

def innerConstant : ℝ := 1 + valueConstant absoluteDepth + selfGradientConstant +
  2 * LatchLemma.latchConstant + 3 * forcingJetConstant + numericalForceBound

theorem innerConstant_pos : 0 < innerConstant := by
  unfold innerConstant
  linarith [valueConstant_pos absoluteDepth, selfGradientConstant_pos,
    LatchLemma.latchConstant_pos, forcingJetConstant_pos, numericalForceBound_pos]

theorem innerConstant_value : valueConstant absoluteDepth ≤ innerConstant := by
  unfold innerConstant
  linarith [selfGradientConstant_pos, LatchLemma.latchConstant_pos,
    forcingJetConstant_pos, numericalForceBound_pos]

theorem innerConstant_first : selfGradientConstant + forcingJetConstant ≤ innerConstant := by
  unfold innerConstant
  linarith [valueConstant_pos absoluteDepth, LatchLemma.latchConstant_pos,
    forcingJetConstant_pos, numericalForceBound_pos]

theorem innerConstant_higher :
    2 * LatchLemma.latchConstant + 2 * forcingJetConstant ≤ innerConstant := by
  unfold innerConstant
  linarith [valueConstant_pos absoluteDepth, selfGradientConstant_pos,
    forcingJetConstant_pos, numericalForceBound_pos]

theorem innerConstant_numerical : numericalForceBound ≤ innerConstant := by
  unfold innerConstant
  linarith [valueConstant_pos absoluteDepth, selfGradientConstant_pos,
    LatchLemma.latchConstant_pos, forcingJetConstant_pos]

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem residual_derivative_split (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (residual b a v) Z‖ ≤
      ‖iteratedFDeriv ℝ n (sumResidual v) Z‖ +
      ‖iteratedFDeriv ℝ n (forcingSum b a v) Z‖ := by
  rw [funext (residual_eq_sumResidual_sub b a v)]
  exact LocalizedProductDerivatives.norm_iteratedFDeriv_sub_le
    ((sumResidual_contDiff v).of_le (by exact_mod_cast hn)).contDiffAt
    ((forcingSum_contDiff b a v).of_le (by exact_mod_cast hn)).contDiffAt

variable [CompleteSpace E]

theorem residual_first_derivative_bound (hm : 1 ≤ m)
    (b a : Fin m → Y) (v : Fin m → Fin (absoluteDepth + 2) → E)
    (hb : ∀ i, ‖b i‖ = H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : Space Y E m (absoluteDepth + 2)) :
    ‖iteratedFDeriv ℝ 1 (residual b a v) Z‖ ≤ innerConstant * Real.sqrt m := by
  have hs := (absolute_sumResidual_derivative_bounds v hv Z).1
  have hf := forcingSum_derivative_bound b a v hb ha hv Z (n := 1) (by norm_num)
  have hsplit := residual_derivative_split b a v Z (n := 1) (by norm_num)
  have hroot : 1 ≤ Real.sqrt (m : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m by exact_mod_cast hm)
    simpa using h
  have hfroot : forcingJetConstant ≤ forcingJetConstant * Real.sqrt m :=
    le_mul_of_one_le_right forcingJetConstant_pos.le hroot
  calc
    _ ≤ (selfGradientConstant + forcingJetConstant) * Real.sqrt m := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right innerConstant_first (Real.sqrt_nonneg _)

theorem residual_higher_derivative_bound
    (b a : Fin m → Y) (v : Fin m → Fin (absoluteDepth + 2) → E)
    (hb : ∀ i, ‖b i‖ = H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : Space Y E m (absoluteDepth + 2)) :
    ‖iteratedFDeriv ℝ 2 (residual b a v) Z‖ +
      ‖iteratedFDeriv ℝ 3 (residual b a v) Z‖ ≤ innerConstant := by
  have hs := (absolute_sumResidual_derivative_bounds v hv Z).2
  have hf2 := forcingSum_derivative_bound b a v hb ha hv Z (n := 2) (by norm_num)
  have hf3 := forcingSum_derivative_bound b a v hb ha hv Z (n := 3) (by norm_num)
  have h2 := residual_derivative_split b a v Z (n := 2) (by norm_num)
  have h3 := residual_derivative_split b a v Z (n := 3) (by norm_num)
  linarith [innerConstant_higher]

variable [CompleteSpace Y]

/-- All four inequalities in source equation `inner-W`, for the actual
residual, with one absolute constant. -/
structure ResidualBounds (b a : Fin m → Y) (v : Fin m → Fin (absoluteDepth + 2) → E) : Prop where
  smooth : ContDiff ℝ 3 (residual b a v)
  value : ∀ Z, -innerConstant * m ≤ residual b a v Z ∧ residual b a v Z ≤ 0
  first : ∀ Z, ‖iteratedFDeriv ℝ 1 (residual b a v) Z‖ ≤ innerConstant * Real.sqrt m
  higher : ∀ Z, ‖iteratedFDeriv ℝ 2 (residual b a v) Z‖ +
    ‖iteratedFDeriv ℝ 3 (residual b a v) Z‖ ≤ innerConstant
  numerical : ∀ Z, ‖gradient (fun y => residual b a v (replaceNumerical Z y))
    (numerical Y E m (absoluteDepth + 2) Z)‖ ≤ innerConstant

theorem inner_bounds (hm : 1 ≤ m)
    (b a : Fin m → Y) (v : Fin m → Fin (absoluteDepth + 2) → E)
    (hb : ∀ i, ‖b i‖ = H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1) :
    ResidualBounds b a v := by
  refine ⟨residual_contDiff b a v, ?_, residual_first_derivative_bound hm b a v hb ha hv,
    residual_higher_derivative_bound b a v hb ha hv, ?_⟩
  · intro Z
    have h := residual_bounds b a v Z
    refine ⟨?_, h.2⟩
    have hC := mul_le_mul_of_nonneg_right innerConstant_value (Nat.cast_nonneg m)
    linarith [h.1]
  · intro Z
    exact (residual_numerical_gradient_bound b a v hb ha Z).trans innerConstant_numerical

/-- Full `lem:inner`: actual objective decomposition, global derivative and
value estimates, and activation for every nonnegative outgoing coefficient.
The certificate is the literal one in the preceding inverse-gate lemma. -/
theorem inner_lemma (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ)
    (b a : Fin (m + 1) → Y) (v : Fin (m + 1) → Fin (absoluteDepth + 2) → E)
    (hb : ∀ i, ‖b i‖ = H₀) (ha : ∀ i, ‖a i‖ = 1)
    (hcert : ∀ i, H₀ / 4 ≤ ⟪a i, InverseGate.inverse A hA (b i)⟫_ℝ)
    (hv : ∀ i j, ‖v i j‖ = 1) :
    ResidualBounds b a v ∧
    (∀ Z, objective A b a v Z =
      quadratic A (numerical Y E (m + 1) (absoluteDepth + 2) Z) +
        publicQuadratic (m + 1) absoluteDepth Z + residual b a v Z) ∧
    (∀ l, 0 ≤ l → ∀ Z, ‖gradient (driven A b a v l) Z‖ ≤ 1 →
      (∀ i, ports v Z i = 1) ∧
        ‖A (numerical Y E (m + 1) (absoluteDepth + 2) Z)‖ ≤ 1) := by
  exact ⟨inner_bounds (by omega) b a v hb ha hv,
    objective_decomposition A b a v,
    fun l hl Z hg => absolute_activation A hA hsym b a v hb ha hcert hv hl Z hg⟩

end GradientHessian.Inner
