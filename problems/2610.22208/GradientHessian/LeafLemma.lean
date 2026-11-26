import GradientHessian.LeafRegularity
import GradientHessian.LeafOracle
import GradientHessian.LeafCoercivity

/-! The complete analytic capped-leaf interface, for the literal functions
on shared physical coordinates. The oracle factorization is explicit and
conditional on known marked coefficients, as in the source. -/

noncomputable section
namespace GradientHessian.Leaf
open InnerCoordinates
open scoped InnerProductSpace

def leafConstant : ℝ := leafJetConstant + Inner.innerConstant + 2*numericalRadius^2 + 12

theorem leafConstant_pos : 0 < leafConstant := by
  unfold leafConstant
  linarith [leafJetConstant_pos, Inner.innerConstant_pos, sq_nonneg numericalRadius]

theorem leafConstant_jet : leafJetConstant ≤ leafConstant := by
  unfold leafConstant
  linarith [Inner.innerConstant_pos, sq_nonneg numericalRadius]
theorem leafConstant_inner : Inner.innerConstant ≤ leafConstant := by
  unfold leafConstant
  linarith [leafJetConstant_pos, sq_nonneg numericalRadius]
theorem leafConstant_twelve : 12 ≤ leafConstant := by
  unfold leafConstant
  linarith [leafJetConstant_pos, Inner.innerConstant_pos, sq_nonneg numericalRadius]
theorem leafConstant_bounded : 2*numericalRadius^2+Inner.innerConstant ≤ leafConstant := by
  unfold leafConstant
  linarith [leafJetConstant_pos]

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {m : ℕ}

structure Bounds (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) : Prop where
  smooth : ContDiff ℝ 3 (objective A b a v)
  correction_smooth : ContDiff ℝ 3 (correction A b a v)
  sign : ∀ Z, correction A b a v Z ≤ 0
  jets : ∀ n ≤ 3, ∀ Z, ‖iteratedFDeriv ℝ n (correction A b a v) Z‖ ≤ leafConstant*(m:ℝ)^(3-n)
  bounded_value : ∀ Z, ‖numerical Y E m (Inner.absoluteDepth+2) Z‖ ≤ numericalRadius →
    -leafConstant*m ≤ correction A b a v Z
  numerical_gradient : ∀ Z,
    gradient (fun y => objective A b a v (replaceNumerical Z y))
      (numerical Y E m (Inner.absoluteDepth+2) Z) =
        numericalMatrix A Z (numerical Y E m (Inner.absoluteDepth+2) Z) + numericalForce b a v Z
  matrix_lower : ∀ Z : Space Y E m, InverseGate.LowerBound (numericalMatrix A Z)
  matrix_upper : ∀ (Z : Space Y E m) x, ⟪numericalMatrix A Z x,x⟫_ℝ ≤ leafConstant*m*‖x‖^2
  matrix_symmetric : ∀ (Z : Space Y E m) x z, ⟪numericalMatrix A Z x,z⟫_ℝ = ⟪x,numericalMatrix A Z z⟫_ℝ
  force : ∀ Z, ‖numericalForce b a v Z‖ ≤ leafConstant
  energy : ∀ Z, ‖numerical Y E m (Inner.absoluteDepth+2) Z‖^2/2 +
    Inner.publicQuadratic m Inner.absoluteDepth Z - leafConstant*m ≤ objective A b a v Z
  coercive : ∀ Z, coercivityConstant*‖Z‖^2-leafConstant*m ≤ objective A b a v Z
  third : ∀ Z, ‖iteratedFDeriv ℝ 3 (objective A b a v) Z‖ ≤ leafConstant
  hessian_lipschitz : LipschitzWith ⟨leafConstant, leafConstant_pos.le⟩
    (iteratedFDeriv ℝ 2 (objective A b a v))

theorem leaf_bounds (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A) (hAn : ‖A‖ ≤ m)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1) :
    Bounds A b a v := by
  refine ⟨objective_contDiff hm A b a v, correction_contDiff hm A b a v,
    correction_nonpos A hAn b a v, ?_, ?_, ?_, numericalMatrix_lower hm A hA hAn,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn Z
    exact (correction_derivative_bound hm A hAn b a v hb ha hv Z hn).trans
      (mul_le_mul_of_nonneg_right leafConstant_jet (by positivity))
  · intro Z hZ
    have h := (bounded_correction A hAn b a v Z hZ).1
    have hC := mul_le_mul_of_nonneg_right leafConstant_bounded (Nat.cast_nonneg m)
    linarith
  · intro Z
    exact (objective_numerical_hasGradientAt hm A hsym b a v Z).gradient
  · intro Z x
    have hB := (numericalMatrix_norm hm A hAn Z).trans
      (mul_le_mul_of_nonneg_right leafConstant_twelve (Nat.cast_nonneg m))
    calc
      _ ≤ ‖numericalMatrix A Z x‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ (leafConstant*m*‖x‖)*‖x‖ := by
        gcongr
        exact (numericalMatrix A Z).le_opNorm x |>.trans
          (mul_le_mul_of_nonneg_right hB (norm_nonneg x))
      _ = _ := by ring
  · intro Z
    exact LeafNumerical.gradientMatrix_symmetric m (capRadius m) A hsym _
  · intro Z
    exact (numericalForce_bound b a v hb ha Z).trans leafConstant_inner
  · intro Z
    have h := objective_energy hm A hA b a v Z
    have hC := mul_le_mul_of_nonneg_right leafConstant_inner (Nat.cast_nonneg m)
    linarith
  · intro Z
    have h := objective_coercive_bound hm A hA b a v Z
    have hC := mul_le_mul_of_nonneg_right leafConstant_inner (Nat.cast_nonneg m)
    linarith
  · intro Z
    exact (objective_third_derivative_bound hm A hAn b a v hb ha hv Z).trans leafConstant_jet
  · intro x y
    exact (objective_hessian_lipschitz hm A hAn b a v hb ha hv x y).trans
      (mul_le_mul_right' (ENNReal.coe_le_coe.mpr leafConstant_jet) _)

/-- All analytic claims in `lem:leaf`, including zero value and activation
for every nonnegative outgoing coefficient. Convex-mixture localization and
the one-product identities are exported separately without hiding their data. -/
theorem leaf_lemma (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A) (hAn : ‖A‖ ≤ m+1)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin (m+1) → Y)
    (v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1)
    (hcert : ∀ i, InverseGate.H₀/4 ≤ ⟪a i,InverseGate.inverse A hA (b i)⟫_ℝ)
    (hv : ∀ i j, ‖v i j‖ = 1) :
    Bounds A b a v ∧ objective A b a v (0 : Space Y E (m+1)) = -10*InverseGate.H₀^2 ∧
      ∀ l, 0 ≤ l → ∀ Z, ‖gradient (driven A b a v l) Z‖ ≤ 1 → outgoing v Z = 1 := by
  exact ⟨leaf_bounds (by omega) A hA (by simpa using hAn) hsym b a v hb ha hv,
    objective_zero A b a v, fun l hl Z hg => (activation A hA hAn hsym b a v hb ha hcert hv hl Z hg).1⟩

end GradientHessian.Leaf
