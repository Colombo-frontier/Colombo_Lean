import GradientHessian.LeafLocalization

/-! Source powers M^(3-j) for the actual capped residual on the complete
physical Euclidean space, with one constant independent of every dimension. -/

noncomputable section
namespace GradientHessian.Leaf
open InnerCoordinates
open scoped InnerProductSpace

def correctionJetSum : ℝ := LeafCorrection.correctionConstant 0 + LeafCorrection.correctionConstant 1 +
  LeafCorrection.correctionConstant 2 + LeafCorrection.correctionConstant 3
def leafJetConstant : ℝ := 1 + Inner.innerConstant + 3*capFactor^2*correctionJetSum

theorem correctionJetSum_pos : 0 < correctionJetSum := by
  unfold correctionJetSum
  linarith [LeafCorrection.correctionConstant_pos 0, LeafCorrection.correctionConstant_pos 1,
    LeafCorrection.correctionConstant_pos 2, LeafCorrection.correctionConstant_pos 3]

theorem correctionConstant_le_sum {n : ℕ} (hn : n ≤ 3) :
    LeafCorrection.correctionConstant n ≤ correctionJetSum := by
  unfold correctionJetSum
  have h0 := LeafCorrection.correctionConstant_pos 0
  have h1 := LeafCorrection.correctionConstant_pos 1
  have h2 := LeafCorrection.correctionConstant_pos 2
  have h3 := LeafCorrection.correctionConstant_pos 3
  interval_cases n <;> linarith

theorem leafJetConstant_pos : 0 < leafJetConstant := by
  have hC := correctionJetSum_pos
  have hI := Inner.innerConstant_pos
  unfold leafJetConstant
  positivity

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

theorem capped_quadratic_derivative_bound (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (hA : ‖A‖ ≤ m)
    (Z : Space Y E m) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W : Space Y E m => LeafCorrection.correction (capRadius m)
      (LeafNumerical.deviation m A) (numerical Y E m (Inner.absoluteDepth+2) W)) Z‖ ≤
      (3*capFactor^2*LeafCorrection.correctionConstant n)*(m:ℝ)^(3-n) := by
  have hM : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0:ℝ) < m := lt_of_lt_of_le zero_lt_one hM
  have hC := LeafCorrection.correctionConstant_pos n
  have hL := capRadius_pos hm
  have hcap : 1 ≤ capFactor := capFactor_gt_one.le
  have hpow : (m:ℝ)^n ≤ capFactor^n*(m:ℝ)^n :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ hcap)
  have hcomp := Inner.derivative_comp_linear_le (numerical Y E m (Inner.absoluteDepth+2))
    (Inner.numerical_norm_le _ _) (LeafCorrection.correction_contDiff (capRadius_pos hm)
      (LeafNumerical.deviation m A)) hn Z
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (LeafCorrection.correction (capRadius m) (LeafNumerical.deviation m A))
      (numerical Y E m (Inner.absoluteDepth+2) Z)‖ := hcomp
    _ ≤ LeafCorrection.correctionConstant n*‖LeafNumerical.deviation m A‖*(capRadius m)^2/(capRadius m)^n :=
      LeafCorrection.correction_derivative_bound (capRadius_pos hm) _ n hn _
    _ ≤ LeafCorrection.correctionConstant n*(3*m)*(capRadius m)^2/(capRadius m)^n := by
      gcongr
      exact LeafNumerical.deviation_norm (Nat.cast_nonneg m) A hA
    _ = (3*capFactor^2*LeafCorrection.correctionConstant n)*(m:ℝ)^3/(capFactor^n*(m:ℝ)^n) := by
      simp only [capRadius, mul_pow]
      ring
    _ ≤ (3*capFactor^2*LeafCorrection.correctionConstant n)*(m:ℝ)^3/(m:ℝ)^n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by rw [pow_sub₀ (m:ℝ) hM0.ne' hn]; ring

variable [CompleteSpace Y] [CompleteSpace E]

theorem residual_scaled_derivative_bound (hm : 1 ≤ m) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : Space Y E m) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (Inner.residual b a v) Z‖ ≤ Inner.innerConstant*(m:ℝ)^(3-n) := by
  have hi := Inner.inner_bounds hm b a v hb ha hv
  have hM : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hC := Inner.innerConstant_pos.le
  interval_cases n
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonpos (hi.value Z).2]
    have hp : (m:ℝ) ≤ (m:ℝ)^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (by norm_num : 1 ≤ 3)
    norm_num only [Nat.sub_zero]
    nlinarith [(hi.value Z).1, mul_le_mul_of_nonneg_left hp hC]
  · have hs : Real.sqrt (m:ℝ) ≤ (m:ℝ)^2 :=
      ((Real.sqrt_le_iff).mpr ⟨hM0, by nlinarith⟩).trans (by nlinarith)
    exact (hi.first Z).trans (mul_le_mul_of_nonneg_left hs hC)
  · norm_num only [Nat.reduceSub, pow_one]
    have hh := hi.higher Z
    have hn3 := norm_nonneg (iteratedFDeriv ℝ 3 (Inner.residual b a v) Z)
    have hp := le_mul_of_one_le_right hC hM
    linarith
  · norm_num only [Nat.sub_self, pow_zero, mul_one]
    have hh := hi.higher Z
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (Inner.residual b a v) Z)]

theorem correction_derivative_bound (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (hA : ‖A‖ ≤ m)
    (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : Space Y E m) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (correction A b a v) Z‖ ≤ leafJetConstant*(m:ℝ)^(3-n) := by
  have hsum := Inner.norm_iteratedFDeriv_add_le
    ((LeafCorrection.correction_contDiff (capRadius_pos hm) (LeafNumerical.deviation m A)).comp
      (numerical Y E m (Inner.absoluteDepth+2)).contDiff)
    (Inner.residual_contDiff b a v) hn Z
  dsimp only [Function.comp_def] at hsum
  have hc := capped_quadratic_derivative_bound hm A hA Z hn
  have hr := residual_scaled_derivative_bound hm b a v hb ha hv Z hn
  have hcoef : 3*capFactor^2*LeafCorrection.correctionConstant n + Inner.innerConstant ≤ leafJetConstant := by
    have hh := mul_le_mul_of_nonneg_left (correctionConstant_le_sum hn) (by positivity : 0 ≤ 3*capFactor^2)
    unfold leafJetConstant
    linarith
  calc
    _ ≤ (3*capFactor^2*LeafCorrection.correctionConstant n + Inner.innerConstant)*(m:ℝ)^(3-n) := by
      change ‖iteratedFDeriv ℝ n (fun W => _+_) Z‖ ≤ _
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

end GradientHessian.Leaf
