import Smoothness2601.Minimax
import Smoothness2601.DifferentiationBias
import Smoothness2601.WeightGrowth

/-! Actual population derivative assumptions to the fully specified Chebyshev
query rule. The r=1 case is derived from the two baseline Hessian blocks. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped BigOperators

namespace Smoothness2601.Population

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

def pairedLinear (A : Y →L[ℝ] X) (B : Y →L[ℝ] Y) : Y →L[ℝ] Joint X Y :=
  packLinear.comp (A.prod B)

@[simp] theorem pairedLinear_apply (A : Y →L[ℝ] X) (B : Y →L[ℝ] Y) (v : Y) :
    pairedLinear A B v = pack (A v) (B v) := rfl

theorem pairedLinear_norm_bound (A : Y →L[ℝ] X) (B : Y →L[ℝ] Y)
    {C : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) :
    ‖pairedLinear A B‖ ≤ Real.sqrt 2 * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have ha : ‖A v‖ ≤ C * ‖v‖ := (A.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
  have hb : ‖B v‖ ≤ C * ‖v‖ := (B.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  have ha2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg v))).mpr ha
  have hb2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg v))).mpr hb
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt 2 * C * ‖v‖)).mp
  rw [pairedLinear_apply, norm_sq]
  change ‖A v‖ ^ 2 + ‖B v‖ ^ 2 ≤ (Real.sqrt 2 * C * ‖v‖) ^ 2
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  simp only [mul_pow, hs]
  nlinarith [sq_nonneg (C * ‖v‖)]

variable [CompleteSpace X] [CompleteSpace Y]
variable {b : Budgets} (P : Population (X := X) (Y := Y) b)

def lowerGradientField (x : X) (y : Y) : Joint X Y := P.grad_g (pack x y)
def lowerJacobian (x : X) (y : Y) : Y →L[ℝ] Joint X Y :=
  pairedLinear (P.gxy x y) (P.gyy x y)

theorem lowerGradientField_hasFDerivAt (x : X) (y : Y) :
    HasFDerivAt (P.lowerGradientField x) (P.lowerJacobian x y) y := by
  have he := (packLinear : (X × Y) →L[ℝ] Joint X Y).hasFDerivAt.comp y
    ((P.has_gxy x y).prodMk (P.has_gyy x y))
  exact he

theorem lowerJacobian_lipschitz (x : X) (u v : Y) :
    ‖P.lowerJacobian x u - P.lowerJacobian x v‖ ≤ Real.sqrt 2 * b.L₂ * ‖u-v‖ := by
  have hdist : ‖pack x u - pack x v‖ = ‖u-v‖ := by
    rw [norm_sub_pack]
    simp [Bilevel.Model.jointDistance, Real.sqrt_sq (norm_nonneg (u-v))]
  have ha := P.variation_xy x x u v
  have hb := P.variation_yy x x u v
  rw [hdist] at ha hb
  have he : P.lowerJacobian x u - P.lowerJacobian x v =
      pairedLinear (P.gxy x u - P.gxy x v) (P.gyy x u - P.gyy x v) := rfl
  rw [he]
  simpa only [mul_assoc] using pairedLinear_norm_bound _ _
    (mul_nonneg b.L₂_pos.le (norm_nonneg _)) ha hb

theorem lowerGradientField_contDiff_one (x : X) : ContDiff ℝ 1 (P.lowerGradientField x) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨P.lowerJacobian x, ?_, P.lowerGradientField_hasFDerivAt x⟩
  have hLip : LipschitzWith ⟨Real.sqrt 2 * b.L₂,
      mul_nonneg (Real.sqrt_nonneg _) b.L₂_pos.le⟩ (P.lowerJacobian x) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [dist_eq_norm] using P.lowerJacobian_lipschitz x u v
  exact hLip.continuous

theorem lowerGradientField_iterated_one_lipschitz (x : X) (u v : Y) :
    ‖iteratedFDeriv ℝ 1 (P.lowerGradientField x) u -
      iteratedFDeriv ℝ 1 (P.lowerGradientField x) v‖ ≤ Real.sqrt 2 * b.L₂ * ‖u-v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) b.L₂_pos.le) (norm_nonneg _))
  intro m
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_one_apply,
    (P.lowerGradientField_hasFDerivAt x u).fderiv,
    (P.lowerGradientField_hasFDerivAt x v).fderiv]
  have he := (P.lowerJacobian x u - P.lowerJacobian x v).le_opNorm (m 0)
  have hb := mul_le_mul_of_nonneg_right (P.lowerJacobian_lipschitz x u v) (norm_nonneg (m 0))
  simpa using he.trans hb

def normalizedAmplitude (b : Budgets) (M : ℝ) : ℝ := max 1 (max M (Real.sqrt 2 * b.L₂))
def normalizedFrequency (Λ : ℝ) : ℝ := max 1 Λ
def adjointRadius (b : Budgets) : ℝ := max 1 (b.L₀ / b.μ)

theorem normalizedAmplitude_one_le (M : ℝ) : 1 ≤ normalizedAmplitude b M := le_max_left _ _
theorem normalizedAmplitude_original_le (M : ℝ) : M ≤ normalizedAmplitude b M :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem normalizedAmplitude_baseline_le (M : ℝ) :
    Real.sqrt 2 * b.L₂ ≤ normalizedAmplitude b M :=
  (le_max_right _ _).trans (le_max_right _ _)
theorem normalizedFrequency_one_le (Λ : ℝ) : 1 ≤ normalizedFrequency Λ := le_max_left _ _
theorem normalizedFrequency_original_le (Λ : ℝ) : Λ ≤ normalizedFrequency Λ := le_max_right _ _
theorem adjointRadius_one_le : 1 ≤ adjointRadius b := le_max_left _ _

def fieldDerivativeBudget (b : Budgets) (M Λ β : ℝ) (r : ℕ) : ℝ :=
  normalizedAmplitude b M * normalizedFrequency Λ ^ (r+1) * ((r+1).factorial : ℝ) ^ β

theorem fieldDerivativeBudget_pos (M Λ β : ℝ) (r : ℕ) :
    0 < fieldDerivativeBudget b M Λ β r := by
  have hM := zero_lt_one.trans_le (normalizedAmplitude_one_le (b := b) M)
  have hΛ := zero_lt_one.trans_le (normalizedFrequency_one_le Λ)
  unfold fieldDerivativeBudget
  positivity

theorem baseline_le_fieldDerivativeBudget (M Λ : ℝ) {β : ℝ} (hβ : 0 ≤ β) (r : ℕ) :
    Real.sqrt 2 * b.L₂ ≤ fieldDerivativeBudget b M Λ β r := by
  have hΛ : 1 ≤ normalizedFrequency Λ ^ (r+1) :=
    one_le_pow₀ (normalizedFrequency_one_le Λ)
  have hfact : (1 : ℝ) ≤ (r+1).factorial := by exact_mod_cast Nat.factorial_pos (r+1)
  have hF := Real.one_le_rpow hfact hβ
  have hM := zero_le_one.trans (normalizedAmplitude_one_le (b := b) M)
  have he := mul_le_mul hΛ hF (by norm_num : (0:ℝ) ≤ 1) (by positivity)
  have hh := mul_le_mul_of_nonneg_left he hM
  unfold fieldDerivativeBudget
  nlinarith [normalizedAmplitude_baseline_le (b := b) M]

theorem original_le_fieldDerivativeBudget {M Λ β : ℝ} (_hM : 0 < M) (hΛ : 0 < Λ)
    (r : ℕ) : M * Λ ^ (r+1) * ((r+1).factorial : ℝ) ^ β ≤ fieldDerivativeBudget b M Λ β r := by
  have hp := pow_le_pow_left₀ hΛ.le (normalizedFrequency_original_le Λ) (r+1)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  exact mul_le_mul (normalizedAmplitude_original_le (b := b) M) hp
    (pow_nonneg hΛ.le _) (zero_le_one.trans (normalizedAmplitude_one_le (b := b) M))

/-- All finite available orders, including r=1 and p=∞, under exactly the
population assumptions. The extra derivative C^{r+1} is not required. -/
theorem field_order_regularity {p : WithTop ℕ} {M Λ β : ℝ}
    (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β)
    (hreg : P.HigherRegularity p (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ p) (x : X) :
    ContDiff ℝ r (P.lowerGradientField x) ∧
    ∀ u v, ‖iteratedFDeriv ℝ r (P.lowerGradientField x) u -
      iteratedFDeriv ℝ r (P.lowerGradientField x) v‖ ≤
        fieldDerivativeBudget b M Λ β r * ‖u-v‖ := by
  by_cases hr1 : r = 1
  · subst r
    refine ⟨P.lowerGradientField_contDiff_one x, ?_⟩
    intro u v
    exact (P.lowerGradientField_iterated_one_lipschitz x u v).trans
      (mul_le_mul_of_nonneg_right (baseline_le_fieldDerivativeBudget M Λ hβ 1) (norm_nonneg _))
  · have hr2 : 2 ≤ r := by omega
    obtain ⟨_, hg, _, hb⟩ := hreg (r-1) (by omega)
      (by simpa only [Nat.sub_add_cancel hr] using hrp) x
    have he : r-1+2 = r+1 := by omega
    rw [show r-1+1=r by omega, he] at hb
    refine ⟨?_, ?_⟩
    · convert hg using 1
      norm_cast
      omega
    intro u v
    have hbound := hb u v
    simp only [derivativeEnvelope, if_neg (show ¬r+1 ≤ 2 by omega)] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right (original_le_fieldDerivativeBudget hM hΛ r)
      (norm_nonneg _))

open ChebyshevDifferentiation DifferentiationBias

omit [InnerProductSpace ℝ Y] [CompleteSpace Y] in
theorem field_coefficient_le {M Λ β V : ℝ} (_hV : 0 ≤ V) (r : ℕ) (v : Y)
    (hv : ‖v‖ ≤ V) :
    fieldDerivativeBudget b M Λ β r * ‖v‖ ^ (r+1) / ((r+1).factorial : ℝ) ≤
      taylorCoefficient r (normalizedAmplitude b M) (normalizedFrequency Λ * V) β := by
  have hp := pow_le_pow_left₀ (norm_nonneg v) hv (r+1)
  have hb := fieldDerivativeBudget_pos (b := b) M Λ β r
  have hfac : (0 : ℝ) < (r+1).factorial := by positivity
  calc
    _ ≤ fieldDerivativeBudget b M Λ β r * V ^ (r+1) / ((r+1).factorial : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hb.le) hfac.le
    _ = _ := by
      unfold fieldDerivativeBudget taylorCoefficient
      rw [mul_pow, Real.rpow_sub hfac β 1, Real.rpow_one]
      ring

/-- The actual deterministic query rule, with the exact manuscript weights. -/
def gradientDifference (x : X) (y v : Y) (k : ℕ) (h : ℝ) : Joint X Y :=
  ∑ i, explicitWeight k h i • P.grad_g (pack x (y + (h * node (2*k+1) i) • v))

/-- Source eq:Zbias, now obtained from the original Population fields. -/
theorem gradientDifference_bias {p : WithTop ℕ} {M Λ β V : ℝ}
    (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) (hV : 0 ≤ V)
    (hreg : P.HigherRegularity p (derivativeEnvelope b M Λ β))
    (k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ 2*k+1) (hrp : (r : WithTop ℕ) ≤ p)
    {h : ℝ} (hh : 0 < h) (x : X) (y v : Y) (hv : ‖v‖ ≤ V) :
    ‖P.gradientDifference x y v k h - pack (P.gxy x y v) (P.gyy x y v)‖ ≤
      (2*k+1 : ℕ) * taylorCoefficient r (normalizedAmplitude b M)
        (normalizedFrequency Λ * V) β * h ^ r := by
  obtain ⟨hregF, hLip⟩ := P.field_order_regularity hM hΛ hβ hreg r hr hrp x
  have he := chebyshev_bias_frechet k r hh
    (fieldDerivativeBudget_pos (b := b) M Λ β r).le hr hrk
    (P.lowerGradientField x) hregF hLip y v
  rw [(P.lowerGradientField_hasFDerivAt x y).fderiv] at he
  have hcoef := field_coefficient_le (b := b) (M := M) (Λ := Λ) (β := β) hV r v hv
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef (by positivity : (0 : ℝ) ≤ (2*k+1 : ℕ)))
    (pow_nonneg hh.le r)
  calc
    _ ≤ (2*k+1 : ℕ) * (fieldDerivativeBudget b M Λ β r * ‖v‖ ^ (r+1)) *
        h ^ r / ((r+1).factorial : ℝ) := he
    _ ≤ _ := by convert hb using 1; ring

def stencilHalfOrder (r : ℕ) : ℕ := r / 2
def stencilDegree (r : ℕ) : ℕ := 2 * stencilHalfOrder r + 1

theorem stencilDegree_bounds (r : ℕ) : r ≤ stencilDegree r ∧ stencilDegree r ≤ r+1 := by
  unfold stencilDegree stencilHalfOrder
  omega

def populationRadius (b : Budgets) (M Λ β V a : ℝ) (r : ℕ) : ℝ :=
  differentiationRadius r (stencilDegree r) (normalizedAmplitude b M)
    (normalizedFrequency Λ * V) β a

theorem normalizedFrequency_mul_one_le {Λ V : ℝ} (hV : 1 ≤ V) :
    1 ≤ normalizedFrequency Λ * V := by
  nlinarith [normalizedFrequency_one_le Λ]

theorem populationRadius_pos {M Λ β V a : ℝ} (hV : 1 ≤ V) (ha : 0 < a) (r : ℕ) :
    0 < populationRadius b M Λ β V a r := by
  exact differentiationRadius_pos (by unfold stencilDegree; omega)
    (zero_lt_one.trans_le (normalizedAmplitude_one_le (b := b) M))
    (zero_lt_one.trans_le (normalizedFrequency_mul_one_le hV)) ha β

/-- The source's explicit radius enforces the desired bias at every finite
available smoothness order, with no restrictions on the queried lower points. -/
theorem populationRadius_bias {p : WithTop ℕ} {M Λ β V a : ℝ}
    (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) (hV : 1 ≤ V) (ha : 0 < a)
    (hreg : P.HigherRegularity p (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ p)
    (x : X) (y v : Y) (hv : ‖v‖ ≤ V) :
    ‖P.gradientDifference x y v (stencilHalfOrder r) (populationRadius b M Λ β V a r) -
      pack (P.gxy x y v) (P.gyy x y v)‖ ≤ a := by
  have he := P.gradientDifference_bias hM hΛ hβ (zero_le_one.trans hV) hreg
    (stencilHalfOrder r) r hr (stencilDegree_bounds r).1 hrp
    (populationRadius_pos (b := b) (M := M) (Λ := Λ) (β := β) hV ha r) x y v hv
  exact he.trans_eq (differentiationRadius_bias_exact hr
    (hr.trans (stencilDegree_bounds r).1)
    (zero_lt_one.trans_le (normalizedAmplitude_one_le (b := b) M))
    (zero_lt_one.trans_le (normalizedFrequency_mul_one_le hV)) ha β)

/-- Source lem:W for the same explicit weights and radius used by the actual
gradient query rule. The constant is independent of r and p. -/
theorem populationRadius_weight_bound {M Λ β V a : ℝ} (hV : 1 ≤ V) (ha : 0 < a)
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ i, |explicitWeight (stencilHalfOrder r) (populationRadius b M Λ β V a r) i|) ≤
      weightGrowthConstant (normalizedAmplitude b M) (normalizedFrequency Λ * V) β *
        (r : ℝ) ^ β * a ^ (-1 / (r : ℝ)) := by
  rw [explicit_weights_abs_sum _ (populationRadius_pos hV ha r)]
  change (stencilDegree r : ℝ) / differentiationRadius r (stencilDegree r)
    (normalizedAmplitude b M) (normalizedFrequency Λ * V) β a ≤ _
  rw [radius_weight_formula hr (hr.trans (stencilDegree_bounds r).1)
    (zero_lt_one.trans_le (normalizedAmplitude_one_le (b := b) M))
    (zero_lt_one.trans_le (normalizedFrequency_mul_one_le hV)) ha β]
  exact normalizedWeight_bound hr (stencilDegree_bounds r).1 (stencilDegree_bounds r).2
    (normalizedAmplitude_one_le M) (normalizedFrequency_mul_one_le hV) ha β

/-- A single positive constant controls actual bias and actual l1 weights
simultaneously for every available finite r, including when p=∞. -/
theorem uniform_population_differentiation {p : WithTop ℕ} {M Λ β V : ℝ}
    (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) (hV : 1 ≤ V)
    (hreg : P.HigherRegularity p (derivativeEnvelope b M Λ β)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → (r : WithTop ℕ) ≤ p →
      ∀ (a : ℝ), 0 < a →
        0 < populationRadius b M Λ β V a r ∧
        (∀ (x : X) (y v : Y), ‖v‖ ≤ V →
          ‖P.gradientDifference x y v (stencilHalfOrder r) (populationRadius b M Λ β V a r) -
            pack (P.gxy x y v) (P.gyy x y v)‖ ≤ a) ∧
        (∑ i, |explicitWeight (stencilHalfOrder r) (populationRadius b M Λ β V a r) i|) ≤
          C * (r : ℝ) ^ β * a ^ (-1 / (r : ℝ)) := by
  refine ⟨weightGrowthConstant (normalizedAmplitude b M) (normalizedFrequency Λ * V) β,
    weightGrowthConstant_pos (normalizedAmplitude_one_le M) (normalizedFrequency_mul_one_le hV) β, ?_⟩
  intro r hr hrp a ha
  exact ⟨populationRadius_pos hV ha r,
    P.populationRadius_bias hM hΛ hβ hV ha hreg r hr hrp,
    populationRadius_weight_bound hV ha r hr⟩

end Smoothness2601.Population
