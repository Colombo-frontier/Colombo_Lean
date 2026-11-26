import HeavyTail.GaussianMixedCore
import HeavyTail.GaussianMomentModel

/-! The fixed-center form of manuscript `lem:mixed-exp`, with the necessary
explicit hypothesis `0 ≤ η` and a dimension-independent explicit constant. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

def mixedConstant (p : ℝ) : ℝ :=
  100 * (mixedWeakConstant * (2 : ℝ) ^ p + 4 * mixedQuadraticConstant)

theorem mixedConstant_pos (p : ℝ) : 0 < mixedConstant p := by
  unfold mixedConstant mixedWeakConstant mixedQuadraticConstant
  positivity

private theorem weighted_three_le {A B U X Y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    A * U + B * X + 4 * B * Y ≤ (A + 4 * B) * (U + X + Y) := by
  nlinarith [mul_nonneg hA hX, mul_nonneg hA hY, mul_nonneg hB hU, mul_nonneg hB hX]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def fixedMixedExp (ξ : Ω → E) (b v₀ : E) (η a ε : ℝ) (w : Ω × E) : ℝ :=
  Real.exp (ε * (HeavyTail.clip (η * ⟪b + ξ w.1, v₀ + a • w.2⟫_ℝ) -
    η * ⟪b, v₀ + a • w.2⟫_ℝ))

theorem fixedMixedExp_eq_core (ξ : Ω → E) (b v₀ : E) (η a ε : ℝ) :
    fixedMixedExp E ξ b v₀ η a ε =
      coreExp E ξ (η * ⟪b, v₀⟫_ℝ) ((η * a) • b) (η • v₀) (η * a) ε := by
  funext w
  unfold fixedMixedExp coreExp
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
    real_inner_comm v₀ (ξ w.1)]
  congr 2 <;> congr 1 <;> ring

theorem fixedMixedExp_integrable {ξ : Ω → E} (hξ : Measurable ξ)
    (b v₀ : E) (η a ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    Integrable (fixedMixedExp E ξ b v₀ η a ε) (P.prod (euclideanGaussianLaw E)) := by
  rw [fixedMixedExp_eq_core]
  exact coreExp_integrable E hξ _ _ _ _ _ hε

theorem fixed_mixed_exp_bound {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hcenter : (∫ ω, ξ ω ∂P) = 0)
    {p s V M R η a : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hweak : ∀ v : E, ‖v‖ = 1 → (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ s ^ p)
    (b v₀ : E) (hb : ‖b‖ ≤ M) (hv₀ : ‖v₀‖ ≤ 2 * R)
    (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    (∫ w, fixedMixedExp E ξ b v₀ η a ε w ∂P.prod (euclideanGaussianLaw E)) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  have hR : 0 ≤ R := ha.le.trans haR
  have hM : 0 ≤ M := (norm_nonneg b).trans hb
  have hV0 : 0 ≤ V := (integral_nonneg fun ω => sq_nonneg ‖ξ ω‖).trans hV
  have hηa : 0 ≤ η * a := mul_nonneg hη ha.le
  have ht : |η * ⟪b, v₀⟫_ℝ| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg hη]
    have hinner := (abs_real_inner_le_norm b v₀).trans
      (mul_le_mul hb hv₀ (norm_nonneg _) hM)
    have hh := mul_le_mul_of_nonneg_left hinner hη
    nlinarith
  have hdnorm : ‖(η * a) • b‖ = η * a * ‖b‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hηa]
  have hdM : ‖(η * a) • b‖ ≤ η * a * M := by
    rw [hdnorm]
    exact mul_le_mul_of_nonneg_left hb hηa
  have hsmall : ‖(η * a) • b‖ ≤ 1 / 16 := by
    calc
      _ ≤ η * a * M := hdM
      _ ≤ η * R * M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haR hη) hM
      _ = η * M * R := by ring
      _ ≤ 1 / 16 := htune
  have hd : 4 * ‖(η * a) • b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ((η * a) • b)]
  have hd2 : ‖(η * a) • b‖ ^ 2 ≤ η ^ 2 * a ^ 2 * M ^ 2 := by
    nlinarith [norm_nonneg ((η * a) • b), mul_nonneg hηa hM]
  have hpint := directional_power_integrable E hξ h2 (by linarith : 0 ≤ p) hp2 (η • v₀)
  have hW := unit_direction_bound E (ξ := ξ) (by linarith : 0 < p) hs.le hweak (η • v₀)
  have hnormv : ‖η • v₀‖ ≤ η * (2 * R) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left hv₀ hη
  have hscale : (s * ‖η • v₀‖) ^ p ≤ (2 : ℝ) ^ p * (η ^ p * (s * R) ^ p) := by
    have hn := Real.rpow_le_rpow (mul_nonneg hs.le (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hnormv hs.le) (by linarith : 0 ≤ p)
    have he : s * (η * (2 * R)) = 2 * (η * (s * R)) := by ring
    rw [he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg hη (mul_nonneg hs.le hR)), Real.mul_rpow hη (mul_nonneg hs.le hR)] at hn
    exact hn
  have hW' := hW.trans hscale
  have hcore := gaussian_core_exp E hξ h2 hcenter hp hp2 ht
    ((η * a) • b) (η • v₀) hd (η * a) ε hε hpint
  rw [← fixedMixedExp_eq_core] at hcore
  apply hcore.trans
  apply Real.exp_le_exp.mpr
  have hcw : 0 ≤ mixedWeakConstant := by unfold mixedWeakConstant; positivity
  have hcq : 0 ≤ mixedQuadraticConstant := by unfold mixedQuadraticConstant; positivity
  have hw := mul_le_mul_of_nonneg_left hW' hcw
  have hq := mul_le_mul_of_nonneg_left hV
    (mul_nonneg hcq (sq_nonneg (η * a)))
  have hdq := mul_le_mul_of_nonneg_left hd2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hcq)
  have hcombine := weighted_three_le
    (A := mixedWeakConstant * (2 : ℝ) ^ p) (B := mixedQuadraticConstant)
    (U := η ^ p * (s * R) ^ p) (X := η ^ 2 * a ^ 2 * V) (Y := η ^ 2 * a ^ 2 * M ^ 2)
    (by positivity) hcq (by positivity) (by positivity) (by positivity)
  unfold mixedConstant
  nlinarith

end HeavyTail.GaussianEstimates
