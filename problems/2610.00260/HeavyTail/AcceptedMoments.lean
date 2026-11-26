import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
Actual integral estimates for the accepted law in Lemma `lem:accept`.
The probability measure Q is explicit; bounds assumed below are on the
uncentered accepted noise, never on its centered second or p-th moments.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open scoped InnerProductSpace
namespace HeavyTail

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem integral_centered_norm_sq_identity {ξ : Ω → E}
    (hξ : Integrable ξ Q) (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) Q) :
    (∫ ω, ‖ξ ω - ∫ z, ξ z ∂Q‖ ^ 2 ∂Q) =
      (∫ ω, ‖ξ ω‖ ^ 2 ∂Q) - ‖∫ z, ξ z ∂Q‖ ^ 2 := by
  let m := ∫ z, ξ z ∂Q
  have hi : Integrable (fun ω => ⟪m, ξ ω⟫_ℝ) Q := hξ.const_inner m
  calc
    (∫ ω, ‖ξ ω - m‖ ^ 2 ∂Q) =
        ∫ ω, ‖ξ ω‖ ^ 2 - 2 * ⟪m, ξ ω⟫_ℝ + ‖m‖ ^ 2 ∂Q := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [norm_sub_sq_real, real_inner_comm]
    _ = (∫ ω, ‖ξ ω‖ ^ 2 - 2 * ⟪m, ξ ω⟫_ℝ ∂Q) + ∫ _ : Ω, ‖m‖ ^ 2 ∂Q :=
      integral_add (h2.sub (hi.const_mul 2)) (integrable_const _)
    _ = (∫ ω, ‖ξ ω‖ ^ 2 ∂Q) - ‖m‖ ^ 2 := by
      have hsplit : (∫ ω, ‖ξ ω‖ ^ 2 - 2 * ⟪m, ξ ω⟫_ℝ ∂Q) =
          (∫ ω, ‖ξ ω‖ ^ 2 ∂Q) - ∫ ω, 2 * ⟪m, ξ ω⟫_ℝ ∂Q :=
        integral_sub h2 (hi.const_mul 2)
      rw [hsplit, integral_const_mul, integral_inner hξ, integral_const]
      simp only [measureReal_univ_eq_one, one_smul]
      change _ - 2 * ⟪m, m⟫_ℝ + ‖m‖ ^ 2 = _
      rw [real_inner_self_eq_norm_sq]
      ring

theorem integral_centered_norm_sq_le {ξ : Ω → E}
    (hξ : Integrable ξ Q) (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) Q) :
    (∫ ω, ‖ξ ω - ∫ z, ξ z ∂Q‖ ^ 2 ∂Q) ≤ ∫ ω, ‖ξ ω‖ ^ 2 ∂Q := by
  rw [integral_centered_norm_sq_identity hξ h2]
  exact sub_le_self _ (sq_nonneg _)

theorem bounded_square_le_rpow {x B p : ℝ} (hx : 0 ≤ x) (hxB : x ≤ B)
    (hp : 0 < p) (hp2 : p ≤ 2) : x ^ 2 ≤ B ^ (2 - p) * x ^ p := by
  by_cases hz : x = 0
  · simp [hz, Real.zero_rpow hp.ne']
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have he : x ^ 2 = x ^ p * x ^ (2 - p) := by
      rw [← Real.rpow_add hxp]
      simp only [add_sub_cancel, Real.rpow_two]
    rw [he]
    calc
      x ^ p * x ^ (2 - p) ≤ x ^ p * B ^ (2 - p) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxB (sub_nonneg.mpr hp2))
          (Real.rpow_nonneg hx p)
      _ = _ := mul_comm _ _

theorem integrable_bounded_norm_rpow {ξ : Ω → E} {B p : ℝ}
    (hξ : AEStronglyMeasurable ξ Q) (hp : 0 ≤ p)
    (hbound : ∀ᵐ ω ∂Q, ‖ξ ω‖ ≤ B) :
    Integrable (fun ω => ‖ξ ω‖ ^ p) Q := by
  apply (integrable_const (B ^ p)).mono'
  · exact (Real.continuous_rpow_const hp).comp_aestronglyMeasurable hξ.norm
  · filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hω hp

theorem accepted_second_moment {ξ : Ω → E} {B p : ℝ}
    (hξ : AEStronglyMeasurable ξ Q) (hp : 0 < p) (hp2 : p ≤ 2)
    (hbound : ∀ᵐ ω ∂Q, ‖ξ ω‖ ≤ B) :
    (∫ ω, ‖ξ ω - ∫ z, ξ z ∂Q‖ ^ 2 ∂Q) ≤
      B ^ (2 - p) * (∫ ω, ‖ξ ω‖ ^ p ∂Q) := by
  have hi : Integrable ξ Q := (integrable_const B).mono' hξ hbound
  have hi2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) Q := by
    simpa only [Real.rpow_two] using
      integrable_bounded_norm_rpow hξ (by norm_num : (0 : ℝ) ≤ 2) hbound
  have hip := integrable_bounded_norm_rpow hξ hp.le hbound
  calc
    _ ≤ ∫ ω, ‖ξ ω‖ ^ 2 ∂Q := integral_centered_norm_sq_le hi hi2
    _ ≤ ∫ ω, B ^ (2 - p) * ‖ξ ω‖ ^ p ∂Q := by
      apply integral_mono_ae hi2 (hip.const_mul _)
      filter_upwards [hbound] with ω hω
      exact bounded_square_le_rpow (norm_nonneg _) hω hp hp2
    _ = _ := integral_const_mul _ _

theorem accepted_second_moment_bound {ξ : Ω → E} {τ p L a₀ : ℝ}
    (hξ : AEStronglyMeasurable ξ Q) (hτ : 0 ≤ τ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hbound : ∀ᵐ ω ∂Q, ‖ξ ω‖ ≤ 3 * τ / 2)
    (hmoment : (∫ ω, ‖ξ ω‖ ^ p ∂Q) ≤ L ^ p / (1 - a₀)) :
    (∫ ω, ‖ξ ω - ∫ z, ξ z ∂Q‖ ^ 2 ∂Q) ≤
      (3 * τ / 2) ^ (2 - p) * (L ^ p / (1 - a₀)) := by
  exact (accepted_second_moment hξ (by linarith) hp2 hbound).trans
    (mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg (by positivity) _))

theorem abs_sub_rpow_le (x y : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    |x - y| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|x| ^ p + |y| ^ p) := by
  have hN := NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨|x|, abs_nonneg x⟩ : NNReal) (⟨|y|, abs_nonneg y⟩ : NNReal) hp
  have hR : (|x| + |y|) ^ p ≤ (2 : ℝ) ^ (p - 1) * (|x| ^ p + |y| ^ p) := by
    exact_mod_cast hN
  have hab : |x - y| ≤ |x| + |y| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  exact (Real.rpow_le_rpow (abs_nonneg _) hab (by linarith)).trans hR

theorem abs_integral_rpow_le {X : Ω → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hX : Integrable X Q)
    (hXp : Integrable (fun ω => |X ω| ^ p) Q) :
    |∫ ω, X ω ∂Q| ^ p ≤ ∫ ω, |X ω| ^ p ∂Q := by
  have hJ := (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn
    isClosed_Ici (Filter.Eventually.of_forall fun ω => abs_nonneg (X ω)) hX.abs hXp
  have hn : |∫ ω, X ω ∂Q| ≤ ∫ ω, |X ω| ∂Q := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm X
  exact (Real.rpow_le_rpow (abs_nonneg _) hn (by linarith)).trans hJ

/-- Centering costs at most 2^p, with no bound assumed on centered moments. -/
theorem accepted_weak_centering {X : Ω → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hX : Integrable X Q)
    (hXp : Integrable (fun ω => |X ω| ^ p) Q) :
    (∫ ω, |X ω - ∫ z, X z ∂Q| ^ p ∂Q) ≤
      (2 : ℝ) ^ p * (∫ ω, |X ω| ^ p ∂Q) := by
  let m := ∫ z, X z ∂Q
  let K := (2 : ℝ) ^ (p - 1)
  have hK : 0 ≤ K := Real.rpow_nonneg (by norm_num) _
  have hdom : Integrable (fun ω => K * (|X ω| ^ p + |m| ^ p)) Q :=
    (hXp.add (integrable_const _)).const_mul K
  have hpoint (ω : Ω) : |X ω - m| ^ p ≤ K * (|X ω| ^ p + |m| ^ p) :=
    abs_sub_rpow_le (X ω) m hp
  have hcenter : Integrable (fun ω => |X ω - m| ^ p) Q := by
    apply hdom.mono'
    · exact (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp_aestronglyMeasurable
        (hX.aestronglyMeasurable.sub aestronglyMeasurable_const).norm
    · exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpoint ω
  have hmean : |m| ^ p ≤ ∫ ω, |X ω| ^ p ∂Q := abs_integral_rpow_le hp hX hXp
  have htwo : K * 2 = (2 : ℝ) ^ p := by
    calc
      K * 2 = (2 : ℝ) ^ ((p - 1) + 1) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        simp only [Real.rpow_one, K]
      _ = (2 : ℝ) ^ p := by congr 1; ring
  calc
    (∫ ω, |X ω - m| ^ p ∂Q) ≤ ∫ ω, K * (|X ω| ^ p + |m| ^ p) ∂Q :=
      integral_mono hcenter hdom hpoint
    _ = K * ((∫ ω, |X ω| ^ p ∂Q) + |m| ^ p) := by
      rw [integral_const_mul, integral_add hXp (integrable_const _), integral_const]
      simp only [measureReal_univ_eq_one, one_smul]
    _ ≤ K * ((∫ ω, |X ω| ^ p ∂Q) + (∫ ω, |X ω| ^ p ∂Q)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hmean _) hK
    _ = _ := by rw [← htwo]; ring

/-- Exact normalization of the actual restricted probability law. -/
theorem integral_cond_eq_div (X : Ω → ℝ) (S : Set Ω) :
    (∫ ω, X ω ∂ProbabilityTheory.cond Q S) = (∫ ω in S, X ω ∂Q) / Q.real S := by
  rw [ProbabilityTheory.cond, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, Measure.real, div_eq_mul_inv, mul_comm]

theorem conditional_nonnegative_moment_le {X : Ω → ℝ} (S : Set Ω)
    (hX : Integrable X Q) (hpos : ∀ᵐ ω ∂Q, 0 ≤ X ω) :
    (∫ ω, X ω ∂ProbabilityTheory.cond Q S) ≤ (∫ ω, X ω ∂Q) / Q.real S := by
  rw [integral_cond_eq_div]
  exact div_le_div_of_nonneg_right (setIntegral_le_integral hX hpos) (measureReal_nonneg)

theorem conditional_weak_centering {X : Ω → ℝ} {S : Set Ω} {p : ℝ}
    (hSpos : Q S ≠ 0) (hp : 1 ≤ p) (hX : Integrable X Q)
    (hXp : Integrable (fun ω => |X ω| ^ p) Q) :
    (∫ ω, |X ω - ∫ z, X z ∂ProbabilityTheory.cond Q S| ^ p
      ∂ProbabilityTheory.cond Q S) ≤
      (2 : ℝ) ^ p * (∫ ω, |X ω| ^ p ∂Q) / Q.real S := by
  letI : IsProbabilityMeasure (ProbabilityTheory.cond Q S) :=
    ProbabilityTheory.cond_isProbabilityMeasure hSpos
  have hcX : Integrable X (ProbabilityTheory.cond Q S) :=
    hX.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hSpos)
  have hcXp : Integrable (fun ω => |X ω| ^ p) (ProbabilityTheory.cond Q S) :=
    hXp.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hSpos)
  have h := accepted_weak_centering hp hcX hcXp
  have hn := conditional_nonnegative_moment_le S hXp
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg (X ω)) p)
  have hm := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
  exact h.trans (by simpa only [mul_div_assoc] using hm)

/-- The trace estimate directly from the original law, restricted to an acceptance set.
    This is a measure-theoretic statement, not a construction of the adaptive sampler. -/
theorem conditional_second_moment {ξ : Ω → E} {S : Set Ω} {p B L : ℝ}
    (hS : MeasurableSet S) (hSpos : Q S ≠ 0) (hp : 0 < p) (hp2 : p ≤ 2)
    (hB : 0 ≤ B) (hξ : AEStronglyMeasurable ξ Q)
    (hbound : ∀ ω ∈ S, ‖ξ ω‖ ≤ B)
    (hXp : Integrable (fun ω => ‖ξ ω‖ ^ p) Q)
    (hmoment : (∫ ω, ‖ξ ω‖ ^ p ∂Q) ≤ L ^ p) :
    (∫ ω, ‖ξ ω - ∫ z, ξ z ∂ProbabilityTheory.cond Q S‖ ^ 2
      ∂ProbabilityTheory.cond Q S) ≤ B ^ (2 - p) * (L ^ p / Q.real S) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.cond Q S) :=
    ProbabilityTheory.cond_isProbabilityMeasure hSpos
  have hcξ : AEStronglyMeasurable ξ (ProbabilityTheory.cond Q S) :=
    hξ.restrict.smul_measure _
  have hcb : ∀ᵐ ω ∂ProbabilityTheory.cond Q S, ‖ξ ω‖ ≤ B := by
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem hS] with ω hω
    exact hbound ω hω
  have h := accepted_second_moment hcξ hp hp2 hcb
  have hn := conditional_nonnegative_moment_le S hXp
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg (ξ ω)) p)
  have hn' := hn.trans (div_le_div_of_nonneg_right hmoment measureReal_nonneg)
  exact h.trans (mul_le_mul_of_nonneg_left hn' (Real.rpow_nonneg hB _))

theorem noise_norm_on_acceptance {b z : E} {τ : ℝ}
    (hb : ‖b‖ ≤ τ / 2) (hz : ‖b + z‖ ≤ τ) : ‖z‖ ≤ 3 * τ / 2 := by
  have he : b + z - b = z := by abel
  have hn := norm_sub_le (b + z) b
  rw [he] at hn
  linarith

theorem conditional_truncated_second_moment {ξ : Ω → E} {b : E} {τ p L : ℝ}
    (hτ : 0 ≤ τ) (hb : ‖b‖ ≤ τ / 2)
    (hS : MeasurableSet {ω | ‖b + ξ ω‖ ≤ τ})
    (hSpos : Q {ω | ‖b + ξ ω‖ ≤ τ} ≠ 0)
    (hp : 1 < p) (hp2 : p ≤ 2) (hξ : AEStronglyMeasurable ξ Q)
    (hXp : Integrable (fun ω => ‖ξ ω‖ ^ p) Q)
    (hmoment : (∫ ω, ‖ξ ω‖ ^ p ∂Q) ≤ L ^ p) :
    let A := {ω | ‖b + ξ ω‖ ≤ τ}
    let Qacc := ProbabilityTheory.cond Q A
    (∫ ω, ‖ξ ω - ∫ z, ξ z ∂Qacc‖ ^ 2 ∂Qacc) ≤
      (3 * τ / 2) ^ (2 - p) * (L ^ p / Q.real A) := by
  dsimp only
  exact conditional_second_moment hS hSpos (by linarith) hp2 (by positivity) hξ
    (fun ω hω => noise_norm_on_acceptance hb hω) hXp hmoment

theorem conditional_vector_weak_moment {ξ : Ω → E} {S : Set Ω} {p s : ℝ}
    (hSpos : Q S ≠ 0) (hp : 1 ≤ p) (hξ : Integrable ξ Q) (v : E)
    (hXp : Integrable (fun ω => |⟪v, ξ ω⟫_ℝ| ^ p) Q)
    (hmoment : (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂Q) ≤ s ^ p) :
    (∫ ω, |⟪v, ξ ω - ∫ z, ξ z ∂ProbabilityTheory.cond Q S⟫_ℝ| ^ p
      ∂ProbabilityTheory.cond Q S) ≤ (2 : ℝ) ^ p * s ^ p / Q.real S := by
  have hcξ : Integrable ξ (ProbabilityTheory.cond Q S) :=
    hξ.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hSpos)
  have he : (fun ω => |⟪v, ξ ω - ∫ z, ξ z ∂ProbabilityTheory.cond Q S⟫_ℝ| ^ p) =
      (fun ω => |⟪v, ξ ω⟫_ℝ - ∫ z, ⟪v, ξ z⟫_ℝ ∂ProbabilityTheory.cond Q S| ^ p) := by
    funext ω
    rw [inner_sub_right, integral_inner hcξ]
  rw [he]
  have h := conditional_weak_centering hSpos hp (hξ.const_inner v) hXp
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg (by norm_num) _)) measureReal_nonneg)

end HeavyTail
