import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! Measure-theoretic ingredients for the rejection and testing arguments.
All probability statements use actual measures and Bochner integrals. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HeavyTail
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The expectation-to-probability conversion in the Hamming argument. -/
theorem hamming_probability_lower {J : Ω → ℝ} {k : ℝ}
    (hk : 0 < k) (hJ : Measurable J) (hJi : Integrable J P)
    (hbound : ∀ ω, J ω ≤ k) (hmean : 7 * k / 16 ≤ ∫ ω, J ω ∂P) :
    1 / 4 ≤ P.real {ω | k / 4 ≤ J ω} := by
  let S : Set Ω := {ω | k / 4 ≤ J ω}
  have hS : MeasurableSet S := hJ measurableSet_Ici
  have hi : Integrable (S.indicator (fun _ : Ω => (3 * k / 4))) P :=
    (integrable_const _).indicator hS
  have hb : ∀ ω, J ω ≤ k / 4 + S.indicator (fun _ : Ω => (3 * k / 4)) ω := by
    intro ω
    by_cases h : ω ∈ S
    · simp only [indicator_of_mem h]
      linarith [hbound ω]
    · simp only [indicator_of_not_mem h]
      have hh : ¬ k / 4 ≤ J ω := h
      linarith
  have h := integral_mono hJi ((integrable_const _).add hi) hb
  change (∫ ω, J ω ∂P) ≤ ∫ ω, k / 4 + S.indicator (fun _ : Ω => 3 * k / 4) ω ∂P at h
  rw [integral_add (integrable_const _) hi, integral_const,
    integral_indicator hS, integral_const] at h
  simp only [measureReal_univ_eq_one, one_smul, measureReal_restrict_apply_univ,
    smul_eq_mul] at h
  dsimp [S] at h
  nlinarith

omit [IsProbabilityMeasure P] in
/-- Centering removes the mean-times-rejection-probability term exactly. -/
theorem accepted_centered_mean_identity {X : Ω → ℝ} {S : Set Ω}
    (hS : MeasurableSet S) (hX : Integrable X P) (hzero : ∫ ω, X ω ∂P = 0) :
    (∫ ω in S, X ω ∂P) / P.real S =
      -(∫ ω in Sᶜ, X ω ∂P) / P.real S := by
  have h := integral_add_compl hS hX
  rw [hzero] at h
  congr 1
  linarith

/-- Hölder control of a directional mean on any measurable rejection event. -/
theorem restricted_mean_holder {X : Ω → ℝ} {S : Set Ω} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hS : MeasurableSet S)
    (hX : MemLp X (ENNReal.ofReal p) P) :
    |∫ ω in S, X ω ∂P| ≤
      (∫ ω, |X ω| ^ p ∂P) ^ (1 / p) * (P.real S) ^ (1 / q) := by
  have hi : MemLp (S.indicator (fun _ : Ω => (1 : ℝ))) (ENNReal.ofReal q) P :=
    (memLp_const (1 : ℝ)).indicator hS
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq hX hi
  have hn : (fun ω => ‖X ω‖ * ‖S.indicator (fun _ : Ω => (1 : ℝ)) ω‖) =
      S.indicator (fun ω => |X ω|) := by
    funext ω
    by_cases h : ω ∈ S <;> simp [h, Real.norm_eq_abs]
  have hp : (fun ω => ‖S.indicator (fun _ : Ω => (1 : ℝ)) ω‖ ^ q) =
      S.indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    by_cases h : ω ∈ S <;> simp [h, Real.zero_rpow hpq.symm.ne_zero]
  rw [hn, hp, integral_indicator hS, integral_indicator hS, integral_const] at hh
  simp only [measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
    Real.norm_eq_abs] at hh
  have hnorm : |∫ ω in S, X ω ∂P| ≤ ∫ ω in S, |X ω| ∂P := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := P.restrict S) X)
  exact hnorm.trans hh

/-- The directional rejection bias, including its normalization denominator. -/
theorem accepted_directional_bias {X : Ω → ℝ} {S : Set Ω} {p q s : ℝ}
    (hpq : p.HolderConjugate q) (hS : MeasurableSet S)
    (hX : MemLp X (ENNReal.ofReal p) P) (hXi : Integrable X P)
    (hzero : ∫ ω, X ω ∂P = 0) (hs : 0 ≤ s)
    (hmoment : ∫ ω, |X ω| ^ p ∂P ≤ s ^ p) (haccept : 0 < P.real S) :
    |(∫ ω in S, X ω ∂P) / P.real S| ≤
      s * (P.real Sᶜ) ^ (1 / q) / (1 - P.real Sᶜ) := by
  have hroot : (∫ ω, |X ω| ^ p ∂P) ^ (1 / p) ≤ s := by
    calc
      _ ≤ (s ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _))
          hmoment hpq.one_div_nonneg
      _ = s := by rw [← Real.rpow_mul hs, mul_one_div_cancel hpq.ne_zero, Real.rpow_one]
  have hmass := measureReal_add_measureReal_compl (μ := P) hS
  simp only [measureReal_univ_eq_one] at hmass
  have hden : 1 - P.real Sᶜ = P.real S := by linarith
  rw [accepted_centered_mean_identity hS hXi hzero, abs_div, abs_neg,
    abs_of_pos haccept, hden]
  apply div_le_div_of_nonneg_right _ haccept.le
  exact (restricted_mean_holder hpq hS.compl hX).trans
    (mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg (measureReal_nonneg) _))

/-- Markov's inequality on a specified measurable event, in real-valued form. -/
theorem event_moment_bound {X : Ω → ℝ} {S : Set Ω} {t p : ℝ}
    (hS : MeasurableSet S) (hp : 0 ≤ p) (ht : 0 < t)
    (hX : Integrable (fun ω => |X ω| ^ p) P) (hlarge : ∀ ω ∈ S, t ≤ |X ω|) :
    P.real S ≤ (∫ ω, |X ω| ^ p ∂P) / t ^ p := by
  have hset : (∫ _ in S, t ^ p ∂P) ≤ ∫ ω in S, |X ω| ^ p ∂P :=
    integral_mono_ae (integrable_const _) hX.integrableOn
      ((ae_restrict_mem hS).mono (fun ω hω => Real.rpow_le_rpow ht.le (hlarge ω hω) hp))
  have hfull : (∫ ω in S, |X ω| ^ p ∂P) ≤ ∫ ω, |X ω| ^ p ∂P :=
    integral_mono_measure P.restrict_le_self
      (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg _) _)) hX
  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hset
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ht p)).mpr (hset.trans hfull)

/-- The norm-defined rejection event has the manuscript Markov bound. -/
theorem norm_rejection_probability {E : Type*} [NormedAddCommGroup E]
    {ζ : Ω → E} {b : E} {τ L p : ℝ} (hp : 0 ≤ p) (hτ : 0 < τ) (hL : 0 ≤ L)
    (hb : ‖b‖ ≤ τ / 2)
    (hS : MeasurableSet {ω | τ < ‖b + ζ ω‖})
    (hζ : Integrable (fun ω => ‖ζ ω‖ ^ p) P)
    (hmoment : ∫ ω, ‖ζ ω‖ ^ p ∂P ≤ L ^ p) :
    P.real {ω | τ < ‖b + ζ ω‖} ≤ (2 * L / τ) ^ p := by
  have hbound := event_moment_bound (X := fun ω => ‖ζ ω‖) hS hp
    (by linarith : 0 < τ / 2) (by simpa only [abs_norm] using hζ)
    (fun ω hω => by
      simp only [abs_norm]
      have hn := norm_add_le b (ζ ω)
      change τ < ‖b + ζ ω‖ at hω
      linarith)
  simp only [abs_norm] at hbound
  calc
    _ ≤ (∫ ω, ‖ζ ω‖ ^ p ∂P) / (τ / 2) ^ p := hbound
    _ ≤ L ^ p / (τ / 2) ^ p :=
      div_le_div_of_nonneg_right hmoment (Real.rpow_nonneg (by linarith) _)
    _ = (2 * L / τ) ^ p := by
      rw [← Real.div_rpow hL (by linarith : 0 ≤ τ / 2)]
      congr 1
      ring

/-- The manuscript's fixed acceptance probability, with explicit constants. -/
theorem norm_rejection_probability_sixteenth {E : Type*} [NormedAddCommGroup E]
    {ζ : Ω → E} {b : E} {τ L G p : ℝ}
    (hp : 1 < p) (hG : 0 ≤ G) (hL : 0 < L) (hτ : 64 * (4 * G + L) ≤ τ)
    (hb : ‖b‖ ≤ 4 * G) (hS : MeasurableSet {ω | τ < ‖b + ζ ω‖})
    (hζ : Integrable (fun ω => ‖ζ ω‖ ^ p) P)
    (hmoment : ∫ ω, ‖ζ ω‖ ^ p ∂P ≤ L ^ p) :
    P.real {ω | τ < ‖b + ζ ω‖} ≤ 1 / 16 := by
  have ht : 0 < τ := by linarith
  have hratio : 2 * L / τ ≤ 1 / 16 := by
    apply (div_le_iff₀ ht).mpr
    linarith
  calc
    _ ≤ (2 * L / τ) ^ p := norm_rejection_probability (by linarith) ht hL.le
      (by linarith) hS hζ hmoment
    _ ≤ 2 * L / τ := Real.rpow_le_self_of_le_one (by positivity) (by linarith) hp.le
    _ ≤ 1 / 16 := hratio

section VectorBias
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] [IsProbabilityMeasure P] in
theorem norm_le_of_unit_inner_bound {x : E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v : E, ‖v‖ = 1 → |inner (𝕜 := ℝ) v x| ≤ C) : ‖x‖ ≤ C := by
  by_cases hx : x = 0
  · simpa [hx] using hC
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    exact inv_mul_cancel₀ hn
  have hh := h (‖x‖⁻¹ • x) hunit
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at hh
  have heq : ‖x‖⁻¹ * ‖x‖ ^ 2 = ‖x‖ := by field_simp; ring
  simpa [heq, abs_of_nonneg (norm_nonneg x)] using hh

/-- Duality converts the directional bound into a dimension-free vector bias. -/
theorem accepted_vector_bias {ζ : Ω → E} {S : Set Ω} {p q s : ℝ}
    (hpq : p.HolderConjugate q) (hS : MeasurableSet S)
    (hζ : Integrable ζ P) (hzero : ∫ ω, ζ ω ∂P = 0) (hs : 0 ≤ s)
    (hweakLp : ∀ v : E, ‖v‖ = 1 → MemLp (fun ω => inner (𝕜 := ℝ) v (ζ ω)) (ENNReal.ofReal p) P)
    (hweak : ∀ v : E, ‖v‖ = 1 → ∫ ω, |inner (𝕜 := ℝ) v (ζ ω)| ^ p ∂P ≤ s ^ p)
    (haccept : 0 < P.real S) :
    ‖(P.real S)⁻¹ • (∫ ω in S, ζ ω ∂P)‖ ≤
      s * (P.real Sᶜ) ^ (1 / q) / (1 - P.real Sᶜ) := by
  have hmass := measureReal_add_measureReal_compl (μ := P) hS
  simp only [measureReal_univ_eq_one] at hmass
  apply norm_le_of_unit_inner_bound
  · apply div_nonneg (mul_nonneg hs (Real.rpow_nonneg measureReal_nonneg _))
    linarith
  intro v hv
  have hcenter : (∫ ω, inner (𝕜 := ℝ) v (ζ ω) ∂P) = 0 := by
    rw [integral_inner hζ, hzero, inner_zero_right]
  have h := accepted_directional_bias hpq hS (hweakLp v hv) (hζ.const_inner v)
    hcenter hs (hweak v hv) haccept
  rw [integral_inner hζ.integrableOn] at h
  simpa only [real_inner_smul_right, div_eq_mul_inv, mul_comm] using h
end VectorBias

end HeavyTail
