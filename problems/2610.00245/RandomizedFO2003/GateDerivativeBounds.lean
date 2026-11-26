import RandomizedFO2003.ForcingDerivativeBounds
import RandomizedFO2003.RadialGate

namespace RandomizedFO2003.Primitives

open scoped BigOperators

theorem gate_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ q : ℝ, ‖iteratedFDeriv ℝ i gate q‖ ≤ C := by
  induction n with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro i hi q
    have hi0 : i = 0 := by omega
    rw [hi0, norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (gate_nonneg q)]
    exact gate_le_one q
  | succ n ih =>
    obtain ⟨C, hC, hb⟩ := ih
    obtain ⟨M, hM, hm⟩ := gate_derivative_bound (n + 1) (by omega)
    refine ⟨max C M, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro i hi q
    by_cases hin : i ≤ n
    · exact (hb i hin q).trans (le_max_left _ _)
    · have heq : i = n + 1 := by omega
      rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact (hm q).trans (le_max_right _ _)

noncomputable def gateJetConstant (n : ℕ) : ℝ := (gate_jet_bound n).choose

theorem gateJetConstant_pos (n : ℕ) : 0 < gateJetConstant n := (gate_jet_bound n).choose_spec.1

theorem gateJetConstant_spec (n i : ℕ) (hi : i ≤ n) (q : ℝ) :
    ‖iteratedFDeriv ℝ i gate q‖ ≤ gateJetConstant n := (gate_jet_bound n).choose_spec.2 i hi q

noncomputable def radialDerivativeJetConstant (n : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n + 1), radialDerivativeConstant i

theorem radialDerivativeJetConstant_pos (n : ℕ) : 0 < radialDerivativeJetConstant n := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), radialDerivativeConstant i :=
    Finset.sum_nonneg (fun i _ => (radialDerivativeConstant_pos i).le)
  unfold radialDerivativeJetConstant
  linarith

theorem radialDerivative_le_jet (n i : ℕ) (hi : i ≤ n) :
    radialDerivativeConstant i ≤ radialDerivativeJetConstant n := by
  have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (n + 1)) =>
    (radialDerivativeConstant_pos j).le) (Finset.mem_range.mpr (by omega : i < n + 1))
  exact hs.trans (le_add_of_nonneg_left (by norm_num))

/-- Dimension-free control of the inner map in the gate's chain rule. -/
noncomputable def readoutPowerConstant (n : ℕ) (B α : ℝ) : ℝ :=
  1 + radialDerivativeJetConstant n * (B / α)

theorem readoutPowerConstant_ge_one (n : ℕ) {B α : ℝ} (hB : 0 < B) (hα : 0 < α) :
    1 ≤ readoutPowerConstant n B α := by
  unfold readoutPowerConstant
  have hc := (radialDerivativeJetConstant_pos n).le
  exact le_add_of_nonneg_right (mul_nonneg hc (div_nonneg hB.le hα.le))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radialReadout_iteratedFDeriv_bound (n : ℕ) (a : E) {B α : ℝ}
    (hB : 0 < B) (hα : 0 < α) (x : E) :
    ‖iteratedFDeriv ℝ n (radialReadout a B α) x‖ ≤
      (‖a‖ / α) * radialDerivativeConstant n * B ^ (1 - (n : ℤ)) := by
  have heq : radialReadout a B α = (Cascade.forcingReadoutLinear a α) ∘ (radialSquash B : E → E) := by
    funext y
    simp only [Function.comp_apply, Cascade.forcingReadoutLinear_apply, radialReadout, Cascade.forcingReadout]
  rw [heq]
  apply (Cascade.Calculus.norm_iteratedFDeriv_linear_comp_le _ n (radialSquash_contDiff B n) x).trans
  rw [Cascade.forcingReadoutLinear_norm a hα]
  exact (mul_le_mul_of_nonneg_left (radialSquash_derivative_bound n hB x) (by positivity)).trans_eq
    (mul_assoc _ _ _).symm

theorem radialReadout_power_derivative_bound (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (a : E) (ha : ‖a‖ ≤ 1) {B α : ℝ} (hB : 0 < B) (hα : 0 < α) (x : E) :
    ‖iteratedFDeriv ℝ i (radialReadout a B α) x‖ ≤ (readoutPowerConstant n B α / B) ^ i := by
  have hR := readoutPowerConstant_ge_one n hB hα
  have hcoef : radialDerivativeConstant i * (B / α) ≤ readoutPowerConstant n B α := by
    apply (mul_le_mul_of_nonneg_right (radialDerivative_le_jet n i hin) (by positivity)).trans
    exact le_add_of_nonneg_left (by norm_num)
  calc
    _ ≤ (‖a‖ / α) * radialDerivativeConstant i * B ^ (1 - (i : ℤ)) :=
      radialReadout_iteratedFDeriv_bound i a hB hα x
    _ ≤ (1 / α) * radialDerivativeConstant i * B ^ (1 - (i : ℤ)) := by
      gcongr
      exact (radialDerivativeConstant_pos i).le
    _ = (radialDerivativeConstant i * (B / α)) / B ^ i := by
      rw [zpow_sub₀ hB.ne', zpow_one, zpow_natCast]
      ring
    _ ≤ readoutPowerConstant n B α / B ^ i :=
      div_le_div_of_nonneg_right hcoef (by positivity)
    _ ≤ (readoutPowerConstant n B α) ^ i / B ^ i := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [pow_one] using pow_le_pow_right₀ hR hi
    _ = (readoutPowerConstant n B α / B) ^ i := (div_pow _ _ _).symm

/-- A global derivative bound for the actual radial gate, including points
outside the compression ball. No coordinate basis enters its constants. -/
theorem radialGate_iteratedFDeriv_bound (n : ℕ) (a : E) (ha : ‖a‖ ≤ 1)
    {B α : ℝ} (hB : 0 < B) (hα : 0 < α) (x : E) :
    ‖iteratedFDeriv ℝ n (radialGate a B α) x‖ ≤
      n.factorial * gateJetConstant n * (readoutPowerConstant n B α / B) ^ n := by
  exact norm_iteratedFDeriv_comp_le (gate_contDiff n) (radialReadout_contDiff a B α n)
    le_rfl x (fun i hi => gateJetConstant_spec n i hi _)
    (fun i hi hin => radialReadout_power_derivative_bound n i hi hin a ha hB hα x)

end RandomizedFO2003.Primitives
