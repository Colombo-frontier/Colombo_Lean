import HeavyTail.AcceptedMoments

/-! A conditional accepted-law exponential estimate implies the corresponding
raw-step estimate when rejection performs no update. This is the bridge used
by direct analysis of the capped raw execution. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal
namespace HeavyTail
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def rawAcceptanceFactor (S : Set Ω) (F : Ω → ℝ) (ω : Ω) : ℝ :=
  if ω ∈ S then F ω else 1

theorem rawAcceptanceFactor_integral {S : Set Ω} (hS : MeasurableSet S)
    (hpos : P S ≠ 0) {F : Ω → ℝ} (hi : IntegrableOn F S P) :
    (∫ ω, rawAcceptanceFactor S F ω ∂P) =
      P.real S * (∫ ω, F ω ∂ProbabilityTheory.cond P S) + P.real Sᶜ := by
  have hp : P.real S ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos, measure_ne_top P S⟩
  have he : rawAcceptanceFactor S F = S.piecewise F (fun _ => (1 : ℝ)) := rfl
  rw [he, integral_piecewise hS hi (integrable_const (1 : ℝ)).integrableOn,
    integral_const, integral_cond_eq_div]
  simp only [smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
  field_simp

theorem rawAcceptanceFactor_integrable {S : Set Ω} (hS : MeasurableSet S)
    {F : Ω → ℝ} (hi : IntegrableOn F S P) : Integrable (rawAcceptanceFactor S F) P := by
  exact Integrable.piecewise hS hi (integrable_const (1 : ℝ)).integrableOn

theorem rawAcceptanceFactor_bound {S : Set Ω} (hS : MeasurableSet S)
    (hpos : P S ≠ 0) {F : Ω → ℝ} {C : ℝ} (hi : IntegrableOn F S P)
    (hC : 1 ≤ C) (hcond : (∫ ω, F ω ∂ProbabilityTheory.cond P S) ≤ C) :
    (∫ ω, rawAcceptanceFactor S F ω ∂P) ≤ C := by
  rw [rawAcceptanceFactor_integral hS hpos hi]
  have hm : P.real S + P.real Sᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := P) hS
  have hp := mul_le_mul_of_nonneg_left hcond (measureReal_nonneg : 0 ≤ P.real S)
  have hq := mul_le_mul_of_nonneg_left hC (measureReal_nonneg : 0 ≤ P.real Sᶜ)
  have hmC : P.real S * C + P.real Sᶜ * C = C := by rw [← add_mul, hm, one_mul]
  linarith only [hp, hq, hmC]

theorem stopped_rawAcceptanceFactor_bound {S : Set Ω} (hS : MeasurableSet S)
    (hpos : P S ≠ 0) {F : Ω → ℝ} {C : ℝ} (hi : IntegrableOn F S P)
    (hC : 1 ≤ C) (hcond : (∫ ω, F ω ∂ProbabilityTheory.cond P S) ≤ C)
    (active : Prop) [Decidable active] :
    (∫ ω, (if active then rawAcceptanceFactor S F ω else 1) ∂P) ≤ C := by
  by_cases ha : active
  · simp only [if_pos ha]
    exact rawAcceptanceFactor_bound hS hpos hi hC hcond
  · simpa only [if_neg ha, integral_const, measureReal_univ_eq_one, one_smul] using hC

end HeavyTail
