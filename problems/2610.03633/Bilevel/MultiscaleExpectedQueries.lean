import Bilevel.MultiscaleRisk

/-!
# Expected-query reduction for the multiscale experiment

This is the truncation step of `lb:thm:multiscale-lower`. A capped execution
agrees with the stopped execution whenever its cost is at most the cap.
The good-event margin for the capped execution remains an explicit premise:
this module does not supply the missing concrete SFO/genie coupling.
-/

noncomputable section
open MeasureTheory
namespace Bilevel.MultiscaleRisk

/-- The fixed-horizon good event yields an accuracy/cost tradeoff for a
stopped execution. No global bound on the loss after truncation is needed. -/
theorem stopped_risk_cost_tradeoff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad activation : Set Ω) (hb : MeasurableSet bad) (ha : MeasurableSet activation)
    (hbad : μ.real bad ≤ 1/8) (hactivation : μ.real activation ≤ 1/16)
    (loss cost : Ω → ℝ) (hloss : Integrable loss μ) (hcost : Integrable cost μ)
    (hpos : ∀ ω, 0 ≤ loss ω) (hcostpos : ∀ ω, 0 ≤ cost ω)
    (ε cap : ℝ) (hε : 0 < ε) (hcap : 0 < cap)
    (hmargin : ∀ᵐ ω ∂μ, ω ∉ bad → ω ∉ activation → cost ω ≤ cap →
      8*ε ≤ loss ω) :
    13*ε/2 ≤ (∫ ω, loss ω ∂μ) + (8*ε/cap) * ∫ ω, cost ω ∂μ := by
  have hcoeff : 0 ≤ 8*ε/cap := by positivity
  have haug : ∀ᵐ ω ∂μ, ω ∉ bad → ω ∉ activation →
      8*ε ≤ loss ω + (8*ε/cap)*cost ω := by
    filter_upwards [hmargin] with ω hω
    intro hnb hna
    by_cases hc : cost ω ≤ cap
    · exact (hω hnb hna hc).trans
        (le_add_of_nonneg_right (mul_nonneg hcoeff (hcostpos ω)))
    · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hc) hcoeff
      have heq : (8*ε/cap)*cap = 8*ε := by field_simp
      rw [heq] at hh
      linarith [hpos ω]
  have h := risk_from_good_event μ bad activation hb ha hbad hactivation
    (fun ω => loss ω + (8*ε/cap)*cost ω)
    (hloss.add (hcost.const_mul _))
    (fun ω => add_nonneg (hpos ω) (mul_nonneg hcoeff (hcostpos ω)))
    ε hε haug
  rw [integral_add hloss (hcost.const_mul _), integral_const_mul] at h
  exact h

/-- An expected-accuracy guarantee forces expected cost proportional to the
cap. The numerical constant follows from the source's `13/16` good probability
and `8 ε` end-game margin. -/
theorem expected_queries_from_capped_margin
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad activation : Set Ω) (hb : MeasurableSet bad) (ha : MeasurableSet activation)
    (hbad : μ.real bad ≤ 1/8) (hactivation : μ.real activation ≤ 1/16)
    (loss cost : Ω → ℝ) (hloss : Integrable loss μ) (hcost : Integrable cost μ)
    (hpos : ∀ ω, 0 ≤ loss ω) (hcostpos : ∀ ω, 0 ≤ cost ω)
    (ε cap : ℝ) (hε : 0 < ε) (hcap : 0 < cap)
    (hmargin : ∀ᵐ ω ∂μ, ω ∉ bad → ω ∉ activation → cost ω ≤ cap →
      8*ε ≤ loss ω)
    (haccuracy : (∫ ω, loss ω ∂μ) ≤ ε) :
    11*cap/16 ≤ ∫ ω, cost ω ∂μ := by
  have h := stopped_risk_cost_tradeoff μ bad activation hb ha hbad hactivation
    loss cost hloss hcost hpos hcostpos ε cap hε hcap hmargin
  have hmul := mul_le_mul_of_nonneg_right h hcap.le
  have hcancel : (8*ε/cap) * (∫ ω, cost ω ∂μ) * cap =
      8*ε*(∫ ω, cost ω ∂μ) := by field_simp
  rw [add_mul, hcancel] at hmul
  have hacc := mul_le_mul_of_nonneg_right haccuracy hcap.le
  nlinarith

/-- Explicit capped/stopped output agreement supplies the margin premise.
The cost may be an unbounded integrable query count. -/
theorem expected_queries_of_coupled_cap
    {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad activation : Set Ω) (hb : MeasurableSet bad) (ha : MeasurableSet activation)
    (hbad : μ.real bad ≤ 1/8) (hactivation : μ.real activation ≤ 1/16)
    (loss : X → ℝ) (stopped capped : Ω → X) (cost : Ω → ℝ)
    (hloss : Integrable (fun ω => loss (stopped ω)) μ) (hcost : Integrable cost μ)
    (hpos : ∀ x, 0 ≤ loss x) (hcostpos : ∀ ω, 0 ≤ cost ω)
    (ε cap : ℝ) (hε : 0 < ε) (hcap : 0 < cap)
    (hagreement : ∀ᵐ ω ∂μ, cost ω ≤ cap → stopped ω = capped ω)
    (hmargin : ∀ᵐ ω ∂μ, ω ∉ bad → ω ∉ activation → 8*ε ≤ loss (capped ω))
    (haccuracy : (∫ ω, loss (stopped ω) ∂μ) ≤ ε) :
    11*cap/16 ≤ ∫ ω, cost ω ∂μ := by
  apply expected_queries_from_capped_margin μ bad activation hb ha hbad hactivation
    (fun ω => loss (stopped ω)) cost hloss hcost (fun ω => hpos _) hcostpos
    ε cap hε hcap _ haccuracy
  filter_upwards [hagreement, hmargin] with ω he hm
  intro hnb hna hc
  rw [he hc]
  exact hm hnb hna

end Bilevel.MultiscaleRisk
