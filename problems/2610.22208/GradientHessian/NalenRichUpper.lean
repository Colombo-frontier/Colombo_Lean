import GradientHessian.NalenPolicyGuarantees
import GradientHessian.NalenCapParameters

/-! Source upper bound (i) with an actual measurable oracle algorithm,
pathwise rich cap exactly h, and an explicit absolute ordinary-call bound. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Nalen Model
open scoped ENNReal

theorem cap_horizon_ceil_refresh {T : ℝ} {h : ℕ} (hm : 1≤capRefresh T h) :
    capHorizon T h ⌈/⌉ capRefresh T h=h := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  unfold capHorizon
  have he : h*capRefresh T h+capRefresh T h-1=
      (capRefresh T h-1)+h*capRefresh T h := by omega
  rw [he,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt (show capRefresh T h-1<capRefresh T h by omega)]
  omega

def richCapAlgorithm (d : ℕ) (T : ℝ) (h : ℕ) (hq : 1≤capAveraging T h) : Algorithm d :=
  algorithm d (stepRadius_pos hq).le (stepSize (capRefresh T h) (capAveraging T h))
    (capRefresh T h) (capAveraging T h) (capHorizon T h)

theorem richCapAlgorithm_guarantees (d : ℕ) {T : ℝ} {h : ℕ}
    (hT : 1≤T) (hh : 1≤h) (hhT : (h:ℝ)≤T) :
    (richCapAlgorithm d T h (cap_parameters hT hh hhT).1).Guarantees T (3*capHorizon T h+1) h := by
  obtain ⟨hq,hm,hK,hTK,hN,hG⟩ := cap_parameters hT hh hhT
  have hhorizon := algorithm_guarantees (d := d) hm hq hK (by rfl : capRefresh T h≤(capAveraging T h)^3)
    (le_of_eq (cap_block_horizon T h)) hTK
  rw [cap_horizon_ceil_refresh hm] at hhorizon
  exact hhorizon

theorem source_rich_upper (d : ℕ) {T : ℝ} {h : ℕ}
    (hT : 1≤T) (hh : 1≤h) (hhT : (h:ℝ)≤T) :
    ∃ (A : Algorithm d) (G : ℕ), A.Guarantees T G h ∧
      (G:ℝ)≤14740*T^((3:ℝ)/2)/Real.sqrt (h:ℝ) :=
  ⟨richCapAlgorithm d T h (cap_parameters hT hh hhT).1,3*capHorizon T h+1,
    richCapAlgorithm_guarantees d hT hh hhT,cap_source_query_bound hT hh hhT⟩

theorem source_rich_complexity_upper (d : ℕ) {T : ℝ} {h : ℕ}
    (hT : 1≤T) (hh : 1≤h) (hhT : (h:ℝ)≤T) :
    complexity h d T≤ENNReal.ofReal (14740*T^((3:ℝ)/2)/Real.sqrt (h:ℝ)) := by
  obtain ⟨A,G,hA,hG⟩ := source_rich_upper d hT hh hhT
  exact (complexity_le A hA).trans (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hG)

end GradientHessian.NalenPolicy
