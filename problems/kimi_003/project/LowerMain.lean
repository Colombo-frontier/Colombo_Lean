import HardFamilyBayesLower
import UpperMain

open MeasureTheory

namespace Task006.Full

open Task006.HaarRebalancing Task006.HardFamilyBayes Task006.Full.HardFamily
open Task006.AdaptiveSphereTranscript

universe u
noncomputable section

theorem uniform_reply_lower {d N : ℕ} {L R eps : ℝ} (h : Regime d L R eps)
    {S : Type u} [MeasurableSpace S] (σ : Measure S) [IsProbabilityMeasure σ]
    (alg : OracleAlgorithm d N S) (huniform : UniformlySolves.{u,0} L R eps σ alg) :
    (d : ℝ)*(L*R/eps)^3/131072 < (N : ℝ) := by
  rcases h with ⟨hd,hL,hR,heps,hreg⟩
  let A := L*R/eps
  have hA16 : 16 ≤ A := by
    have hb : (2^17 : ℝ) ≤ A := (le_max_right _ _).trans hreg
    norm_num at hb
    linarith
  have hA0 : 0 < A := by linarith
  have hscale : (16*L/A)*R = 16*eps := by
    dsimp only [A]
    field_simp [hL.ne',hR.ne',heps.ne']
  let j : Fin d := ⟨0,by omega⟩
  have hsolve (θ : Space d) (hθ : ‖θ‖ = 1) :
      alg.SolvesInstance eps σ (instanceOfDirection L R A hL.le hA16 θ hθ) :=
    huniform ℝ inferInstance (law L A hA16) inferInstance
      (instanceOfDirection L R A hL.le hA16 θ hθ)
  have hlegal : LegalOriginal alg R := fun θ hθ seed tape => (hsolve θ hθ).1 seed tape
  have hbayes := fixed_instance_to_bayes_bound alg j L R A eps hL hR.le hA16 σ hsolve
  by_contra hn
  have hN : (N : ℝ) ≤ (d : ℝ)*A^3/131072 := le_of_not_gt hn
  have hbudget : (4096/A^3)*(N : ℝ) ≤ (d : ℝ)/32 :=
    (Task006LowerAudit.budget_threshold_equivalence A d N hA0).2 hN
  by_cases hd8 : 8 ≤ d
  · have hgt := large_dimension_bayes_risk_gt alg j L R A eps hL hR.le hA16 heps
      hscale hd8 hlegal σ hbudget
    exact (not_lt_of_ge hbayes) hgt
  · have hgt := small_dimension_bayes_risk_gt alg j L R A eps hL hR.le hA16 heps
      hscale (by omega) (by omega) hlegal σ hbudget
    exact (not_lt_of_ge hbayes) hgt

theorem admissible_reply_lower {d N : ℕ} {L R eps : ℝ} (h : Regime d L R eps)
    (hbudget : AdmitsBudget.{u,0} d N L R eps) :
    (d : ℝ)*(L*R/eps)^3/131072 < (N : ℝ) := by
  rcases hbudget with ⟨S,mS,σ,hσ,alg,huniform⟩
  letI : MeasurableSpace S := mS
  letI : IsProbabilityMeasure σ := hσ
  exact uniform_reply_lower h σ alg huniform

/-- The minimax infimum is taken only after an actual admissible algorithm has
proved the budget set nonempty. The lower bound quantifies over every admitted
measurable policy and every independent seed law. -/
theorem minimax_lower_complexity {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    (d : ℝ)*(L*R/eps)^3/131072 ≤ (minimaxReplies.{0,0} d L R eps : ℝ) := by
  have hmin : AdmitsBudget.{0,0} d (minimaxReplies.{0,0} d L R eps) L R eps :=
    Nat.sInf_mem (upper_budget_nonempty h)
  exact (admissible_reply_lower h hmin).le

#print axioms uniform_reply_lower
#print axioms admissible_reply_lower
#print axioms minimax_lower_complexity

end
end Task006.Full
