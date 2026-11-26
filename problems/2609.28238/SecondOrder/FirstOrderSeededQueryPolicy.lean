import SecondOrder.SeededQueryPolicy
import SecondOrder.FirstOrderSequentialLowerBound
import SecondOrder.FiniteSeedAveraging
import SecondOrder.FiniteBudgetCoupling

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

variable {d T : ℕ}

theorem scaledFirstOrderRichReply_measurable_fixed (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ)
    {R : ℝ} (z : FirstOrderCoefficients d T R) :
    Measurable (fun x => richReply (scaledFirstOrderSample Θ A β) z x) := by
  have hf : ContDiff ℝ 2 (scaledFirstOrderSample Θ A β z) :=
    (scaledFirstOrderSample_contDiff Θ A β z).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  exact (hf.continuous.prodMk ((contDiff_gradient_one hf).continuous.prodMk
    (continuous_hessian hf))).measurable

theorem firstOrderOriginalOutput_measurable_seed (P : Ξ → FirstOrderPolicy d T S)
    (hP : MeasurableQueryPolicyFamily P) (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ)
    {R : ℝ} (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) N) :
    Measurable (fun ξ => firstOrderOriginalOutput (P ξ) Θ A β a₀ N h) := by
  unfold firstOrderOriginalOutput
  exact queryPolicyOutput_measurable_seed P hP
    (fun x z => richReply (scaledFirstOrderSample Θ A β) z x)
    (scaledFirstOrderRichReply_measurable_fixed Θ A β) (finiteHistoryTape a₀ N h) N

theorem firstOrderOriginal_sosp_measurable_seed (P : Ξ → FirstOrderPolicy d T S)
    (hP : MeasurableQueryPolicyFamily P) (Θ : Fin (T+1) → (Fin d → Bool)) (A β ε γ : ℝ)
    {R : ℝ} (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) N) :
    MeasurableSet {ξ | IsSOSP (scaledFirstOrderPopulation Θ A β) ε γ
      (firstOrderOriginalOutput (P ξ) Θ A β a₀ N h)} :=
  (isSOSP_measurableSet ((scaledFirstOrderPopulation_contDiff Θ A β).of_le
    (show (2:WithTop ℕ∞)≤3 by decide)) ε γ).preimage
      (firstOrderOriginalOutput_measurable_seed P hP Θ A β a₀ N h)

end
end SecondOrder
