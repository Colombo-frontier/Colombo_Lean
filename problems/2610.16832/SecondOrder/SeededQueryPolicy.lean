import SecondOrder.FiniteSeedAveraging
import SecondOrder.FiniteBudgetCoupling

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {Ξ X Y S Z : Type*} [MeasurableSpace Ξ] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace S]

/-- Joint measurability of an algorithm's initialization, query and update
maps as functions of its private seed and its current state. -/
structure MeasurableQueryPolicyFamily (P : Ξ → QueryPolicy X Y S) : Prop where
  initial : Measurable (fun ξ => (P ξ).initial)
  query : ∀ n, Measurable (fun w : Ξ × S => (P w.1).query n w.2)
  update : ∀ n, Measurable (fun w : Ξ × (S × Y) => (P w.1).update n w.2.1 w.2.2)

theorem queryPolicyRun_measurable_seed (P : Ξ → QueryPolicy X Y S) (hP : MeasurableQueryPolicyFamily P)
    (reply : X → Z → Y) (hreply : ∀ z, Measurable (fun x => reply x z)) (z : ℕ → Z) :
    ∀ n, Measurable (fun ξ => queryPolicyRun (P ξ) reply z n) := by
  intro n
  induction n with
  | zero => exact hP.initial
  | succ n ih =>
    have hq := (hP.query n).comp (measurable_id.prodMk ih)
    have hr := (hreply (z n)).comp hq
    exact (hP.update n).comp (measurable_id.prodMk (ih.prodMk hr))

theorem queryPolicyOutput_measurable_seed (P : Ξ → QueryPolicy X Y S) (hP : MeasurableQueryPolicyFamily P)
    (reply : X → Z → Y) (hreply : ∀ z, Measurable (fun x => reply x z)) (z : ℕ → Z) (n : ℕ) :
    Measurable (fun ξ => (P ξ).query n (queryPolicyRun (P ξ) reply z n)) :=
  (hP.query n).comp (measurable_id.prodMk (queryPolicyRun_measurable_seed P hP reply hreply z n))

variable {m T : ℕ}

theorem scaledCurvatureRichReply_measurable_fixed (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ)
    {R : ℝ} (z : CurvatureCoefficients m T R) :
    Measurable (fun x => richReply (scaledCurvatureSample Θ A β) z x) := by
  have hf : ContDiff ℝ 2 (scaledCurvatureSample Θ A β z) :=
    (scaledCurvatureSample_contDiff Θ A β z).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  exact (hf.continuous.prodMk ((contDiff_gradient_one hf).continuous.prodMk
    (continuous_hessian hf))).measurable

theorem curvatureOriginalOutput_measurable_seed (P : Ξ → CurvaturePolicy m T S)
    (hP : MeasurableQueryPolicyFamily P) (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ)
    {R : ℝ} (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (h : FiniteHistory Unit (CurvatureCoefficients m T R) N) :
    Measurable (fun ξ => curvatureOriginalOutput (P ξ) Θ A β a₀ N h) := by
  unfold curvatureOriginalOutput
  exact queryPolicyOutput_measurable_seed P hP
    (fun x z => richReply (scaledCurvatureSample Θ A β) z x)
    (scaledCurvatureRichReply_measurable_fixed Θ A β) (finiteHistoryTape a₀ N h) N

theorem curvatureOriginal_sosp_measurable_seed (P : Ξ → CurvaturePolicy m T S)
    (hP : MeasurableQueryPolicyFamily P) (Θ : Fin (T+1) → BalancedVector m) (A β ε γ : ℝ)
    {R : ℝ} (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (h : FiniteHistory Unit (CurvatureCoefficients m T R) N) :
    MeasurableSet {ξ | IsSOSP (scaledCurvaturePopulation Θ A β) ε γ
      (curvatureOriginalOutput (P ξ) Θ A β a₀ N h)} :=
  (isSOSP_measurableSet ((scaledCurvaturePopulation_contDiff Θ A β).of_le
    (show (2:WithTop ℕ∞)≤3 by decide)) ε γ).preimage
      (curvatureOriginalOutput_measurable_seed P hP Θ A β a₀ N h)

end
end SecondOrder
