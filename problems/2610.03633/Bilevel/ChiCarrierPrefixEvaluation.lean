import Bilevel.ChiPrefixJets
import Bilevel.ChiRecursiveCarrierLocality
import Bilevel.ChiCarrierDeepestLocality

/-! Actual selector, closed carrier, and centered deepest payload prefix
evaluators. Receiver terms and exact residual cancellation remain present. -/
noncomputable section
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive

theorem selector_prefix_value (n r : ℕ) (h : ℝ) (hh : 0<h) (i : Fin (n+1)) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤h/4) :
    selector n i (h⁻¹ • z)=selector n i (h⁻¹ • retain n r z) :=
  value_eq_retain _ (((selector_contDiff n 3 i).comp (contDiff_id.const_smul h⁻¹)).differentiable (by norm_num))
    (fun w hw k hk => normalized_selector_gradient_small n h hh i k w (hw k hk)) z hz

theorem selector_prefix_gradient (n r : ℕ) (h : ℝ) (hh : 0<h) (i : Fin (n+1)) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|<h/4) :
    gradient (fun w => selector n i (h⁻¹ • w)) z=
      gradient (fun w => selector n i (h⁻¹ • w)) (retain n r z) :=
  gradient_eq_retain (by positivity) _ (((selector_contDiff n 3 i).comp (contDiff_id.const_smul h⁻¹)).differentiable (by norm_num))
    (fun w hw k hk => normalized_selector_gradient_small n h hh i k w (hw k hk)) z hz

theorem closedCarrier_prefix_value (n r : ℕ) (ℓ h A ν g hp T : ℝ) (hh : 0<h)
    (q : Fin (n+1) → ℝ) (hq : ∀ i,r ≤ i.val → q i=0) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤h/4) :
    closedCarrier n ℓ h A ν g hp T q z=closedCarrier n ℓ h A ν g hp T q (retain n r z) :=
  value_eq_retain _ ((closedCarrier_contDiff n ℓ h A ν g hp T q).differentiable (by norm_num))
    (fun w hw k hk => closedCarrier_gradient_support n r ℓ h A ν g hp T hh q hq w hw k hk) z hz

theorem closedCarrier_prefix_gradient (n r : ℕ) (ℓ h A ν g hp T : ℝ) (hh : 0<h)
    (q : Fin (n+1) → ℝ) (hq : ∀ i,r ≤ i.val → q i=0) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|<h/4) :
    gradient (closedCarrier n ℓ h A ν g hp T q) z=
      gradient (closedCarrier n ℓ h A ν g hp T q) (retain n r z) :=
  gradient_eq_retain (by positivity) _ ((closedCarrier_contDiff n ℓ h A ν g hp T q).differentiable (by norm_num))
    (fun w hw k hk => closedCarrier_gradient_support n r ℓ h A ν g hp T hh q hq w hw k hk) z hz

theorem centeredPayload_prefix_value (n r : ℕ) (ℓ h A ν g hp T : ℝ) (hh : 0<h)
    (z : Space n) (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤h/4) :
    payload n ℓ h A ν g hp T z-ChiFine.frontier n ℓ h z=
      payload n ℓ h A ν g hp T (retain n r z)-ChiFine.frontier n ℓ h (retain n r z) :=
  value_eq_retain _ (((payload_contDiff n ℓ h A ν g hp T 3).sub (ChiFine.frontier_contDiff n ℓ h)).differentiable (by norm_num))
    (fun w hw k hk => centeredPayload_gradient_support n r ℓ h A ν g hp T hh w hw k hk) z hz

theorem centeredPayload_prefix_gradient (n r : ℕ) (ℓ h A ν g hp T : ℝ) (hh : 0<h)
    (z : Space n) (hz : ∀ k : Fin (n+1),r≤k.val → |z k|<h/4) :
    gradient (fun w => payload n ℓ h A ν g hp T w-ChiFine.frontier n ℓ h w) z=
      gradient (fun w => payload n ℓ h A ν g hp T w-ChiFine.frontier n ℓ h w) (retain n r z) :=
  gradient_eq_retain (by positivity) _ (((payload_contDiff n ℓ h A ν g hp T 3).sub (ChiFine.frontier_contDiff n ℓ h)).differentiable (by norm_num))
    (fun w hw k hk => centeredPayload_gradient_support n r ℓ h A ν g hp T hh w hw k hk) z hz

end Bilevel.ChiPrefixEvaluation
