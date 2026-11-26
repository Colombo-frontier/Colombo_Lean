import SecondOrder.PrefixFrontier
import SecondOrder.FirstOrderScales
import SecondOrder.FirstOrderAdaptiveInformation
import SecondOrder.SequentialStageCounting

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def firstOrderLimitedProgress (Θ : Fin (T+1) → (Fin d → Bool)) (β : ℝ)
    (x : Point (FirstOrderDimension d T)) (r : ℕ) : ℕ :=
  prefixPositiveFrontier (fun i => firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β x i)) r

theorem firstOrderLimitedProgress_le (Θ : Fin (T+1) → (Fin d → Bool)) (β : ℝ)
    (x : Point (FirstOrderDimension d T)) (r : ℕ) :
    firstOrderLimitedProgress Θ β x r≤T+1 ∧ firstOrderLimitedProgress Θ β x r≤r :=
  ⟨prefixPositiveFrontier_le_size _ _, prefixPositiveFrontier_le_cut _ _⟩

theorem firstOrderLimitedProgress_prefix (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (β : ℝ)
    (x : Point (FirstOrderDimension d T)) (r : ℕ) (hΘ : ∀ i, i.val<r → Θ i=Θ' i) :
    firstOrderLimitedProgress Θ β x r=firstOrderLimitedProgress Θ' β x r :=
  prefixPositiveFrontier_congr _ _ r (fun i hi => by rw [hΘ i hi])

theorem firstOrderLimitedProgress_no_far (Θ : Fin (T+1) → (Fin d → Bool)) (β : ℝ)
    (x : Point (FirstOrderDimension d T)) (r : ℕ)
    (hfar : ∀ i, r ≤ i.val → ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β x i)) :
    firstOrderLimitedProgress Θ β x r=firstOrderProgress Θ (firstOrderDilation d T β x) :=
  prefixPositiveFrontier_no_far _ r hfar

theorem firstOrderLimitedProgress_reply (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ)
    {R : ℝ} (z : FirstOrderCoefficients d T R) (x : Point (FirstOrderDimension d T)) (r : ℕ)
    (hfar : ∀ i, r ≤ i.val → ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β x i)) :
    richReply (scaledFirstOrderSample Θ A β) z x =
      scaledFirstOrderTruncatedReply Θ A β z (firstOrderLimitedProgress Θ β x r) x := by
  rw [firstOrderLimitedProgress_no_far Θ β x r hfar]
  exact scaledFirstOrderReply_at_progress Θ A β z x

/-- Prefix dependence also covers the terminal index, where every hidden
block has already been revealed. -/
theorem scaledFirstOrderTruncatedReply_hidden_prefix (Θ Θ' : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : FirstOrderCoefficients d T R) (k : ℕ)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) (x : Point (FirstOrderDimension d T)) :
    scaledFirstOrderTruncatedReply Θ A β z k x=scaledFirstOrderTruncatedReply Θ' A β z k x := by
  by_cases hk : k≤T
  · exact scaledFirstOrderTruncatedReply_prefix_invariant Θ Θ' A β z z hk hΘ (fun _ _ => rfl) x
  · have he : Θ=Θ' := funext (fun i => hΘ i (by omega))
    rw [he]

end
end SecondOrder

