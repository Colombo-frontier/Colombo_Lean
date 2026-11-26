import SecondOrder.ScaledFirstOrderModel

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T k : ℕ}

def scaledFirstOrderTruncatedLoss (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ)
    {R : ℝ} (z : FirstOrderCoefficients d T R) (k : ℕ) : Point (FirstOrderDimension d T) → ℝ :=
  scalarLinearScaling (firstOrderTruncatedLoss Θ z k) A (firstOrderDilation d T β)

def scaledFirstOrderTruncatedReply (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ)
    {R : ℝ} (z : FirstOrderCoefficients d T R) (k : ℕ)
    (x : Point (FirstOrderDimension d T)) : RichReply (FirstOrderDimension d T) :=
  richReply (fun z => scaledFirstOrderTruncatedLoss Θ A β z k) z x

theorem scaledFirstOrderTruncatedLoss_contDiff (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ)
    {R : ℝ} (z : FirstOrderCoefficients d T R) (k : ℕ) :
    ContDiff ℝ 3 (scaledFirstOrderTruncatedLoss Θ A β z k) :=
  scalarLinearScaling_contDiff (firstOrderTruncatedLoss_contDiff Θ z k) A _

theorem scaledFirstOrderReply_truncate (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ)
    {R : ℝ} (z : FirstOrderCoefficients d T R) (k : ℕ) (x : Point (FirstOrderDimension d T))
    (hfuture : ∀ i, k ≤ i.val → firstOrderBlockCompletion (Θ i) ((firstOrderDilation d T β x) i)=0) :
    richReply (scaledFirstOrderSample Θ A β) z x = scaledFirstOrderTruncatedReply Θ A β z k x := by
  have h₀ := firstOrderRandomLoss_truncate_jet Θ z k (firstOrderDilation d T β x) hfuture
  have h := (h₀.comp_linear (firstOrderDilation d T β)).const_mul A
  exact Prod.ext h.value (Prod.ext h.gradient_eq h.hessian_eq)

theorem scaledFirstOrderTruncatedReply_prefix_invariant
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z z' : FirstOrderCoefficients d T R) (hk : k≤T)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) (hz : ∀ i, i.val≤k → z i=z' i)
    (x : Point (FirstOrderDimension d T)) :
    scaledFirstOrderTruncatedReply Θ A β z k x = scaledFirstOrderTruncatedReply Θ' A β z' k x := by
  have he : scaledFirstOrderTruncatedLoss Θ A β z k = scaledFirstOrderTruncatedLoss Θ' A β z' k := by
    unfold scaledFirstOrderTruncatedLoss
    rw [firstOrderTruncatedLoss_prefix_invariant Θ Θ' z z' hk hΘ hz]
  unfold scaledFirstOrderTruncatedReply richReply
  dsimp only
  rw [he]

def scaledFirstOrderFrontierReply (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (x : Point (FirstOrderDimension d T))
    (a : FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R)) :
    RichReply (FirstOrderDimension d T) :=
  scaledFirstOrderTruncatedReply (firstOrderExtendHiddenPrefix θ₀ pastΘ) A β
    (firstOrderExtendCoefficientPrefix a.1 a.2) k x

theorem scaledFirstOrderFrontierReply_base_independent (θ₀ θ₁ : (Fin d → Bool))
    (pastΘ : Fin k → (Fin d → Bool)) (A β : ℝ) {R : ℝ} (hk : k≤T)
    (x : Point (FirstOrderDimension d T))
    (a : FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R)) :
    scaledFirstOrderFrontierReply θ₀ pastΘ A β x a = scaledFirstOrderFrontierReply θ₁ pastΘ A β x a := by
  apply scaledFirstOrderTruncatedReply_prefix_invariant _ _ _ _ _ _ hk
  · intro i hi
    simp only [firstOrderExtendHiddenPrefix, dif_pos hi]
  · intro _ _
    rfl

theorem scaledFirstOrderTruncatedReply_frontier_map (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β : ℝ) {R : ℝ} (z : FirstOrderCoefficients d T R)
    (hk : k≤T) (x : Point (FirstOrderDimension d T)) :
    scaledFirstOrderTruncatedReply Θ A β z k x =
      scaledFirstOrderFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β x
        ((fun i : Fin k => z ⟨i.val,by omega⟩), z ⟨k,by omega⟩) := by
  apply scaledFirstOrderTruncatedReply_prefix_invariant _ _ _ _ _ _ hk
  · intro i hi
    simp only [firstOrderExtendHiddenPrefix, dif_pos hi]
  · intro i hi
    unfold firstOrderExtendCoefficientPrefix
    split_ifs with hik
    · rfl
    · have he : i = (⟨k,by omega⟩ : Fin (T+1)) := by
        apply Fin.ext
        change i.val=k
        omega
      rw [he]

theorem scaledFirstOrderReply_at_progress (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ)
    {R : ℝ} (z : FirstOrderCoefficients d T R) (x : Point (FirstOrderDimension d T)) :
    richReply (scaledFirstOrderSample Θ A β) z x =
      scaledFirstOrderTruncatedReply Θ A β z (firstOrderProgress Θ (firstOrderDilation d T β x)) x :=
  scaledFirstOrderReply_truncate Θ A β z _ x (firstOrderProgress_future_zero Θ _)

theorem scaledFirstOrderTruncatedReply_continuous (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : FirstOrderCoefficients d T R) (k : ℕ) :
    Continuous (scaledFirstOrderTruncatedReply Θ A β z k) := by
  have hf := scaledFirstOrderTruncatedLoss_contDiff Θ A β z k
  have hg : ContDiff ℝ 1 (gradient (scaledFirstOrderTruncatedLoss Θ A β z k)) :=
    (InnerProductSpace.toDual ℝ (Point (FirstOrderDimension d T))).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 3 by decide))
  exact hf.continuous.prodMk (hg.continuous.prodMk (hg.continuous_fderiv (by norm_num)))

theorem scaledFirstOrderTruncatedReply_measurable (Θ : Fin (T+1) → (Fin d → Bool))
    (A β R : ℝ) (k : ℕ) : Measurable
      (fun w : Point (FirstOrderDimension d T) × FirstOrderCoefficients d T R =>
        scaledFirstOrderTruncatedReply Θ A β w.2 k w.1) :=
  measurable_from_prod_countable (fun z => (scaledFirstOrderTruncatedReply_continuous Θ A β z k).measurable)

theorem scaledFirstOrderFrontierReply_measurable (θ₀ : (Fin d → Bool))
    (pastΘ : Fin k → (Fin d → Bool)) (A β R : ℝ) : Measurable
      (fun w : Point (FirstOrderDimension d T) ×
        (FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R)) =>
        scaledFirstOrderFrontierReply θ₀ pastΘ A β w.1 w.2) :=
  measurable_from_prod_countable (fun a =>
    (scaledFirstOrderTruncatedReply_continuous (firstOrderExtendHiddenPrefix (T := T) θ₀ pastΘ) A β
      (firstOrderExtendCoefficientPrefix a.1 a.2) k).measurable)

end
end SecondOrder

