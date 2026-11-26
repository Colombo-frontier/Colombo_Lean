import SecondOrder.ScaledCurvatureCompletion

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T k : ℕ}

def scaledCurvatureTruncatedLoss (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ)
    {R : ℝ} (z : CurvatureCoefficients m T R) (k : ℕ) : Point (CurvatureDimension m T) → ℝ :=
  scalarLinearScaling (curvatureTruncatedLoss Θ z k) A (curvatureDilation m T β)

def scaledCurvatureTruncatedReply (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ)
    {R : ℝ} (z : CurvatureCoefficients m T R) (k : ℕ)
    (x : Point (CurvatureDimension m T)) : RichReply (CurvatureDimension m T) :=
  richReply (fun z => scaledCurvatureTruncatedLoss Θ A β z k) z x

theorem scaledCurvatureTruncatedLoss_contDiff (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ)
    {R : ℝ} (z : CurvatureCoefficients m T R) (k : ℕ) :
    ContDiff ℝ 3 (scaledCurvatureTruncatedLoss Θ A β z k) :=
  scalarLinearScaling_contDiff (curvatureTruncatedLoss_contDiff Θ z k) A _

theorem scaledCurvatureReply_truncate (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ)
    {R : ℝ} (z : CurvatureCoefficients m T R) (k : ℕ) (x : Point (CurvatureDimension m T))
    (hfuture : ∀ i, k ≤ i.val → periodicCompletion (Θ i) ((curvatureDilation m T β x) i)=0) :
    richReply (scaledCurvatureSample Θ A β) z x = scaledCurvatureTruncatedReply Θ A β z k x := by
  have h₀ := curvatureRandomLoss_truncate_jet Θ z k (curvatureDilation m T β x) hfuture
  have h := (h₀.comp_linear (curvatureDilation m T β)).const_mul A
  exact Prod.ext h.value (Prod.ext h.gradient_eq h.hessian_eq)

theorem scaledCurvatureTruncatedReply_prefix_invariant
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z z' : CurvatureCoefficients m T R) (hk : k≤T)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) (hz : ∀ i, i.val≤k → z i=z' i)
    (x : Point (CurvatureDimension m T)) :
    scaledCurvatureTruncatedReply Θ A β z k x = scaledCurvatureTruncatedReply Θ' A β z' k x := by
  have he : scaledCurvatureTruncatedLoss Θ A β z k = scaledCurvatureTruncatedLoss Θ' A β z' k := by
    unfold scaledCurvatureTruncatedLoss
    rw [curvatureTruncatedLoss_prefix_invariant Θ Θ' z z' hk hΘ hz]
  unfold scaledCurvatureTruncatedReply richReply
  dsimp only
  rw [he]

def scaledCurvatureFrontierReply (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (A β : ℝ) {R : ℝ} (x : Point (CurvatureDimension m T))
    (a : CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R)) :
    RichReply (CurvatureDimension m T) :=
  scaledCurvatureTruncatedReply (extendHiddenPrefix θ₀ pastΘ) A β
    (extendCoefficientPrefix a.1 a.2) k x

theorem scaledCurvatureFrontierReply_base_independent (θ₀ θ₁ : BalancedVector m)
    (pastΘ : Fin k → BalancedVector m) (A β : ℝ) {R : ℝ} (hk : k≤T)
    (x : Point (CurvatureDimension m T))
    (a : CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R)) :
    scaledCurvatureFrontierReply θ₀ pastΘ A β x a = scaledCurvatureFrontierReply θ₁ pastΘ A β x a := by
  apply scaledCurvatureTruncatedReply_prefix_invariant _ _ _ _ _ _ hk
  · intro i hi
    simp only [extendHiddenPrefix, dif_pos hi]
  · intro _ _
    rfl

theorem scaledCurvatureTruncatedReply_frontier_map (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β : ℝ) {R : ℝ} (z : CurvatureCoefficients m T R)
    (hk : k≤T) (x : Point (CurvatureDimension m T)) :
    scaledCurvatureTruncatedReply Θ A β z k x =
      scaledCurvatureFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β x
        ((fun i : Fin k => z ⟨i.val,by omega⟩), z ⟨k,by omega⟩) := by
  apply scaledCurvatureTruncatedReply_prefix_invariant _ _ _ _ _ _ hk
  · intro i hi
    simp only [extendHiddenPrefix, dif_pos hi]
  · intro i hi
    unfold extendCoefficientPrefix
    split_ifs with hik
    · rfl
    · have he : i = (⟨k,by omega⟩ : Fin (T+1)) := by
        apply Fin.ext
        change i.val=k
        omega
      rw [he]

theorem scaledCurvatureReply_at_progress (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ)
    {R : ℝ} (z : CurvatureCoefficients m T R) (x : Point (CurvatureDimension m T)) :
    richReply (scaledCurvatureSample Θ A β) z x =
      scaledCurvatureTruncatedReply Θ A β z (curvatureProgress Θ (curvatureDilation m T β x)) x :=
  scaledCurvatureReply_truncate Θ A β z _ x (curvatureProgress_future_zero Θ _)

theorem scaledCurvatureTruncatedReply_continuous (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : CurvatureCoefficients m T R) (k : ℕ) :
    Continuous (scaledCurvatureTruncatedReply Θ A β z k) := by
  have hf := scaledCurvatureTruncatedLoss_contDiff Θ A β z k
  have hg : ContDiff ℝ 1 (gradient (scaledCurvatureTruncatedLoss Θ A β z k)) :=
    (InnerProductSpace.toDual ℝ (Point (CurvatureDimension m T))).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 3 by decide))
  exact hf.continuous.prodMk (hg.continuous.prodMk (hg.continuous_fderiv (by norm_num)))

theorem scaledCurvatureTruncatedReply_measurable (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (k : ℕ) : Measurable
      (fun w : Point (CurvatureDimension m T) × CurvatureCoefficients m T R =>
        scaledCurvatureTruncatedReply Θ A β w.2 k w.1) :=
  measurable_from_prod_countable (fun z => (scaledCurvatureTruncatedReply_continuous Θ A β z k).measurable)

theorem scaledCurvatureFrontierReply_measurable (θ₀ : BalancedVector m)
    (pastΘ : Fin k → BalancedVector m) (A β R : ℝ) : Measurable
      (fun w : Point (CurvatureDimension m T) ×
        (CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R)) =>
        scaledCurvatureFrontierReply θ₀ pastΘ A β w.1 w.2) :=
  measurable_from_prod_countable (fun a =>
    (scaledCurvatureTruncatedReply_continuous (extendHiddenPrefix (T := T) θ₀ pastΘ) A β
      (extendCoefficientPrefix a.1 a.2) k).measurable)

end
end SecondOrder
