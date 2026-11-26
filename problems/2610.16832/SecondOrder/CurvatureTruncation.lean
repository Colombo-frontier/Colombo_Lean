import SecondOrder.CompletionZeroJet
import SecondOrder.SelectorJetEquality
import SecondOrder.CurvatureRichReply

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

def curvatureGatedChain (Θ : Fin (T+1) → BalancedVector m)
    (p : Fin (T+1) → Point (2*m) → ℝ) (x : CurvatureSpace m T) : ℝ :=
  periodicBlockPotential (Θ 0) (x 0)+
    ∑ i : Fin T, 2*(p i.castSucc (x i.castSucc)*periodicBlockPotential (Θ i.succ) (x i.succ))

theorem curvatureGatedChain_contDiff (Θ : Fin (T+1) → BalancedVector m)
    (p : Fin (T+1) → Point (2*m) → ℝ) {r : WithTop ℕ∞}
    (hp : ∀ i, ContDiff ℝ r (p i)) : ContDiff ℝ r (curvatureGatedChain Θ p) := by
  apply ContDiff.add
  · exact (periodicBlockPotential_contDiff (Θ 0) r).comp
      (blockProj (E := Point (2*m)) (0 : Fin (T+1))).contDiff
  · apply ContDiff.sum
    intro i _
    exact contDiff_const.mul (((hp i.castSucc).comp
      (blockProj (E := Point (2*m)) i.castSucc).contDiff).mul
      ((periodicBlockPotential_contDiff (Θ i.succ) r).comp
      (blockProj (E := Point (2*m)) i.succ).contDiff))

theorem curvatureGatedChain_jetEq (Θ : Fin (T+1) → BalancedVector m)
    {p q : Fin (T+1) → Point (2*m) → ℝ} (x : CurvatureSpace m T)
    (hp : ∀ i, ScalarJetEq (p i) (q i) (x i)) :
    ScalarJetEq (curvatureGatedChain Θ p) (curvatureGatedChain Θ q) x := by
  apply ScalarJetEq.add
  · exact ScalarJetEq.refl ((periodicBlockPotential_contDiff (Θ 0) 2).comp
      (blockProj (E := Point (2*m)) (0 : Fin (T+1))).contDiff) x
  · apply ScalarJetEq.sum
    intro i _
    exact (((hp i.castSucc).comp_linear (blockProj (E := Point (2*m)) i.castSucc)).mul
      (ScalarJetEq.refl ((periodicBlockPotential_contDiff (Θ i.succ) 2).comp
        (blockProj (E := Point (2*m)) i.succ).contDiff) x)).const_mul 2

/-- A globally defined scalar loss in which every gate at or beyond the
frontier is identically zero. The fresh block is numbered k. -/
def curvatureTruncatedLoss (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (k : ℕ) : CurvatureSpace m T → ℝ :=
  fun x => curvatureGatedChain Θ (prefixGates (fun i => periodicCompletion (Θ i)) k) x+
    reverseBlockSelector (prefixGates (fun i => periodicCompletion (Θ i)) k)
      (curvatureNoisePayload Θ z) x

theorem curvatureTruncatedLoss_contDiff (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (k : ℕ) : ContDiff ℝ 3 (curvatureTruncatedLoss Θ z k) := by
  have hp := prefixGates_contDiff (fun i => periodicCompletion (Θ i)) k
    (fun i => periodicCompletion_contDiff (Θ i))
  exact (curvatureGatedChain_contDiff Θ _ hp).add
    (reverseBlockSelector_contDiff _ _ hp (fun j _ => curvatureNoisePayload_contDiff Θ z j 3))

/-- Full scalar, gradient, and Hessian truncation at the current point, with
the actual reverse-product noise and terminal gate included. -/
theorem curvatureRandomLoss_truncate_jet (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (k : ℕ) (x : CurvatureSpace m T)
    (hfuture : ∀ i, k ≤ i.val → periodicCompletion (Θ i) (x i)=0) :
    ScalarJetEq (curvatureRandomLoss Θ z) (curvatureTruncatedLoss Θ z k) x := by
  have hp : ∀ i, ScalarJetEq (periodicCompletion (Θ i))
      (prefixGates (fun j => periodicCompletion (Θ j)) k i) (x i) :=
    prefixGates_jetEq _ k (fun i => (periodicCompletion_contDiff (Θ i)).of_le
      (show (2:WithTop ℕ∞) ≤ 3 by decide)) x
      (fun i hi => periodicCompletion_zeroJet (Θ i) (x i) (hfuture i hi))
  exact (curvatureGatedChain_jetEq Θ x hp).add
    (reverseBlockSelector_jetEq hp (fun j _ => ScalarJetEq.refl
      (curvatureNoisePayload_contDiff Θ z j 2) x))

def curvatureTruncatedReply (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (k : ℕ) (x : CurvatureSpace m T) : CurvatureRichResponse m T :=
  (curvatureTruncatedLoss Θ z k x, gradient (curvatureTruncatedLoss Θ z k) x,
    fderiv ℝ (gradient (curvatureTruncatedLoss Θ z k)) x)

theorem curvatureRichReply_truncate (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (k : ℕ) (x : CurvatureSpace m T)
    (hfuture : ∀ i, k ≤ i.val → periodicCompletion (Θ i) (x i)=0) :
    curvatureRichReply Θ z x = curvatureTruncatedReply Θ z k x := by
  have h := curvatureRandomLoss_truncate_jet Θ z k x hfuture
  exact Prod.ext h.value (Prod.ext h.gradient_eq h.hessian_eq)

end
end SecondOrder
