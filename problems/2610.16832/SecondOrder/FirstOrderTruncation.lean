import SecondOrder.CompletionZeroJet
import SecondOrder.SelectorJetEquality
import SecondOrder.FirstOrderRichReply

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

theorem firstOrderBlockCompletion_eq_zero_iff (θ : Fin d → Bool) (x : Point d) :
    firstOrderBlockCompletion θ x=0 ↔ firstOrderBlockEncoding θ x≤1/4 := by
  change gate (2*(firstOrderBlockEncoding θ x-1/4))=0 ↔ _
  rw [gate_eq_zero_iff]
  constructor <;> intro h <;> linarith

theorem firstOrderBlockCompletion_zeroJet (θ : Fin d → Bool) (x : Point d)
    (hx : firstOrderBlockCompletion θ x=0) : ScalarJetEq (firstOrderBlockCompletion θ) (fun _ => 0) x := by
  obtain ⟨hv,hg,hH⟩ := firstOrderBlockCompletion_flat θ ((firstOrderBlockCompletion_eq_zero_iff θ x).1 hx)
  exact scalarJetEq_zero_of_flat
    ((firstOrderBlockCompletion_contDiff θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)) x hv hg hH

def firstOrderGatedChain (Θ : Fin (T+1) → Fin d → Bool)
    (p : Fin (T+1) → Point d → ℝ) (x : FirstOrderSpace d T) : ℝ :=
  firstOrderBlockPotential (Θ 0) (x 0)+
    (∑ i : Fin T, 2*(p i.castSucc (x i.castSucc)*firstOrderBlockPotential (Θ i.succ) (x i.succ)))+
    ∑ j : Fin (T+1), firstOrderBlockRegularizer (x j)

theorem firstOrderGatedChain_contDiff (Θ : Fin (T+1) → Fin d → Bool)
    (p : Fin (T+1) → Point d → ℝ) {r : WithTop ℕ∞}
    (hp : ∀ i, ContDiff ℝ r (p i)) : ContDiff ℝ r (firstOrderGatedChain Θ p) := by
  apply ContDiff.add
  · apply ContDiff.add
    · exact (firstOrderBlockPotential_contDiff (Θ 0) r).comp
        (blockProj (E := Point d) (0:Fin (T+1))).contDiff
    · apply ContDiff.sum
      intro i _
      exact contDiff_const.mul (((hp i.castSucc).comp
        (blockProj (E := Point d) i.castSucc).contDiff).mul
        ((firstOrderBlockPotential_contDiff (Θ i.succ) r).comp (blockProj (E := Point d) i.succ).contDiff))
  · apply ContDiff.sum
    intro j _
    exact (firstOrderBlockRegularizer_contDiff r).comp (blockProj (E := Point d) j).contDiff

theorem firstOrderGatedChain_jetEq (Θ : Fin (T+1) → Fin d → Bool)
    {p q : Fin (T+1) → Point d → ℝ} (x : FirstOrderSpace d T)
    (hp : ∀ i, ScalarJetEq (p i) (q i) (x i)) :
    ScalarJetEq (firstOrderGatedChain Θ p) (firstOrderGatedChain Θ q) x := by
  apply ScalarJetEq.add
  · apply ScalarJetEq.add
    · exact ScalarJetEq.refl ((firstOrderBlockPotential_contDiff (Θ 0) 2).comp
        (blockProj (E := Point d) (0:Fin (T+1))).contDiff) x
    · apply ScalarJetEq.sum
      intro i _
      exact (((hp i.castSucc).comp_linear (blockProj (E := Point d) i.castSucc)).mul
        (ScalarJetEq.refl ((firstOrderBlockPotential_contDiff (Θ i.succ) 2).comp
          (blockProj (E := Point d) i.succ).contDiff) x)).const_mul 2
  · apply ScalarJetEq.sum
    intro j _
    exact ScalarJetEq.refl ((firstOrderBlockRegularizer_contDiff 2).comp
      (blockProj (E := Point d) j).contDiff) x

/-- Future gates vanish identically; the public regularizer remains on every block. -/
def firstOrderTruncatedLoss (Θ : Fin (T+1) → Fin d → Bool) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (k : ℕ) : FirstOrderSpace d T → ℝ :=
  fun x => firstOrderGatedChain Θ (prefixGates (fun i => firstOrderBlockCompletion (Θ i)) k) x+
    reverseBlockSelector (prefixGates (fun i => firstOrderBlockCompletion (Θ i)) k) (firstOrderNoisePayload Θ z) x

theorem firstOrderTruncatedLoss_contDiff (Θ : Fin (T+1) → Fin d → Bool) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (k : ℕ) : ContDiff ℝ 3 (firstOrderTruncatedLoss Θ z k) := by
  have hp := prefixGates_contDiff (fun i => firstOrderBlockCompletion (Θ i)) k
    (fun i => firstOrderBlockCompletion_contDiff (Θ i))
  exact (firstOrderGatedChain_contDiff Θ _ hp).add
    (reverseBlockSelector_contDiff _ _ hp (fun j _ => firstOrderNoisePayload_contDiff Θ z j 3))

theorem firstOrderRandomLoss_truncate_jet (Θ : Fin (T+1) → Fin d → Bool) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (k : ℕ) (x : FirstOrderSpace d T)
    (hfuture : ∀ i, k ≤ i.val → firstOrderBlockCompletion (Θ i) (x i)=0) :
    ScalarJetEq (firstOrderRandomLoss Θ z) (firstOrderTruncatedLoss Θ z k) x := by
  have hp : ∀ i, ScalarJetEq (firstOrderBlockCompletion (Θ i))
      (prefixGates (fun j => firstOrderBlockCompletion (Θ j)) k i) (x i) :=
    prefixGates_jetEq _ k (fun i => (firstOrderBlockCompletion_contDiff (Θ i)).of_le
      (show (2:WithTop ℕ∞)≤3 by decide)) x
      (fun i hi => firstOrderBlockCompletion_zeroJet (Θ i) (x i) (hfuture i hi))
  exact (firstOrderGatedChain_jetEq Θ x hp).add
    (reverseBlockSelector_jetEq hp (fun j _ => ScalarJetEq.refl (firstOrderNoisePayload_contDiff Θ z j 2) x))

def firstOrderTruncatedReply (Θ : Fin (T+1) → Fin d → Bool) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (k : ℕ) (x : FirstOrderSpace d T) : FirstOrderRichResponse d T :=
  (firstOrderTruncatedLoss Θ z k x,gradient (firstOrderTruncatedLoss Θ z k) x,
    fderiv ℝ (gradient (firstOrderTruncatedLoss Θ z k)) x)

theorem firstOrderRichReply_truncate (Θ : Fin (T+1) → Fin d → Bool) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (k : ℕ) (x : FirstOrderSpace d T)
    (hfuture : ∀ i, k ≤ i.val → firstOrderBlockCompletion (Θ i) (x i)=0) :
    firstOrderRichReply Θ z x=firstOrderTruncatedReply Θ z k x := by
  have h := firstOrderRandomLoss_truncate_jet Θ z k x hfuture
  exact Prod.ext h.value (Prod.ext h.gradient_eq h.hessian_eq)

end
end SecondOrder
