import SecondOrder.FirstOrderFrontierFormula

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T k : ℕ}

/-- Equality of the revealed hidden prefix and sampled prefix implies equality
of the entire truncated scalar functions, hence of all their derivatives. -/
theorem firstOrderTruncatedLoss_prefix_invariant
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z z' : FirstOrderCoefficients d T R) (hk : k≤T)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) (hz : ∀ i, i.val≤k → z i=z' i) :
    firstOrderTruncatedLoss Θ z k = firstOrderTruncatedLoss Θ' z' k := by
  funext x
  rw [firstOrderTruncatedLoss_frontier_formula Θ z k hk,
    firstOrderTruncatedLoss_frontier_formula Θ' z' k hk]
  congr 1
  apply frontierLossValue_congr
  · intro j hj
    have hjn : j<T+1 := by omega
    simp only [finZeroExtend, dif_pos hjn, hΘ ⟨j,hjn⟩ hj]
  · intro j hj
    have hjn : j<T+1 := by omega
    simp only [finZeroExtend, dif_pos hjn, hΘ ⟨j,hjn⟩ hj]
  · intro j hj
    have hjn : j<T+1 := by omega
    simp only [finZeroExtend, dif_pos hjn, hz ⟨j,hjn⟩ hj]

theorem firstOrderTruncatedReply_prefix_invariant
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z z' : FirstOrderCoefficients d T R) (hk : k≤T)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) (hz : ∀ i, i.val≤k → z i=z' i)
    (x : FirstOrderSpace d T) :
    firstOrderTruncatedReply Θ z k x = firstOrderTruncatedReply Θ' z' k x := by
  unfold firstOrderTruncatedReply
  rw [firstOrderTruncatedLoss_prefix_invariant Θ Θ' z z' hk hΘ hz]

def firstOrderExtendHiddenPrefix (θ₀ : (Fin d → Bool)) (past : Fin k → (Fin d → Bool))
    (i : Fin (T+1)) : (Fin d → Bool) := if hi : i.val<k then past ⟨i.val,hi⟩ else θ₀

abbrev FirstOrderPastCoefficients (d k : ℕ) (R : ℝ) :=
  Fin k → Fin d → SignedCoefficient R

def firstOrderExtendCoefficientPrefix {R : ℝ} (past : FirstOrderPastCoefficients d k R)
    (fresh : Fin d → SignedCoefficient R) (i : Fin (T+1)) :
    Fin d → SignedCoefficient R := if hi : i.val<k then past ⟨i.val,hi⟩ else fresh

/-- A response map whose arguments contain only revealed hidden blocks, past
coefficient arrays, and one fresh coefficient array. -/
def firstOrderFrontierReply (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    {R : ℝ} (x : FirstOrderSpace d T)
    (a : FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R)) :
    FirstOrderRichResponse d T :=
  firstOrderTruncatedReply (firstOrderExtendHiddenPrefix θ₀ pastΘ)
    (firstOrderExtendCoefficientPrefix a.1 a.2) k x

theorem firstOrderFrontierReply_base_independent (θ₀ θ₁ : (Fin d → Bool))
    (pastΘ : Fin k → (Fin d → Bool)) {R : ℝ} (hk : k≤T) (x : FirstOrderSpace d T)
    (a : FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R)) :
    firstOrderFrontierReply θ₀ pastΘ x a = firstOrderFrontierReply θ₁ pastΘ x a := by
  apply firstOrderTruncatedReply_prefix_invariant _ _ _ _ hk
  · intro i hi
    simp only [firstOrderExtendHiddenPrefix, dif_pos hi]
  · intro _ _
    rfl

/-- The extended response is the prefix map at every query point. -/
theorem firstOrderTruncatedReply_frontier_map (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) {R : ℝ} (z : FirstOrderCoefficients d T R)
    (hk : k≤T) (x : FirstOrderSpace d T) :
    firstOrderTruncatedReply Θ z k x =
      firstOrderFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) x
        ((fun i : Fin k => z ⟨i.val,by omega⟩), z ⟨k,by omega⟩) := by
  apply firstOrderTruncatedReply_prefix_invariant _ _ _ _ hk
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

/-- The actual full response is this prefix map whenever every later gate is
zero at the query. In particular the fresh hidden vector is absent from the map. -/
theorem firstOrderRichReply_frontier_map (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) {R : ℝ} (z : FirstOrderCoefficients d T R)
    (hk : k≤T) (x : FirstOrderSpace d T)
    (hfuture : ∀ i, k ≤ i.val → firstOrderBlockCompletion (Θ i) (x i)=0) :
    firstOrderRichReply Θ z x =
      firstOrderFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) x
        ((fun i : Fin k => z ⟨i.val,by omega⟩), z ⟨k,by omega⟩) := by
  rw [firstOrderRichReply_truncate Θ z k x hfuture]
  exact firstOrderTruncatedReply_frontier_map Θ θ₀ z hk x

end
end SecondOrder

