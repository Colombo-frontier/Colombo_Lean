import SecondOrder.CurvatureFrontierFormula

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T k : ℕ}

/-- Equality of the revealed hidden prefix and sampled prefix implies equality
of the entire truncated scalar functions, hence of all their derivatives. -/
theorem curvatureTruncatedLoss_prefix_invariant
    (Θ Θ' : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z z' : CurvatureCoefficients m T R) (hk : k≤T)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) (hz : ∀ i, i.val≤k → z i=z' i) :
    curvatureTruncatedLoss Θ z k = curvatureTruncatedLoss Θ' z' k := by
  funext x
  rw [curvatureTruncatedLoss_frontier_formula Θ z k hk,
    curvatureTruncatedLoss_frontier_formula Θ' z' k hk]
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

theorem curvatureTruncatedReply_prefix_invariant
    (Θ Θ' : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z z' : CurvatureCoefficients m T R) (hk : k≤T)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) (hz : ∀ i, i.val≤k → z i=z' i)
    (x : CurvatureSpace m T) :
    curvatureTruncatedReply Θ z k x = curvatureTruncatedReply Θ' z' k x := by
  unfold curvatureTruncatedReply
  rw [curvatureTruncatedLoss_prefix_invariant Θ Θ' z z' hk hΘ hz]

def extendHiddenPrefix (θ₀ : BalancedVector m) (past : Fin k → BalancedVector m)
    (i : Fin (T+1)) : BalancedVector m := if hi : i.val<k then past ⟨i.val,hi⟩ else θ₀

abbrev CurvaturePastCoefficients (m k : ℕ) (R : ℝ) :=
  Fin k → UpperPair (2*m) → SignedCoefficient R

def extendCoefficientPrefix {R : ℝ} (past : CurvaturePastCoefficients m k R)
    (fresh : UpperPair (2*m) → SignedCoefficient R) (i : Fin (T+1)) :
    UpperPair (2*m) → SignedCoefficient R := if hi : i.val<k then past ⟨i.val,hi⟩ else fresh

/-- A response map whose arguments contain only revealed hidden blocks, past
coefficient arrays, and one fresh coefficient array. -/
def curvatureFrontierReply (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    {R : ℝ} (x : CurvatureSpace m T)
    (a : CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R)) :
    CurvatureRichResponse m T :=
  curvatureTruncatedReply (extendHiddenPrefix θ₀ pastΘ)
    (extendCoefficientPrefix a.1 a.2) k x

theorem curvatureFrontierReply_base_independent (θ₀ θ₁ : BalancedVector m)
    (pastΘ : Fin k → BalancedVector m) {R : ℝ} (hk : k≤T) (x : CurvatureSpace m T)
    (a : CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R)) :
    curvatureFrontierReply θ₀ pastΘ x a = curvatureFrontierReply θ₁ pastΘ x a := by
  apply curvatureTruncatedReply_prefix_invariant _ _ _ _ hk
  · intro i hi
    simp only [extendHiddenPrefix, dif_pos hi]
  · intro _ _
    rfl

/-- The extended response is the prefix map at every query point. -/
theorem curvatureTruncatedReply_frontier_map (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) {R : ℝ} (z : CurvatureCoefficients m T R)
    (hk : k≤T) (x : CurvatureSpace m T) :
    curvatureTruncatedReply Θ z k x =
      curvatureFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) x
        ((fun i : Fin k => z ⟨i.val,by omega⟩), z ⟨k,by omega⟩) := by
  apply curvatureTruncatedReply_prefix_invariant _ _ _ _ hk
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

/-- The actual full response is this prefix map whenever every later gate is
zero at the query. In particular the fresh hidden vector is absent from the map. -/
theorem curvatureRichReply_frontier_map (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) {R : ℝ} (z : CurvatureCoefficients m T R)
    (hk : k≤T) (x : CurvatureSpace m T)
    (hfuture : ∀ i, k ≤ i.val → periodicCompletion (Θ i) (x i)=0) :
    curvatureRichReply Θ z x =
      curvatureFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) x
        ((fun i : Fin k => z ⟨i.val,by omega⟩), z ⟨k,by omega⟩) := by
  rw [curvatureRichReply_truncate Θ z k x hfuture]
  exact curvatureTruncatedReply_frontier_map Θ θ₀ z hk x

end
end SecondOrder
