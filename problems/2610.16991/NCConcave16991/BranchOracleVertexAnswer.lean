import NCConcave16991.BranchOracleVertexEngine

/-! # The actual native sparse answer is exactly the branch program oracle -/

namespace NCConcave16991.BranchOracle
noncomputable section
open MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

theorem replyOracle_eq_nativeRequestAnswer
    (θ : NativeOrthogonal (NativeWordFamily (ι := ι) E M m))
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d)
    (hQ : ∀ t : Vertex M m, Q t.val = nativeVertexOperator (NativeWordFamily (ι := ι) E M m) θ t)
    (q : MixedRequest (ι := ι) E M m) :
    replyOracle E M m Q q = nativeRequestAnswer (NativeWordFamily (ι := ι) E M m) θ q := by
  funext t
  by_cases ht : q.1 = t
  · rcases q with ⟨v, a | b⟩
    · dsimp only at ht
      subst t
      calc
        _ = Q v.val a := replyOracle_at_request E M m Q ⟨v, Sum.inl a⟩
        _ = nativeVertexOperator (NativeWordFamily (ι := ι) E M m) θ v a := congrArg (fun L ↦ L a) (hQ v)
        _ = _ := (nativeRequestAnswer_forward (NativeWordFamily (ι := ι) E M m) θ v a).symm
    · dsimp only at ht
      subst t
      calc
        _ = (Q v.val).symm b := replyOracle_at_request E M m Q ⟨v, Sum.inr b⟩
        _ = (nativeVertexOperator (NativeWordFamily (ι := ι) E M m) θ v).symm b := congrArg (fun L ↦ L.symm b) (hQ v)
        _ = _ := (nativeRequestAnswer_inverse (NativeWordFamily (ι := ι) E M m) θ v b).symm
  · rw [nativeRequestAnswer_unselected _ θ q t ht]
    exact fillReply_other E M m q.1 t _ (Ne.symm ht)

end
end NCConcave16991.BranchOracle
