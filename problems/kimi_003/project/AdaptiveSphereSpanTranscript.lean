import AdaptiveSphereSpan
import AdaptiveSphereTranscript

open MeasureTheory Set

namespace Task006.AdaptiveSphereSpan
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereTranscript
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def transcriptQuerySpan (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) (h : Transcript N) : Submodule ℝ (E d) :=
  Submodule.span ℝ ((fun i : Fin N => effectiveVector weight tape (A.action i seed h)) ''
    {i : Fin N | i.val < t})

theorem transcriptQuerySpan_succ (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : ℕ) (ht : t < N) (h : Transcript N) :
    transcriptQuerySpan A weight tape seed (t+1) h = transcriptQuerySpan A weight tape seed t h ⊔
      Submodule.span ℝ {effectiveVector weight tape (A.action ⟨t,ht⟩ seed h)} := by
  have hindex : {i : Fin N | i.val<t+1} = insert (⟨t,ht⟩ : Fin N) {i : Fin N | i.val<t} := by
    ext i
    change i.val<t+1 ↔ i=(⟨t,ht⟩ : Fin N) ∨ i.val<t
    constructor
    · intro hi
      by_cases hi' : i.val<t
      · exact Or.inr hi'
      · exact Or.inl (Fin.ext (by change i.val=t; omega))
    · rintro (rfl | hi)
      · exact Nat.lt_succ_self t
      · omega
  simp only [transcriptQuerySpan,hindex,Set.image_insert_eq,Submodule.span_insert,sup_comm]

/-- For every counterfactual scalar history the explicit frame spans precisely
its effective query vectors, including dependent or full-rank queries. -/
theorem frameSpan_frameFromTranscript (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : ℕ) (ht : t ≤ N) (h : Transcript N) :
    frameSpan (frameFromTranscript A weight tape seed d le_rfl t h) =
      transcriptQuerySpan A weight tape seed t h := by
  induction t with
  | zero => simp [frameFromTranscript,initialState,frameSpan,transcriptQuerySpan]
  | succ t ih =>
    have hlt : t < N := by omega
    rw [frameFromTranscript,dif_pos hlt,frameSpan_stateStep_full,ih (by omega),
      transcriptQuerySpan_succ A weight tape seed t hlt h]

/-- The real original adaptive protocol's frame spans exactly its actual
measurement vectors, not merely a chosen subspace of them. -/
theorem actual_frameSpan_eq_measurementSpan (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : ℕ) (ht : t ≤ N) (θ : E d) :
    frameSpan (frameFromTranscript A weight tape seed d le_rfl t
      (A.runPrefix (linearSample weight θ) tape seed t)) =
      measurementSpanBefore A weight tape seed t θ := by
  rw [frameSpan_frameFromTranscript A weight tape seed t ht]
  have ha (i : Fin N) (hi : i.val<t) :
      A.action i seed (A.runPrefix (linearSample weight θ) tape seed t) =
        A.executedAction (linearSample weight θ) tape seed i := by
    apply A.past_only
    intro j hj
    exact runPrefix_coordinate_stable A (linearSample weight θ) tape seed i.val t (by omega) j hj
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,(congrArg (effectiveVector weight tape) (ha i hi)).symm⟩
  · rintro ⟨⟨i,hi⟩,rfl⟩
    exact ⟨i,hi,congrArg (effectiveVector weight tape) (ha i hi)⟩

#print axioms frameSpan_frameFromTranscript
#print axioms actual_frameSpan_eq_measurementSpan
end
end Task006.AdaptiveSphereSpan
