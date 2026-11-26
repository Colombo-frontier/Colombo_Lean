import NCConcave16991.BranchOracleRequestMeasurable
import NCConcave16991.OracleProgramLibrary

/-! # A measurable total reply format for finite-vertex mixed programs

A reply records the answer only at the requested vertex and zero elsewhere.
Thus ordinary fixed-query programs can use the dependent mixed request API
without receiving any unrequested information.
-/

namespace NCConcave16991.BranchOracle
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

abbrev MixedReply := ∀ t : Vertex M m, VertexLayer (ι := ι) E M m t

def fillReply (t : Vertex M m) (x : VertexLayer (ι := ι) E M m t) : MixedReply (ι := ι) E M m :=
  fun s ↦ if h : s = t then layerCast E (congrArg Fin.val h.symm) x else 0

theorem fillReply_self (t : Vertex M m) (x : VertexLayer (ι := ι) E M m t) :
    fillReply E M m t x t = x := by simp [fillReply, layerCast]

theorem fillReply_other (t s : Vertex M m) (x : VertexLayer (ι := ι) E M m t) (h : s ≠ t) :
    fillReply E M m t x s = 0 := by simp only [fillReply, dif_neg h]

theorem fillReply_measurable (t : Vertex M m) : Measurable (fillReply (ι := ι) E M m t) := by
  apply measurable_pi_iff.mpr
  intro s
  by_cases hs : s = t
  · subst s
    convert (measurable_id : Measurable (fun x : VertexLayer (ι := ι) E M m t ↦ x)) using 1
    funext x
    exact fillReply_self E M m t x
  · simpa only [fillReply, dif_neg hs] using (measurable_const : Measurable (fun _ : VertexLayer (ι := ι) E M m t ↦ (0 : VertexLayer (ι := ι) E M m s)))

def replyOracle
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (q : MixedRequest (ι := ι) E M m) : MixedReply (ι := ι) E M m :=
  fillReply E M m q.1 (requestAnswer E M m Q q)

theorem replyOracle_at_request
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (q : MixedRequest (ι := ι) E M m) :
    replyOracle E M m Q q q.1 = requestAnswer E M m Q q := fillReply_self E M m _ _

theorem replyOracle_measurable
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t) :
    Measurable (replyOracle E M m Q) := by
  apply measurable_sigma_elim
  intro t
  change Measurable (Sum.elim
    (fun a ↦ fillReply E M m t (Q t.val a))
    (fun b ↦ fillReply E M m t ((Q t.val).symm b)))
  exact ((fillReply_measurable E M m t).comp (Q t.val).continuous.measurable).sumElim
    ((fillReply_measurable E M m t).comp (Q t.val).symm.continuous.measurable)

end
end NCConcave16991.BranchOracle
