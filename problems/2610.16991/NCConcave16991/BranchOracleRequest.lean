import NCConcave16991.BranchOracleMatrixProtocol
import NCConcave16991.BranchOracleResponseMeasurable

/-! # Literal finite-vertex mixed requests for the actual branch oracle

Every physical block of a component query is marked before the simultaneous
matrix round.  Each matrix reply is then one forward request on a formal
prepend or slice of a stored inverse mark.  Source requests use the literal
uniform formal target.  These definitions contain no hidden branch maps.
-/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (M m : ℕ)

abbrev Vertex := Fin (M * (m + 1) + 1)
abbrev VertexLayer (t : Vertex M m) := FormalLayer (ι := ι) E t.val

abbrev MixedRequest := Σ t : Vertex M m, VertexLayer (ι := ι) E M m t ⊕ VertexLayer (ι := ι) E M m t

abbrev MixedAnswer (q : MixedRequest (ι := ι) E M m) := VertexLayer (ι := ι) E M m q.1

def requestAnswer
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (q : MixedRequest (ι := ι) E M m) : MixedAnswer E M m q :=
  match q.2 with
  | Sum.inl a => Q q.1.val a
  | Sum.inr b => (Q q.1.val).symm b

def depthVertex (j : Fin M) (k : Fin (m + 1 + 1)) : Vertex M m :=
  ⟨j.val * (m + 1) + k.val, Nat.lt_succ_of_le (macroDepth_le_total j k)⟩

def queryRequest (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m))
    (t : Vertex M m) (slot : Fin 5) : MixedRequest (ι := ι) E M m :=
  ⟨t, Sum.inr (queryMark E M m t.val slot z)⟩

abbrev InverseMarks := ∀ t : Vertex M m, Fin 5 → VertexLayer (ι := ι) E M m t

def queryInverseMarks
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m)) : InverseMarks (ι := ι) E M m :=
  fun t slot ↦ requestAnswer E M m Q (queryRequest E M m z t slot)

def forwardMatrixRequest (marks : InverseMarks (ι := ι) E M m) (i : ι)
    (j : Fin M) (k : Fin (m + 1)) : MixedRequest (ι := ι) E M m :=
  ⟨depthVertex M m j k.succ, Sum.inl
    (prepend E (j.val * (m + 1) + k.val) i (marks (depthVertex M m j k.castSucc) 3))⟩

def transposeMatrixRequest (marks : InverseMarks (ι := ι) E M m) (i : ι)
    (j : Fin M) (k : Fin (m + 1)) : MixedRequest (ι := ι) E M m :=
  ⟨depthVertex M m j k.castSucc, Sum.inl
    (slice E (j.val * (m + 1) + k.val) i
      (marks (depthVertex M m j k.succ) (if k.succ.val < m + 1 then 3 else 4)))⟩

def sourceRequest (t : Vertex M m) (e : E) : MixedRequest (ι := ι) E M m :=
  ⟨t, Sum.inl (formalTarget E t.val e)⟩

variable (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)

theorem forwardMatrixRequest_answer (i : ι) (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m))
    (j : Fin M) (k : Fin (m + 1)) :
    requestAnswer E M m Q (forwardMatrixRequest E M m (queryInverseMarks E M m Q z) i j k) =
      (macroBranches E Q j k).branch i
        ((PiLp.proj (𝕜 := ℝ) 2 (MacroSpaces (ι := ι) E M m j) k.castSucc) (dualProj (MacroSpaces (ι := ι) E M m) j z)) := by
  dsimp only [requestAnswer, forwardMatrixRequest, queryInverseMarks, queryRequest, depthVertex]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_assoc, macroBranch_forward,
    queryMark_interiorDual, ContinuousLinearMap.comp_apply]
  rfl

theorem transposeMatrixRequest_answer (i : ι) (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m))
    (j : Fin M) (k : Fin (m + 1)) :
    requestAnswer E M m Q (transposeMatrixRequest E M m (queryInverseMarks E M m Q z) i j k) =
      ((macroBranches E Q j k).branch i).toContinuousLinearMap.adjoint
        ((PiLp.proj (𝕜 := ℝ) 2 (MacroSpaces (ι := ι) E M m j) k.succ) (dualProj (MacroSpaces (ι := ι) E M m) j z)) := by
  dsimp only [requestAnswer, transposeMatrixRequest, queryInverseMarks, queryRequest, depthVertex]
  rw [queryMark_dual (ι := ι) E j k.succ, ContinuousLinearMap.comp_apply,
    macroBranch_transpose]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]
  rfl

theorem sourceRequest_answer (t : Vertex M m) (e : E) :
    requestAnswer E M m Q (sourceRequest E M m t e) = Q t.val (formalTarget E t.val e) := rfl

variable [FiniteDimensional ℝ E]

def outputRequest (c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m)))
    (t : Vertex M m) : MixedRequest (ι := ι) E M m :=
  ⟨t, Sum.inr (outputMark E M m t.val c)⟩

theorem outputRequest_source (c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m))) (j : Fin M) :
    requestAnswer E M m Q (outputRequest E M m c (depthVertex M m j (Fin.last (m + 1)))) =
      (Q (macroSite m j)).symm (returnedSourceProbe (MacroSpaces (ι := ι) E M m) j c) := by
  change (Q (macroSite m j)).symm (outputMark E M m (macroSite m j) c) = _
  rw [outputMark_source]

end
end NCConcave16991.BranchOracle
