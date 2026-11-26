import NCConcave16991.BranchOracleLedger
import NCConcave16991.OracleProgramStateLibrary

/-! # The exact algebraic interface of the actual Gaussian frame engine

The birth vector is the requested formal input in the forward case and the
assigned ambient Gaussian in the inverse case.  No norm or correlation
estimate is part of this interface.
-/

namespace NCConcave16991.BranchOracle
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

structure WordEngine (S : Type*) where
  ledger : S → DomainLedger (ι := ι) E M m
  oracle : S → MixedRequest (ι := ι) E M m → S × MixedReply (ι := ι) E M m
  gaussian : S → MixedReply (ι := ι) E M m
  admissible : S → Prop
  admissible_step : ∀ s q, admissible s → admissible (oracle s q).1
  domain_le : ∀ s q t, ledger (oracle s q).1 t ≤
    ledgerBirth E M m (ledger s) q.1 (requestBirthVector E M m q (gaussian s)) t
  inverse_reply_mem : ∀ s (t : Vertex M m) (b : VertexLayer (ι := ι) E M m t),
    (oracle s ⟨t, Sum.inr b⟩).2 t ∈ ledger s t ⊔ Submodule.span ℝ ({gaussian s t} : Set (VertexLayer (ι := ι) E M m t))

variable {S : Type*} (A : WordEngine (ι := ι) E M m S)
variable {E M m}

def WordEngine.Covered (W : Submodule ℝ E) : Prop := ∀ s, A.admissible s → ∀ t w, A.gaussian s t w ∈ W

theorem WordEngine.step_supported (p : WordProfile ι) (W : Submodule ℝ E) (hW : A.Covered W)
    (s : S) (hvalid : A.admissible s) (hs : LedgerSupported E M m p W (A.ledger s))
    (q : MixedRequest (ι := ι) E M m) (hq : RequestFormalSupported E M m p W q) :
    LedgerSupported E M m p W (A.ledger (A.oracle s q).1) :=
  requestBirth_supported E M m p W (A.ledger s) (A.ledger (A.oracle s q).1) hs q (A.gaussian s) hq (hW s hvalid)
    (A.domain_le s q)

theorem WordEngine.inverse_reply_supported (p : WordProfile ι) (W : Submodule ℝ E) (hW : A.Covered W)
    (s : S) (hvalid : A.admissible s) (hs : LedgerSupported E M m p W (A.ledger s))
    (t : Vertex M m) (b : VertexLayer (ι := ι) E M m t) :
    (A.oracle s ⟨t, Sum.inr b⟩).2 t ∈ wordSupport t.val (p.words t.val) W :=
  inverse_span_mem_wordSupport (p.words t.val) W (A.ledger s t) (hs t)
    (A.gaussian s t) _ (hW s hvalid t) (A.inverse_reply_mem s t b)

theorem WordEngine.evalState_admissible {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {T : ℕ}
    (P : OracleProgram.Fixed (MixedRequest (ι := ι) E M m) (MixedReply (ι := ι) E M m) X Ω T)
    (seed : Ω) (s : S) (hvalid : A.admissible s) :
    A.admissible (OracleProgram.evalState P A.oracle seed s).2 := by
  apply OracleProgram.evalState_spec P A.oracle seed (fun _ _ s ↦ A.admissible s) (fun _ s ↦ A.admissible s)
  · intro _ _ hs
    exact hs
  · intro t ht replies state hs
    exact A.admissible_step state _ hs
  · exact hvalid

end
end NCConcave16991.BranchOracle
