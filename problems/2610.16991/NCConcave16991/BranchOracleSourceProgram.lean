import NCConcave16991.BranchOracleReply

/-! # Public prefix source exposure as a genuine finite mixed program -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

def sourceQueries (a : ℕ × E) (t : Vertex M m) : MixedRequest (ι := ι) E M m :=
  ⟨t, Sum.inl (if t.val ≤ a.1 * (m + 1) then formalTarget E t.val a.2 else 0)⟩

theorem sourceQueries_measurable (t : Vertex M m) : Measurable (fun a ↦ sourceQueries (ι := ι) E M m a t) := by
  apply measurable_from_prod_countable_right
  intro r
  by_cases ht : t.val ≤ r * (m + 1)
  · convert sourceRequest_measurable (ι := ι) E M m t using 1
    funext x
    simp only [sourceQueries, if_pos ht, sourceRequest]
  · convert (measurable_const : Measurable (fun _ : E ↦
      (⟨t, Sum.inl (0 : VertexLayer (ι := ι) E M m t)⟩ : MixedRequest (ι := ι) E M m))) using 1
    funext x
    simp only [sourceQueries, if_neg ht]

def decodeSourceReplies (replies : Vertex M m → MixedReply (ι := ι) E M m) : MixedReply (ι := ι) E M m :=
  fun t ↦ replies t t

theorem decodeSourceReplies_measurable : Measurable (decodeSourceReplies (ι := ι) E M m) :=
  measurable_pi_iff.mpr (fun t ↦ (measurable_pi_apply t).comp (measurable_pi_apply t))

def sourceProgram :
    OracleProgram.Fixed (MixedRequest (ι := ι) E M m) (MixedReply (ι := ι) E M m)
      (MixedReply (ι := ι) E M m) (ℕ × E) (M * (m + 1) + 1) :=
  OracleProgram.map (OracleProgram.fullPass (sourceQueries E M m) (sourceQueries_measurable E M m))
    (decodeSourceReplies E M m) (decodeSourceReplies_measurable E M m)

theorem eval_sourceProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t) (r : ℕ) (e : E) :
    OracleProgram.eval (sourceProgram E M m) (replyOracle E M m Q) (r, e) =
      (fun t : Vertex M m ↦ if t.val ≤ r * (m + 1) then Q t.val (formalTarget E t.val e) else 0) := by
  rw [sourceProgram, OracleProgram.eval_map, OracleProgram.eval_fullPass]
  funext t
  change replyOracle E M m Q (sourceQueries E M m (r, e) t) t = _
  rw [show replyOracle E M m Q (sourceQueries E M m (r, e) t) t =
    requestAnswer E M m Q (sourceQueries E M m (r, e) t) from
      replyOracle_at_request E M m Q (sourceQueries E M m (r, e) t)]
  dsimp only [sourceQueries, requestAnswer]
  split_ifs with ht
  · rfl
  · exact (Q t.val).map_zero

def sourcesFromCache (r : ℕ) (cache : MixedReply (ι := ι) E M m) : SourceParameters (MacroSpaces (ι := ι) E M m) :=
  ((fun j ↦ if j.val ≤ r then cache (depthVertex M m j 0) else 0),
   (fun j ↦ if j.val < r then cache (depthVertex M m j (Fin.last (m + 1))) else 0))

theorem sourcesFromCache_measurable : Measurable (fun a : ℕ × MixedReply (ι := ι) E M m ↦ sourcesFromCache E M m a.1 a.2) := by
  apply measurable_from_prod_countable_right
  intro r
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro j
    by_cases hj : j.val ≤ r
    · simpa only [sourcesFromCache, if_pos hj] using (measurable_pi_apply (depthVertex M m j 0))
    · simpa only [sourcesFromCache, if_neg hj] using (measurable_const : Measurable (fun _ : MixedReply (ι := ι) E M m ↦ (0 : MacroSpaces (ι := ι) E M m j 0)))
  · apply measurable_pi_iff.mpr
    intro j
    by_cases hj : j.val < r
    · simpa only [sourcesFromCache, if_pos hj] using (measurable_pi_apply (depthVertex M m j (Fin.last (m + 1))))
    · simpa only [sourcesFromCache, if_neg hj] using (measurable_const : Measurable (fun _ : MixedReply (ι := ι) E M m ↦ (0 : MacroSpaces (ι := ι) E M m j (Fin.last (m + 1)))))

theorem sourcesFromCache_eval_sourceProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t) (r : ℕ) (e : E) :
    sourcesFromCache E M m r (OracleProgram.eval (sourceProgram E M m) (replyOracle E M m Q) (r, e)) =
      (knownIncoming (MacroSpaces (ι := ι) E M m) r (incomingSources E Q e),
       knownTerminal (MacroSpaces (ι := ι) E M m) r (terminalSources E Q e)) := by
  rw [eval_sourceProgram]
  apply Prod.ext
  · funext j
    by_cases hj : j.val ≤ r
    · have ht := Nat.mul_le_mul_right (m + 1) hj
      simp only [sourcesFromCache, knownIncoming, hj, if_true, depthVertex, Fin.val_zero, Nat.add_zero, incomingSources, ht]
    · simp only [sourcesFromCache, knownIncoming, if_neg hj]
  · funext j
    by_cases hj : j.val < r
    · have ht := Nat.mul_le_mul_right (m + 1) (Nat.succ_le_iff.mpr hj)
      have ht' : j.val * (m + 1) + (m + 1) ≤ r * (m + 1) := by simpa only [Nat.succ_mul] using ht
      simp only [sourcesFromCache, knownTerminal, hj, if_true, depthVertex, Fin.val_last, terminalSources, macroSite, ht']
    · simp only [sourcesFromCache, knownTerminal, if_neg hj]

end
end NCConcave16991.BranchOracle
