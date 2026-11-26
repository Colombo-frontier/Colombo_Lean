import AdaptiveSphereTranscript

/-!
Borel measurability of actual adaptive linear transcripts after fixing the
independent exogenous tape and private seed. No posterior distribution or
terminal energy bound is assumed.
-/

open MeasureTheory

namespace Task006.AdaptiveSphereMeasurable

open Task006.Full Task006.Full.OracleAlgorithm Task006.AdaptiveSphereTranscript

noncomputable section

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

/-- The optional-action sigma algebra in ModelFull is exactly this encoding. -/
theorem measurable_actionToSum : Measurable (actionToSum d) := by
  apply Measurable.of_comap_le
  exact le_rfl

/-- With the exogenous tape fixed, every effective query vector is measurable. -/
theorem measurable_effectiveVector (weight : Ω → ℝ) (tape : ℕ → Ω) :
    Measurable (effectiveVector (d := d) weight tape) := by
  have hw : Measurable (fun n : ℕ => weight (tape n)) := measurable_of_countable _
  let encoded : Unit ⊕ (ℕ × Space d) → Space d :=
    Sum.elim (fun _ => 0) (fun p => weight (tape p.1) • p.2)
  have hencoded : Measurable encoded := by
    exact measurable_const.sumElim ((hw.comp measurable_fst).smul measurable_snd)
  have heq : effectiveVector (d := d) weight tape = encoded ∘ actionToSum d := by
    funext q
    cases q with
    | none => rfl
    | some q => rcases q with ⟨handle, point⟩; rfl
  rw [heq]
  exact hencoded.comp measurable_actionToSum

/-- An arbitrary measurable finite policy has a measurable transcript in the
hidden direction, even with adaptive handles and second query points. -/
theorem measurable_linear_runPrefix
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) :
    Measurable (fun theta : Space d =>
      A.runPrefix (linearSample weight theta) tape seed t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < N
    · have hpair : Measurable (fun theta : Space d =>
          (seed, A.runPrefix (linearSample weight theta) tape seed t)) :=
        measurable_const.prodMk ih
      have ha : Measurable (fun theta : Space d =>
          A.action ⟨t, ht⟩ seed (A.runPrefix (linearSample weight theta) tape seed t)) :=
        (A.action_measurable ⟨t, ht⟩).comp hpair
      have hv : Measurable (fun theta : Space d => effectiveVector weight tape
          (A.action ⟨t, ht⟩ seed (A.runPrefix (linearSample weight theta) tape seed t))) :=
        (measurable_effectiveVector weight tape).comp ha
      have hreply : Measurable (fun theta : Space d => scalarReply
          (linearSample weight theta) tape
            (A.action ⟨t, ht⟩ seed (A.runPrefix (linearSample weight theta) tape seed t))) := by
        simp only [scalarReply_linear]
        exact measurable_id.inner hv
      have hup : Measurable (fun theta : Space d =>
          Function.update (A.runPrefix (linearSample weight theta) tape seed t)
            ⟨t, ht⟩ (scalarReply (linearSample weight theta) tape
              (A.action ⟨t, ht⟩ seed (A.runPrefix (linearSample weight theta) tape seed t)))) :=
        measurable_update'.comp (ih.prodMk hreply)
      simpa only [runPrefix, dif_pos ht] using hup
    · simpa only [runPrefix, dif_neg ht] using ih

theorem measurable_linear_finalTranscript
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) :
    Measurable (fun theta : Space d =>
      A.finalTranscript (linearSample weight theta) tape seed) :=
  measurable_linear_runPrefix A weight tape seed N

/-- The individual effective measurement chosen on the actual path is Borel. -/
theorem measurable_executed_effectiveVector
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (i : Fin N) :
    Measurable (fun theta : Space d => effectiveVector weight tape
      (A.executedAction (linearSample weight theta) tape seed i)) := by
  have hp : Measurable (fun theta : Space d =>
      (seed, A.runPrefix (linearSample weight theta) tape seed i.val)) :=
    measurable_const.prodMk (measurable_linear_runPrefix A weight tape seed i.val)
  exact (measurable_effectiveVector weight tape).comp ((A.action_measurable i).comp hp)

#print axioms measurable_effectiveVector
#print axioms measurable_linear_runPrefix
#print axioms measurable_linear_finalTranscript
#print axioms measurable_executed_effectiveVector

end
end Task006.AdaptiveSphereMeasurable
