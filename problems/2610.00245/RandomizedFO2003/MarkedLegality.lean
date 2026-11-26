import RandomizedFO2003.MarkedProgram

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The three concrete requests of a round satisfy the chronological legality
condition, using the exposed-space invariant to justify the matrix request. -/
theorem MarkedRoundPolicy.ambientLegal {H Ω : Type u} [MeasurableSpace H] [MeasurableSpace Ω]
    (policy : MarkedRoundPolicy E H) (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark)
    (d : ℕ) (F : Ω → ExposureFrame (Coordinates (d + 3)) E) (history : Ω → H)
    (W : Ω → Submodule ℝ E) (p : MarkedRoundAmbient E Ω)
    (hsupport : (F (AmbientPairHistory.seed E 3 p)).KnownSupport)
    (hknown : embeddingComplement (F (AmbientPairHistory.seed E 3 p)).latent ≤ W (AmbientPairHistory.seed E 3 p))
    (hgood : (policy.program A mark hm).directAmbientGood d 3 F history p) :
    (policy.program A mark hm).KrylovLegal d A.toLinearMap
      (mark (history (AmbientPairHistory.seed E 3 p))) 3
      (policy.operations (history (AmbientPairHistory.seed E 3 p))) F history W p := by
  let q := AmbientPairHistory.seed E 2 p
  let r := markedVectorRequest mark hm policy
  let F1 := ambientFrameNext r.kind F (r.vector ∘ history)
  let H1 := ambientObservedHistory r F history
  let W1 := fun q : (Ω × E) × E => W q.1.1 ⊔ r.kind.latentAddition (r.vector (history q.1.1)) q.1.2 q.2
  have hs1 : (F1 q).KnownSupport := hsupport.paddedNext _ _ _ _
  have hw1 : embeddingComplement (F1 q).latent ≤ W1 q :=
    ((F q.1.1).paddedNext_latent_span r.kind _ _ _ hgood.2.1 hgood.1).trans
      (sup_le_sup_right hknown _)
  refine ⟨rfl, ?_, rfl, trivial, rfl, ?_, trivial⟩
  · exact markedVectorRequest_legal mark hm policy A.toLinearMap _ _
  · exact matrixResponseRequest_legal A _ (F1 q) hs1 (W1 q) hw1
      (H1 q) (policy.query (H1 q)) (AmbientPairHistory.seed E 1 p).2

/-- Every round of the complete adaptive strategy is legal. No Krylov legality
assumption on the policy is used: it follows from the concrete request syntax
and the frame/space invariants already proved for actual simulation histories. -/
theorem MarkedProgram.ambientLegal (d t : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : MarkedProgram E t H)
    (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark)
    (F : Ω → ExposureFrame (Coordinates (d + markedActionCount t)) E) (history : Ω → H)
    (W : Ω → Submodule ℝ E) (p : AmbientPairHistory E (markedActionCount t) Ω)
    (hsupport : (F (AmbientPairHistory.seed E (markedActionCount t) p)).KnownSupport)
    (hknown : embeddingComplement (F (AmbientPairHistory.seed E (markedActionCount t) p)).latent ≤
      W (AmbientPairHistory.seed E (markedActionCount t) p))
    (hgood : (plan.compile A t mark hm).directAmbientGood d (markedActionCount t) F history p) :
    (plan.compile A t mark hm).KrylovLegal d A.toLinearMap
      (mark (history (AmbientPairHistory.seed E (markedActionCount t) p))) (markedActionCount t)
      (plan.ambientOperations A d t mark hm F history p) F history W p := by
  induction t generalizing H Ω with
  | zero => trivial
  | succ t ih =>
    let n := markedActionCount t
    let round := plan.1.program A mark hm
    let q := AmbientPairHistory.seed E n p
    let F' := round.directAmbientFinalFrame (d + n) 3 F history
    let H' := round.directAmbientTranscript (d + n) 3 F history
    let W' := round.directAmbientBound (d + n) 3 F history W
    have hroundGood : round.directAmbientGood (d + n) 3 F history q :=
      ⟨hgood.1, hgood.2.1, hgood.2.2.1, hgood.2.2.2.1,
        hgood.2.2.2.2.1, hgood.2.2.2.2.2.1, trivial⟩
    have hroundLegal := plan.1.ambientLegal A mark hm (d + n) F history W q hsupport hknown hroundGood
    have htailSupport : (F' q).KnownSupport :=
      round.directAmbientFinalFrame_support (d + n) 3 F history q hsupport
    have htailKnown : embeddingComplement (F' q).latent ≤ W' q :=
      round.directAmbientFinalFrame_bound (d + n) 3 F history W q hknown hroundGood
    have htail := ih plan.2 (mark ∘ ActionHistory.seed E 3)
      (hm.comp (ActionHistory.seed_measurable 3)) F' H' W' p htailSupport htailKnown
      hgood.2.2.2.2.2.2
    have hmark : (mark ∘ ActionHistory.seed E 3) (H' q) =
        mark (history (AmbientPairHistory.seed E (markedActionCount (t + 1)) p)) :=
      plan.1.mark_preserved A mark hm (d + n) F history q
    rw [hmark] at htail
    exact ⟨hroundLegal.1, hroundLegal.2.1, hroundLegal.2.2.1, hroundLegal.2.2.2.1,
      hroundLegal.2.2.2.2.1, hroundLegal.2.2.2.2.2.1, htail⟩

end RandomizedFO2003.Rotations
