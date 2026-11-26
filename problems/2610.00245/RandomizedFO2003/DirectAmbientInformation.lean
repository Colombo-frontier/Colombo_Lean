import RandomizedFO2003.DirectAmbientGood

namespace RandomizedFO2003.Rotations

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-- Known operator support remains valid through the entire direct simulation. -/
theorem ActionProgram.directAmbientFinalFrame_support (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H)
    (p : AmbientPairHistory E n Ω) (hF : (F (AmbientPairHistory.seed E n p)).KnownSupport) :
    (plan.directAmbientFinalFrame d n F history p).KnownSupport := by
  induction n generalizing H Ω with
  | zero => exact hF
  | succ n ih =>
    exact ih plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history) p (hF.paddedNext _ _ _ _)

/-- The cumulative span bound always contains its initial space. -/
theorem ActionProgram.directAmbientBound_contains (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) (W : Ω → Submodule ℝ E)
    (p : AmbientPairHistory E n Ω) :
    W (AmbientPairHistory.seed E n p) ≤ plan.directAmbientBound d n F history W p := by
  induction n generalizing H Ω with
  | zero => exact le_rfl
  | succ n ih =>
    exact le_sup_left.trans (ih plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history)
      (fun q => W q.1.1 ⊔ plan.1.kind.latentAddition (plan.1.vector (history q.1.1)) q.1.2 q.2) p)

/-- The single-step latent-space bound holds along every nondegenerate finite
execution, with no independence or span hypotheses silently introduced. -/
theorem ActionProgram.directAmbientFinalFrame_bound (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) (W : Ω → Submodule ℝ E)
    (p : AmbientPairHistory E n Ω)
    (hW : embeddingComplement (F (AmbientPairHistory.seed E n p)).latent ≤ W (AmbientPairHistory.seed E n p))
    (hp : plan.directAmbientGood d n F history p) :
    embeddingComplement (plan.directAmbientFinalFrame d n F history p).latent ≤
      plan.directAmbientBound d n F history W p := by
  induction n generalizing H Ω with
  | zero => exact hW
  | succ n ih =>
    let q := AmbientPairHistory.seed E n p
    have hnext : embeddingComplement (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history) q).latent ≤
        W q.1.1 ⊔ plan.1.kind.latentAddition (plan.1.vector (history q.1.1)) q.1.2 q.2 :=
      ((F q.1.1).paddedNext_latent_span plan.1.kind _ _ _ hp.2.1 hp.1).trans (sup_le_sup_right hW _)
    exact ih plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history)
      (fun q => W q.1.1 ⊔ plan.1.kind.latentAddition (plan.1.vector (history q.1.1)) q.1.2 q.2)
      p hnext hp.2.2

noncomputable def ActionProgram.directAmbientQueries (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) → AmbientPairHistory E n Ω → List E
  | 0, _, _, _, _, _, _, _, _ => []
  | n + 1, _, _, _, _, plan, F, history, p =>
    let rest := directAmbientQueries d n plan.2
      (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history)) (ambientObservedHistory plan.1 F history) p
    match plan.1.kind with
    | .query => (ambientObservedHistory plan.1 F history (AmbientPairHistory.seed E n p)).2 :: rest
    | .response => rest

/-- Every inverse-query vector returned to the policy lies in the final span
bound, so the result controls all queried latent vectors, not just the final frame. -/
theorem ActionProgram.directAmbientQueries_mem (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) (W : Ω → Submodule ℝ E)
    (p : AmbientPairHistory E n Ω) (hF : (F (AmbientPairHistory.seed E n p)).KnownSupport)
    (hW : embeddingComplement (F (AmbientPairHistory.seed E n p)).latent ≤ W (AmbientPairHistory.seed E n p))
    (hp : plan.directAmbientGood d n F history p) :
    ∀ v ∈ plan.directAmbientQueries d n F history p, v ∈ plan.directAmbientBound d n F history W p := by
  induction n generalizing H Ω with
  | zero => simp [ActionProgram.directAmbientQueries]
  | succ n ih =>
    let q := AmbientPairHistory.seed E n p
    let nextF := ambientFrameNext plan.1.kind F (plan.1.vector ∘ history)
    let nextH := ambientObservedHistory plan.1 F history
    let nextW := fun q : (Ω × E) × E =>
      W q.1.1 ⊔ plan.1.kind.latentAddition (plan.1.vector (history q.1.1)) q.1.2 q.2
    have hnextF : (nextF q).KnownSupport := hF.paddedNext _ _ _ _
    have hnextW : embeddingComplement (nextF q).latent ≤ nextW q :=
      ((F q.1.1).paddedNext_latent_span plan.1.kind _ _ _ hp.2.1 hp.1).trans (sup_le_sup_right hW _)
    have htail := ih plan.2 nextF nextH nextW p hnextF hnextW hp.2.2
    have hgrow := plan.2.directAmbientBound_contains d n nextF nextH nextW p
    have hquery : plan.1.kind = .query → (nextH q).2 ∈
        plan.2.directAmbientBound d n nextF nextH nextW p := by
      intro hk
      apply hgrow
      apply hnextW
      change (nextH q).2 ∈ embeddingComplement (nextF q).latent
      dsimp [nextH, nextF, ambientObservedHistory, ambientFrameNext]
      rw [hk]
      change (F q.1.1).known.adjoint (plan.1.vector (history q.1.1)) +
        ‖(F q.1.1).physical.toContinuousLinearMap.adjoint (plan.1.vector (history q.1.1))‖ •
          (F q.1.1).latent (Spherical.projectedDirection (F q.1.1).latent q.2) ∈
        embeddingComplement
          (((F q.1.1).afterQuery (firstDirection (d + n)) (plan.1.vector (history q.1.1))
            (Spherical.projectedDirection (F q.1.1).latent q.2)).latent.comp
              (tailCoordinates (d + n)).symm.toLinearIsometry)
      rw [embeddingComplement_reindex]
      apply hF.queryValue_mem _ (norm_firstDirection (d + n))
      apply Spherical.radial_norm
      simpa only [hk, ExposureFrame.innovationEmbedding] using hp.2.1
    intro v hv
    cases hk : plan.1.kind with
    | query =>
      change v ∈ plan.2.directAmbientBound d n nextF nextH nextW p
      have hv' : v = (nextH q).2 ∨ v ∈ plan.2.directAmbientQueries d n nextF nextH p := by
        simpa only [ActionProgram.directAmbientQueries, nextF, nextH, q, hk, List.mem_cons] using hv
      rcases hv' with rfl | hv'
      · exact hquery hk
      · exact htail v hv'
    | response =>
      apply htail v
      simpa only [ActionProgram.directAmbientQueries, nextF, nextH, hk] using hv

end RandomizedFO2003.Rotations
