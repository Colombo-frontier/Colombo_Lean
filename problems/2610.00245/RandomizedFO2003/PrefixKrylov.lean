import RandomizedFO2003.ChronologicalKrylov

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Each inverse-query answer is tested against the degree available at
that operation. Later matrix actions cannot invalidate an earlier bound. -/
noncomputable def ActionProgram.prefixQueries (A : Module.End ℝ E) (u : E) (N : Submodule ℝ E) :
    (n : ℕ) → {H : Type u} → [MeasurableSpace H] → ActionProgram E n H →
      (Fin n → LatentOperation) → ℕ → ActionHistory E n H → Prop
  | 0, _, _, _, _, _, _ => True
  | n + 1, _, _, plan, ops, m, p =>
      (plan.1.kind = .query → (ActionHistory.seed E n p).2 ∈
        powerKrylovSpace A u ((ops 0).nextDepth m) ⊔ N) ∧
      prefixQueries A u N n plan.2 (fun i => ops i.succ) ((ops 0).nextDepth m) p

omit [BorelSpace E] in
/-- One common nuisance space and one nondegenerate execution suffice for
all query prefixes simultaneously. There is no union over truncations and
no new multiplicity choice for a shorter horizon. -/
theorem ActionProgram.directAmbient_prefixQueries (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (ops : Fin n → LatentOperation) (A : Module.End ℝ E) (u : E) (m : ℕ)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) (W : Ω → Submodule ℝ E)
    (N : Submodule ℝ E) (p : AmbientPairHistory E n Ω)
    (hsupport : (F (AmbientPairHistory.seed E n p)).KnownSupport)
    (hknown : embeddingComplement (F (AmbientPairHistory.seed E n p)).latent ≤ W (AmbientPairHistory.seed E n p))
    (hW : W (AmbientPairHistory.seed E n p) ≤ powerKrylovSpace A u m ⊔ N)
    (hN : N.map A ≤ N) (hstarts : AmbientPairHistory.AllIn E N n p)
    (hlegal : plan.KrylovLegal d A u n ops F history W p)
    (hgood : plan.directAmbientGood d n F history p) :
    plan.prefixQueries A u N n ops m (plan.directAmbientTranscript d n F history p) := by
  induction n generalizing H Ω m with
  | zero => trivial
  | succ n ih =>
    let q := AmbientPairHistory.seed E n p
    let nextF := ambientFrameNext plan.1.kind F (plan.1.vector ∘ history)
    let nextH := ambientObservedHistory plan.1 F history
    let nextW := fun q : (Ω × E) × E =>
      W q.1.1 ⊔ plan.1.kind.latentAddition (plan.1.vector (history q.1.1)) q.1.2 q.2
    have hnextSupport : (nextF q).KnownSupport := hsupport.paddedNext _ _ _ _
    have hnextKnown : embeddingComplement (nextF q).latent ≤ nextW q :=
      ((F q.1.1).paddedNext_latent_span plan.1.kind _ _ _ hgood.2.1 hgood.1).trans
        (sup_le_sup_right hknown _)
    have hstep : nextW q ≤ powerKrylovSpace A u ((ops 0).nextDepth m) ⊔ N := by
      have ht := (ops 0).step_bound A u m (W q.1.1) N (plan.1.vector (history q.1.1))
        q.1.2 q.2 hW hN hstarts.1 hstarts.2.1 hlegal.2.1
      rw [hlegal.1] at ht
      exact ht
    have htail := ih plan.2 (fun i => ops i.succ) ((ops 0).nextDepth m)
      nextF nextH nextW p hnextSupport hnextKnown hstep hstarts.2.2 hlegal.2.2 hgood.2.2
    have hs := plan.2.directAmbientTranscript_seed d n nextF nextH p
    constructor
    · intro hk
      change (ActionHistory.seed E n (plan.2.directAmbientTranscript d n nextF nextH p)).2 ∈ _
      rw [hs]
      apply hstep
      let one : ActionProgram E 1 H := (plan.1, PUnit.unit)
      have hg : one.directAmbientGood (d + n) 1 F history q := ⟨hgood.1, hgood.2.1, trivial⟩
      have hv : (nextH q).2 ∈ one.directAmbientQueries (d + n) 1 F history q := by
        simp only [one, ActionProgram.directAmbientQueries, hk, List.mem_cons, List.not_mem_nil, or_false]
        rfl
      exact one.directAmbientQueries_mem (d + n) 1 F history W q hsupport hknown hg _ hv
    · exact htail

end RandomizedFO2003.Rotations
