import MatchingBounds1005.ScheduledHaar
import RandomizedFO2003.MatrixRequests

/-! # Chronological containment for actual scheduled Haar simulations

The matrix request is the quadratic operator applied to the inverse answer
actually returned by the preceding query. No query-containment or adaptive
conditional-invariance hypothesis is assumed.
-/

namespace MatchingBounds1005.ScheduledHaar

open MeasureTheory RandomizedFO2003.Rotations

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def RoundRequest.program {H : Type u} [MeasurableSpace H]
    (request : RoundRequest E H) (Q : E →L[ℝ] E) : ActionProgram E 3 H :=
  RoundPolicy.compile Q 1 (request, PUnit.unit)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem map_scheduled_sup (Q : E →L[ℝ] E) (I J N : Submodule ℝ E)
    (hI : I.map Q.toLinearMap ≤ J) (hN : N.map Q.toLinearMap ≤ N) :
    (I ⊔ N).map Q.toLinearMap ≤ J ⊔ N := by
  rw [Submodule.map_sup]
  exact sup_le (hI.trans le_sup_left) (hN.trans le_sup_right)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem span_pair_le {W : Submodule ℝ E} {a b : E}
    (ha : a ∈ W) (hb : b ∈ W) : Submodule.span ℝ {a, b} ≤ W := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · exact ha
  · exact Set.mem_singleton_iff.mp hv ▸ hb

/-- Exact one-round chronological step. The inverse answer is bounded by
`I + N` before its matrix product enlarges the exposed space to `J + N`.
The nondegeneracy event is the concrete event already proved to have full
measure for the actual ambient-product simulation. -/
theorem RoundRequest.chronological_step {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω]
    (request : RoundRequest E H) (Q : E →L[ℝ] E) (d : ℕ)
    (F : Ω → ExposureFrame (Coordinates (d + 3)) E) (history : Ω → H)
    (W : Ω → Submodule ℝ E) (p : AmbientPairHistory E 3 Ω)
    (I J N : Submodule ℝ E) (hIJ : I ≤ J)
    (hstep : I.map Q.toLinearMap ≤ J ∨ ∀ h, request.query h = 0)
    (hQN : N.map Q.toLinearMap ≤ N)
    (hc : request.column ∈ I)
    (hsupport : (F (AmbientPairHistory.seed E 3 p)).KnownSupport)
    (hknown : embeddingComplement (F (AmbientPairHistory.seed E 3 p)).latent ≤
      W (AmbientPairHistory.seed E 3 p))
    (hW : W (AmbientPairHistory.seed E 3 p) ≤ I ⊔ N)
    (hstarts : AmbientPairHistory.AllIn E N 3 p)
    (hgood : (request.program Q).directAmbientGood d 3 F history p) :
    (∀ v ∈ (request.program Q).directAmbientQueries d 3 F history p, v ∈ I ⊔ N) ∧
      (request.program Q).directAmbientBound d 3 F history W p ≤ J ⊔ N := by
  let r₁ : ExposureRequest H E := ⟨.response, fun _ => request.column, measurable_const⟩
  let F₁ := ambientFrameNext r₁.kind F (r₁.vector ∘ history)
  let H₁ := ambientObservedHistory r₁ F history
  let W₁ := fun q : (Ω × E) × E =>
    W q.1.1 ⊔ r₁.kind.latentAddition (r₁.vector (history q.1.1)) q.1.2 q.2
  let r₂ : ExposureRequest (H × E) E := ⟨.query, request.query, request.measurable_query⟩
  let F₂ := ambientFrameNext r₂.kind F₁ (r₂.vector ∘ H₁)
  let H₂ := ambientObservedHistory r₂ F₁ H₁
  let W₂ := fun q : (((Ω × E) × E) × E) × E =>
    W₁ q.1.1 ⊔ r₂.kind.latentAddition (r₂.vector (H₁ q.1.1)) q.1.2 q.2
  let q₁ := AmbientPairHistory.seed E 2 p
  let q₂ := AmbientPairHistory.seed E 1 p
  have hs₁ : (F₁ q₁).KnownSupport := hsupport.paddedNext _ _ _ _
  have hk₁ : embeddingComplement (F₁ q₁).latent ≤ W₁ q₁ :=
    ((F q₁.1.1).paddedNext_latent_span r₁.kind _ _ _ hgood.2.1 hgood.1).trans
      (sup_le_sup_right hknown _)
  have hw₁ : W₁ q₁ ≤ I ⊔ N := by
    change W q₁.1.1 ⊔ Submodule.span ℝ {request.column, q₁.1.2} ≤ I ⊔ N
    exact sup_le hW (span_pair_le (Submodule.mem_sup_left hc)
      (Submodule.mem_sup_right hstarts.1))
  have hw₂ : W₂ q₂ ≤ I ⊔ N := by
    change W₁ q₁ ⊔ Submodule.span ℝ {q₂.2} ≤ I ⊔ N
    refine sup_le hw₁ ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    exact Submodule.mem_sup_right hstarts.2.2.2.1
  have hξ : (H₂ q₂).2 ∈ I ⊔ N := by
    apply hw₂
    exact hs₁.ambientQueryValue_mem (W₁ q₁) hk₁ (request.query (H₁ q₁)) q₂.2
  have hQξ : Q (H₂ q₂).2 ∈ J ⊔ N := by
    rcases hstep with hQI | hzero
    · exact map_scheduled_sup Q I J N hQI hQN ⟨_, hξ, rfl⟩
    · have hz : (H₂ q₂).2 = 0 := by
        simp [H₂, ambientObservedHistory, r₂, hzero, ExposureFrame.exposedValue]
      rw [hz, map_zero]
      exact Submodule.zero_mem _
  constructor
  · intro v hv
    have heq : (request.program Q).directAmbientQueries d 3 F history p = [(H₂ q₂).2] := rfl
    rw [heq, List.mem_singleton] at hv
    exact hv ▸ hξ
  · change W₂ q₂ ⊔ Submodule.span ℝ {Q (H₂ q₂).2, p.1.2} ≤ J ⊔ N
    refine sup_le (hw₂.trans (sup_le_sup_right hIJ N)) ?_
    exact span_pair_le hQξ (Submodule.mem_sup_right hstarts.2.2.2.2.1)

/-- Only public deterministic spaces and the actual syntax of zero-query
padding occur in this schedule condition. There is no containment premise
on any adaptively selected nonzero query. -/
def RoundPolicy.Scheduled (Q : E →L[ℝ] E) : (n : ℕ) → {H : Type u} →
    [MeasurableSpace H] → RoundPolicy E n H → (ℕ → Submodule ℝ E) → Prop
  | 0, _, _, _, _ => True
  | n + 1, _, _, plan, I =>
      plan.1.column ∈ I 0 ∧
      ((I 0).map Q.toLinearMap ≤ I 1 ∨ ∀ h, plan.1.query h = 0) ∧
      Scheduled Q n plan.2 (fun t => I (t + 1))

def ChronologicalIn (I : ℕ → Submodule ℝ E) (N : Submodule ℝ E) : List E → Prop
  | [] => True
  | v :: vs => v ∈ I 0 ⊔ N ∧ ChronologicalIn (fun t => I (t + 1)) N vs

/-- Every query has its own pre-response bound. In particular, the last
matrix response cannot incorrectly authorize a previously hidden readout. -/
theorem RoundPolicy.chronological_containment (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω]
    (plan : RoundPolicy E n H) (Q : E →L[ℝ] E)
    (F : Ω → ExposureFrame (Coordinates (d + actionCount n)) E) (history : Ω → H)
    (W : Ω → Submodule ℝ E) (p : AmbientPairHistory E (actionCount n) Ω)
    (I : ℕ → Submodule ℝ E) (N : Submodule ℝ E)
    (hmono : ∀ t, I t ≤ I (t + 1)) (hQN : N.map Q.toLinearMap ≤ N)
    (hschedule : plan.Scheduled Q n I)
    (hsupport : (F (AmbientPairHistory.seed E (actionCount n) p)).KnownSupport)
    (hknown : embeddingComplement (F (AmbientPairHistory.seed E (actionCount n) p)).latent ≤
      W (AmbientPairHistory.seed E (actionCount n) p))
    (hW : W (AmbientPairHistory.seed E (actionCount n) p) ≤ I 0 ⊔ N)
    (hstarts : AmbientPairHistory.AllIn E N (actionCount n) p)
    (hgood : (plan.compile Q n).directAmbientGood d (actionCount n) F history p) :
    ChronologicalIn I N ((plan.compile Q n).directAmbientQueries d (actionCount n) F history p) ∧
      (plan.compile Q n).directAmbientBound d (actionCount n) F history W p ≤ I n ⊔ N := by
  induction n generalizing H Ω I with
  | zero => exact ⟨trivial, hW⟩
  | succ n ih =>
    let k := actionCount n
    let round := plan.1.program Q
    let q := AmbientPairHistory.seed E k p
    let F' := round.directAmbientFinalFrame (d + k) 3 F history
    let H' := round.directAmbientTranscript (d + k) 3 F history
    let W' := round.directAmbientBound (d + k) 3 F history W
    have hroundGood : round.directAmbientGood (d + k) 3 F history q :=
      ⟨hgood.1, hgood.2.1, hgood.2.2.1, hgood.2.2.2.1,
        hgood.2.2.2.2.1, hgood.2.2.2.2.2.1, trivial⟩
    have hroundStarts : AmbientPairHistory.AllIn E N 3 q :=
      ⟨hstarts.1, hstarts.2.1, hstarts.2.2.1, hstarts.2.2.2.1,
        hstarts.2.2.2.2.1, hstarts.2.2.2.2.2.1, trivial⟩
    have hround := plan.1.chronological_step Q (d + k) F history W q
      (I 0) (I 1) N (hmono 0) hschedule.2.1 hQN hschedule.1
      hsupport hknown hW hroundStarts hroundGood
    have hs' : (F' q).KnownSupport :=
      round.directAmbientFinalFrame_support (d + k) 3 F history q hsupport
    have hk' : embeddingComplement (F' q).latent ≤ W' q :=
      round.directAmbientFinalFrame_bound (d + k) 3 F history W q hknown hroundGood
    have htail := ih plan.2 F' H' W' p (fun t => I (t + 1))
      (fun t => hmono (t + 1)) hschedule.2.2 hs' hk' hround.2
      hstarts.2.2.2.2.2.2 hgood.2.2.2.2.2.2
    obtain ⟨ξ, hξ⟩ : ∃ ξ, round.directAmbientQueries (d + k) 3 F history q = [ξ] := ⟨_, rfl⟩
    have hmem : ξ ∈ I 0 ⊔ N := hround.1 ξ (by rw [hξ]; exact List.mem_singleton_self ξ)
    constructor
    · have heq : (plan.compile Q (n + 1)).directAmbientQueries d (actionCount (n + 1)) F history p =
          round.directAmbientQueries (d + k) 3 F history q ++
            (plan.2.compile Q n).directAmbientQueries d k F' H' p := rfl
      rw [heq, hξ, List.singleton_append]
      exact ⟨hmem, htail.1⟩
    · exact htail.2

/-- The actual quadratic cyclic span of a fixed family of ambient starts. -/
noncomputable def cyclicSpan {m : ℕ} (Q : E →L[ℝ] E) (g : Fin m → E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun p : ℕ × Fin m => (Q.toLinearMap ^ p.1) (g p.2)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem start_mem_cyclicSpan {m : ℕ} (Q : E →L[ℝ] E) (g : Fin m → E) (i : Fin m) :
    g i ∈ cyclicSpan Q g := by
  exact Submodule.subset_span ⟨(0, i), by simp⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem cyclicSpan_invariant {m : ℕ} (Q : E →L[ℝ] E) (g : Fin m → E) :
    (cyclicSpan Q g).map Q.toLinearMap ≤ cyclicSpan Q g := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro v ⟨⟨j, i⟩, rfl⟩
  change Q ((Q.toLinearMap ^ j) (g i)) ∈ cyclicSpan Q g
  exact Submodule.subset_span ⟨(j + 1, i), by simp [pow_succ', Module.End.mul_apply]⟩

/-- Under the actual product sphere law, every latent query lies in its
scheduled subspace plus the cyclic span of the original independent starts.
All frame nondegeneracy and information-space conditions are discharged. -/
theorem RoundPolicy.ae_chronological_containment (d n : ℕ) {H : Type u}
    [MeasurableSpace H] (μ : Measure H) [SFinite μ]
    (Q : Coordinates (d + actionCount n) →L[ℝ] Coordinates (d + actionCount n))
    (plan : RoundPolicy (Coordinates (d + actionCount n)) n H)
    (I : ℕ → Submodule ℝ (Coordinates (d + actionCount n)))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q n I) :
    ∀ᵐ p ∂ambientPairHistoryLaw (Coordinates (d + actionCount n)) (actionCount n) μ,
      ChronologicalIn I
        (cyclicSpan Q (AmbientPairHistory.starts (Coordinates (d + actionCount n)) (actionCount n) p))
        ((plan.compile Q n).selectQueries (actionCount n)
          ((plan.compile Q n).directAmbientTranscript d (actionCount n) (fun _ => .initial) id p)) := by
  let F := fun _ : H => (ExposureFrame.initial :
    ExposureFrame (Coordinates (d + actionCount n)) (Coordinates (d + actionCount n)))
  have hF : ExposureFrame.MeasurableFamily F := ExposureFrame.measurable_initial
  filter_upwards [(plan.compile Q n).directAmbientGood_ae d (actionCount n) μ F hF id measurable_id]
    with p hp
  let N := cyclicSpan Q
    (AmbientPairHistory.starts (Coordinates (d + actionCount n)) (actionCount n) p)
  have hs : AmbientPairHistory.AllIn (Coordinates (d + actionCount n)) N (actionCount n) p := by
    rw [AmbientPairHistory.allIn_iff_starts]
    intro i
    exact start_mem_cyclicSpan Q _ i
  rw [ActionProgram.selectQueries_directAmbient]
  exact (plan.chronological_containment d n Q F id (fun _ => ⊥) p I N hmono
    (cyclicSpan_invariant Q _) hschedule ExposureFrame.initial_knownSupport
    (by rw [initial_latentComplement]) bot_le hs hp).1

/-- The preceding bound is attached to a simulation with exactly the law
of the actual one-Haar-rotation scheduled oracle, rather than an unrelated
random witness process. There are `6*n` iid ambient starts. -/
theorem RoundPolicy.haar_ambient_chronological (d n : ℕ) {H : Type u}
    [MeasurableSpace H] (μ : Measure H) [SFinite μ]
    (Q : Coordinates (d + actionCount n) →L[ℝ] Coordinates (d + actionCount n))
    (plan : RoundPolicy (Coordinates (d + actionCount n)) n H)
    (I : ℕ → Submodule ℝ (Coordinates (d + actionCount n)))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q n I) :
    (μ.prod (haarLaw (Coordinates (d + actionCount n)))).map
      (fun p => plan.run n Q (p.2 : Coordinates (d + actionCount n) →L[ℝ]
        Coordinates (d + actionCount n)) p.1) =
      (ambientPairHistoryLaw (Coordinates (d + actionCount n)) (actionCount n) μ).map
        ((plan.compile Q n).directAmbientTranscript d (actionCount n) (fun _ => .initial) id) ∧
    (∀ᵐ p ∂ambientPairHistoryLaw (Coordinates (d + actionCount n)) (actionCount n) μ,
      ChronologicalIn I
        (cyclicSpan Q (AmbientPairHistory.starts (Coordinates (d + actionCount n)) (actionCount n) p))
        ((plan.compile Q n).selectQueries (actionCount n)
          ((plan.compile Q n).directAmbientTranscript d (actionCount n) (fun _ => .initial) id p))) := by
  constructor
  · simpa only [RoundPolicy.run_eq_compiled] using
      ((plan.compile Q n).haar_ambient_information d (actionCount n) μ).2.1
  · exact plan.ae_chronological_containment d n μ Q I hmono hschedule

theorem ambient_start_count (n : ℕ) : actionCount n + actionCount n = 6 * n := by
  rw [actionCount_eq]
  omega

/-- Change only the seed/history interface, preserving every actual response. -/
noncomputable def RoundPolicy.reseed : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → RoundPolicy E n H →
    (f : Ω → H) → Measurable f → RoundPolicy E n Ω
  | 0, _, _, _, _, _, _, _ => PUnit.unit
  | n + 1, _, _, _, _, plan, f, hf =>
      (⟨plan.1.column, fun h => plan.1.query (f h.1, h.2),
          plan.1.measurable_query.comp (hf.prodMap measurable_id)⟩,
        reseed n plan.2 (Prod.map (Prod.map (Prod.map f id) id) id)
          (((hf.prodMap measurable_id).prodMap measurable_id).prodMap measurable_id))

omit [BorelSpace E] in
theorem RoundPolicy.reseed_run (n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : RoundPolicy E n H)
    (f : Ω → H) (hf : Measurable f) (Q U : E →L[ℝ] E) (h : Ω) :
    ActionHistory.map E (actionCount n) f ((plan.reseed n f hf).run n Q U h) =
      plan.run n Q U (f h) := by
  induction n generalizing H Ω with
  | zero => rfl
  | succ n ih =>
    exact ih plan.2 (Prod.map (Prod.map (Prod.map f id) id) id)
      (((hf.prodMap measurable_id).prodMap measurable_id).prodMap measurable_id)
      (((h, U plan.1.column), U.adjoint (plan.1.query (f h, U plan.1.column))),
        U (Q (U.adjoint (plan.1.query (f h, U plan.1.column)))))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem RoundPolicy.reseed_scheduled (n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : RoundPolicy E n H)
    (f : Ω → H) (hf : Measurable f) (Q : E →L[ℝ] E)
    (I : ℕ → Submodule ℝ E) (hs : plan.Scheduled Q n I) :
    (plan.reseed n f hf).Scheduled Q n I := by
  induction n generalizing H Ω I with
  | zero => trivial
  | succ n ih =>
    refine ⟨hs.1, ?_, ?_⟩
    · rcases hs.2.1 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (fun h => hz _)
    · exact ih plan.2 _ _ (fun t => I (t + 1)) hs.2.2

/-- Source commands distinguish actual matrix-oracle calls from public
column disclosures and a candidate frozen without any oracle response. -/
inductive SourceKind where
  | disclose
  | query
  | candidate
  deriving DecidableEq

def SourceHistory (E : Type) : List SourceKind → Type u → Type u
  | [], H => H
  | .disclose :: w, H => SourceHistory E w (H × E)
  | .query :: w, H => SourceHistory E w ((H × E) × E)
  | .candidate :: w, H => SourceHistory E w (H × E)

instance sourceHistoryMeasurableSpace : (w : List SourceKind) → (H : Type u) →
    [MeasurableSpace H] → MeasurableSpace (SourceHistory E w H)
  | [], _, m => m
  | .disclose :: w, H, _ => sourceHistoryMeasurableSpace w (H × E)
  | .query :: w, H, _ => sourceHistoryMeasurableSpace w ((H × E) × E)
  | .candidate :: w, H, _ => sourceHistoryMeasurableSpace w (H × E)

structure PhysicalRequest (H : Type u) [MeasurableSpace H] where
  point : H → E
  measurable_point : Measurable point

def SourcePolicy : (w : List SourceKind) → (H : Type u) → [MeasurableSpace H] → Type u
  | [], _, _ => PUnit
  | .disclose :: w, H, _ => E × SourcePolicy w (H × E)
  | .query :: w, H, _ => PhysicalRequest (E := E) H × SourcePolicy w ((H × E) × E)
  | .candidate :: w, H, _ => PhysicalRequest (E := E) H × SourcePolicy w (H × E)

/-- The candidate branch appends only a point computed from the existing
history. It calls neither the matrix oracle nor any latent-coordinate oracle. -/
noncomputable def SourcePolicy.run : (w : List SourceKind) → {H : Type u} →
    [MeasurableSpace H] → SourcePolicy (E := E) w H →
      (E →L[ℝ] E) → (E →L[ℝ] E) → H → SourceHistory E w H
  | [], _, _, _, _, _, h => h
  | .disclose :: w, _, _, plan, Q, U, h => run w plan.2 Q U (h, U plan.1)
  | .query :: w, _, _, plan, Q, U, h =>
      let ξ := U.adjoint (plan.1.point h)
      run w plan.2 Q U ((h, ξ), U (Q ξ))
  | .candidate :: w, _, _, plan, Q, U, h => run w plan.2 Q U (h, plan.1.point h)

noncomputable def SourcePolicy.compile : (w : List SourceKind) → {H : Type u} →
    [MeasurableSpace H] → SourcePolicy (E := E) w H → RoundPolicy E w.length H
  | [], _, _, _ => PUnit.unit
  | .disclose :: w, _, _, plan =>
      (⟨plan.1, fun _ => 0, measurable_const⟩,
        (compile w plan.2).reseed w.length (fun h => h.1.1) measurable_fst.fst)
  | .query :: w, _, _, plan =>
      (⟨0, fun h => plan.1.point h.1, plan.1.measurable_point.comp measurable_fst⟩,
        (compile w plan.2).reseed w.length (fun h => ((h.1.1.1, h.1.2), h.2))
          ((measurable_fst.fst.fst.prodMk measurable_fst.snd).prodMk measurable_snd))
  | .candidate :: w, _, _, plan =>
      (⟨0, fun h => plan.1.point h.1, plan.1.measurable_point.comp measurable_fst⟩,
        (compile w plan.2).reseed w.length (fun h => (h.1.1.1, plan.1.point h.1.1.1))
          (measurable_fst.fst.fst.prodMk (plan.1.measurable_point.comp measurable_fst.fst.fst)))

noncomputable def SourcePolicy.decode : (w : List SourceKind) → {H : Type u} →
    [MeasurableSpace H] → SourcePolicy (E := E) w H →
      ActionHistory E (actionCount w.length) H → SourceHistory E w H
  | [], _, _, _ => id
  | .disclose :: w, _, _, plan =>
      decode w plan.2 ∘ ActionHistory.map E (actionCount w.length) (fun h => h.1.1)
  | .query :: w, _, _, plan =>
      decode w plan.2 ∘ ActionHistory.map E (actionCount w.length) (fun h => ((h.1.1.1, h.1.2), h.2))
  | .candidate :: w, _, _, plan =>
      decode w plan.2 ∘ ActionHistory.map E (actionCount w.length)
        (fun h => (h.1.1.1, plan.1.point h.1.1.1))

omit [BorelSpace E] in
/-- Exact source semantics: dummy zero queries and analyst-only candidate
observations are discarded. A candidate is fixed before those observations. -/
theorem SourcePolicy.compile_correct (w : List SourceKind) {H : Type u}
    [MeasurableSpace H] (plan : SourcePolicy (E := E) w H)
    (Q U : E →L[ℝ] E) (h : H) :
    plan.decode w ((plan.compile w).run w.length Q U h) = plan.run w Q U h := by
  induction w generalizing H with
  | nil => rfl
  | cons kind w ih =>
    cases kind <;>
      simp only [SourcePolicy.decode, SourcePolicy.compile, List.length_cons, RoundPolicy.run,
        Function.comp_apply, RoundPolicy.reseed_run, SourcePolicy.run] <;>
      exact ih plan.2 _

def SourcePolicy.Scheduled (Q : E →L[ℝ] E) : (w : List SourceKind) →
    {H : Type u} → [MeasurableSpace H] → SourcePolicy (E := E) w H →
      (ℕ → Submodule ℝ E) → Prop
  | [], _, _, _, _ => True
  | .disclose :: w, _, _, plan, I => plan.1 ∈ I 0 ∧ Scheduled Q w plan.2 (fun t => I (t + 1))
  | .query :: w, _, _, plan, I => (I 0).map Q.toLinearMap ≤ I 1 ∧
      Scheduled Q w plan.2 (fun t => I (t + 1))
  | .candidate :: w, _, _, plan, I => (I 0).map Q.toLinearMap ≤ I 1 ∧
      Scheduled Q w plan.2 (fun t => I (t + 1))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem SourcePolicy.compile_scheduled (w : List SourceKind) {H : Type u}
    [MeasurableSpace H] (plan : SourcePolicy (E := E) w H) (Q : E →L[ℝ] E)
    (I : ℕ → Submodule ℝ E) (hs : plan.Scheduled Q w I) :
    (plan.compile w).Scheduled Q w.length I := by
  induction w generalizing H I with
  | nil => trivial
  | cons kind w ih =>
    cases kind with
    | disclose =>
      refine ⟨hs.1, Or.inr (fun _ => rfl), ?_⟩
      exact RoundPolicy.reseed_scheduled w.length _ _ _ Q _ (ih plan.2 _ hs.2)
    | query =>
      refine ⟨Submodule.zero_mem _, Or.inl hs.1, ?_⟩
      exact RoundPolicy.reseed_scheduled w.length _ _ _ Q _ (ih plan.2 _ hs.2)
    | candidate =>
      refine ⟨Submodule.zero_mem _, Or.inl hs.1, ?_⟩
      exact RoundPolicy.reseed_scheduled w.length _ _ _ Q _ (ih plan.2 _ hs.2)

def commandCount (kind : SourceKind) : List SourceKind → ℕ
  | [] => 0
  | k :: w => (if k = kind then 1 else 0) + commandCount kind w

theorem command_counts (w : List SourceKind) : w.length =
    commandCount .disclose w + commandCount .query w + commandCount .candidate w := by
  induction w with
  | nil => rfl
  | cons k w ih => cases k <;> simp [commandCount, ih] <;> omega

/-- Disclosing each canonical coordinate once and adding one unqueried
candidate costs O(D₀+T) independent starts, not O(D₀*T). -/
theorem source_start_budget (w : List SourceKind) (D₀ T : ℕ)
    (hd : commandCount .disclose w ≤ D₀) (hq : commandCount .query w ≤ T)
    (hc : commandCount .candidate w ≤ 1) :
    actionCount w.length + actionCount w.length ≤ 6 * (D₀ + T + 1) := by
  rw [ambient_start_count, command_counts]
  omega

/-- Public oracle time. Disclosures do not advance it. A final candidate
uses one analyst slot after it has been frozen. -/
def commandClock : List SourceKind → ℕ → ℕ → ℕ
  | [], start, _ => start
  | _ :: _, start, 0 => start
  | .disclose :: w, start, j + 1 => commandClock w start j
  | .query :: w, start, j + 1 => commandClock w (start + 1) j
  | .candidate :: w, start, j + 1 => commandClock w (start + 1) j

@[simp] theorem commandClock_zero (w : List SourceKind) (start : ℕ) :
    commandClock w start 0 = start := by
  cases w with
  | nil => rfl
  | cons k w => cases k <;> rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem calendar_spaces_mono (w : List SourceKind) (start : ℕ)
    (I : ℕ → Submodule ℝ E) (hI : ∀ t, I t ≤ I (t + 1)) :
    ∀ j, I (commandClock w start j) ≤ I (commandClock w start (j + 1)) := by
  induction w generalizing start with
  | nil => intro j; exact le_rfl
  | cons k w ih =>
    intro j
    cases j with
    | zero =>
      cases k <;> simp only [commandClock, commandClock_zero]
      · exact le_rfl
      · exact hI start
      · exact hI start
    | succ j => cases k <;> exact ih _ j

/-- Membership of the actually disclosed canonical columns in the public
calendar. This mentions no random query or random subspace. -/
def SourcePolicy.ColumnsAt (I : ℕ → Submodule ℝ E) : (w : List SourceKind) →
    {H : Type u} → [MeasurableSpace H] → SourcePolicy (E := E) w H → ℕ → Prop
  | [], _, _, _, _ => True
  | .disclose :: w, _, _, plan, start =>
      plan.1 ∈ I start ∧ ColumnsAt I w plan.2 start
  | .query :: w, _, _, plan, start => ColumnsAt I w plan.2 (start + 1)
  | .candidate :: w, _, _, plan, start => ColumnsAt I w plan.2 (start + 1)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Source schedule legality is derived from deterministic propagation and
the actual disclosed columns, including an arbitrary number of disclosures
at the same oracle time. -/
theorem SourcePolicy.scheduled_of_calendar (w : List SourceKind) {H : Type u}
    [MeasurableSpace H] (plan : SourcePolicy (E := E) w H) (Q : E →L[ℝ] E)
    (I : ℕ → Submodule ℝ E) (hQI : ∀ t, (I t).map Q.toLinearMap ≤ I (t + 1))
    (start : ℕ) (hc : plan.ColumnsAt I w start) :
    plan.Scheduled Q w (fun j => I (commandClock w start j)) := by
  induction w generalizing H start with
  | nil => trivial
  | cons k w ih =>
    cases k with
    | disclose => exact ⟨hc.1, ih plan.2 start hc.2⟩
    | query =>
      refine ⟨?_, ih plan.2 (start + 1) hc⟩
      simpa only [commandClock, commandClock_zero] using hQI start
    | candidate =>
      refine ⟨?_, ih plan.2 (start + 1) hc⟩
      simpa only [commandClock, commandClock_zero] using hQI start

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem SourcePolicy.decode_measurable (w : List SourceKind) {H : Type u}
    [MeasurableSpace H] (plan : SourcePolicy (E := E) w H) : Measurable (plan.decode w) := by
  induction w generalizing H with
  | nil => exact measurable_id
  | cons k w ih =>
    cases k with
    | disclose =>
      exact (ih plan.2).comp (ActionHistory.map_measurable (actionCount w.length) _ measurable_fst.fst)
    | query =>
      exact (ih plan.2).comp (ActionHistory.map_measurable (actionCount w.length) _
        ((measurable_fst.fst.fst.prodMk measurable_fst.snd).prodMk measurable_snd))
    | candidate =>
      exact (ih plan.2).comp (ActionHistory.map_measurable (actionCount w.length) _
        (measurable_fst.fst.fst.prodMk (plan.1.measurable_point.comp measurable_fst.fst.fst)))

/-- Exact source transcript law, including candidates with no oracle reply,
together with chronological containment of all actual and analyst inverse
queries. Public schedule conditions suffice; no query-span condition is an
input hypothesis. -/
theorem SourcePolicy.haar_ambient_containment (w : List SourceKind) (d : ℕ) {H : Type u}
    [MeasurableSpace H] (μ : Measure H) [SFinite μ]
    (Q : Coordinates (d + actionCount w.length) →L[ℝ] Coordinates (d + actionCount w.length))
    (plan : SourcePolicy (E := Coordinates (d + actionCount w.length)) w H)
    (I : ℕ → Submodule ℝ (Coordinates (d + actionCount w.length)))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q w I) :
    (μ.prod (haarLaw (Coordinates (d + actionCount w.length)))).map
      (fun p => plan.run w Q (p.2 : Coordinates (d + actionCount w.length) →L[ℝ]
        Coordinates (d + actionCount w.length)) p.1) =
      (ambientPairHistoryLaw (Coordinates (d + actionCount w.length)) (actionCount w.length) μ).map
        (fun p => plan.decode w (((plan.compile w).compile Q w.length).directAmbientTranscript
          d (actionCount w.length) (fun _ => .initial) id p)) ∧
    (∀ᵐ p ∂ambientPairHistoryLaw (Coordinates (d + actionCount w.length)) (actionCount w.length) μ,
      ChronologicalIn I
        (cyclicSpan Q (AmbientPairHistory.starts (Coordinates (d + actionCount w.length))
          (actionCount w.length) p))
        (((plan.compile w).compile Q w.length).selectQueries (actionCount w.length)
          (((plan.compile w).compile Q w.length).directAmbientTranscript d (actionCount w.length)
            (fun _ => .initial) id p))) := by
  have hr := (plan.compile w).haar_ambient_chronological d w.length μ Q I hmono
    (plan.compile_scheduled w Q I hschedule)
  refine ⟨?_, hr.2⟩
  have hdec := plan.decode_measurable w
  have htr := (((plan.compile w).compile Q w.length).haar_ambient_information
    d (actionCount w.length) μ).1
  have hp := congrArg (fun ν => ν.map (plan.decode w)) hr.1
  dsimp only at hp
  rw [Measure.map_map hdec ((plan.compile w).run_measurable d w.length Q),
    Measure.map_map hdec htr] at hp
  simpa only [Function.comp_def, SourcePolicy.compile_correct] using hp

end MatchingBounds1005.ScheduledHaar
