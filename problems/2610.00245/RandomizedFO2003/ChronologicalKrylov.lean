import RandomizedFO2003.KrylovOperations
import RandomizedFO2003.AmbientStarts
import RandomizedFO2003.AmbientQueryTrace

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

def LatentOperation.finalDepth : (n : ℕ) → (Fin n → LatentOperation) → ℕ → ℕ
  | 0, _, m => m
  | n + 1, ops, m => finalDepth n (fun i => ops i.succ) ((ops 0).nextDepth m)

theorem LatentOperation.finalDepth_no_mark (n : ℕ) (ops : Fin n → LatentOperation)
    (hops : ∀ i, ops i ≠ .mark true) : finalDepth n ops 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hfirst : (ops 0).nextDepth 0 = 0 := by
      cases h : ops 0 with
      | query => rfl
      | matrix => rfl
      | mark b => cases b <;> simp_all [nextDepth]
    simp only [finalDepth, hfirst]
    exact ih (fun i => ops i.succ) (fun i => hops i.succ)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-- An explicit pathwise certificate of legal matrix/mark requests. The
schedule may be chosen separately for each execution; this permits adaptive
authorization without treating authorization as an independent random seed. -/
noncomputable def ActionProgram.KrylovLegal (d : ℕ) (A : Module.End ℝ E) (u : E) :
    (n : ℕ) → {H Ω : Type u} → [MeasurableSpace H] → [MeasurableSpace Ω] →
    ActionProgram E n H → (Fin n → LatentOperation) →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) → (Ω → Submodule ℝ E) →
    AmbientPairHistory E n Ω → Prop
  | 0, _, _, _, _, _, _, _, _, _, _ => True
  | n + 1, _, _, _, _, plan, ops, F, history, W, p =>
      let q := AmbientPairHistory.seed E n p
      (ops 0).kind = plan.1.kind ∧
      (ops 0).Legal A u (W q.1.1) (plan.1.vector (history q.1.1)) ∧
      KrylovLegal d A u n plan.2 (fun i => ops i.succ)
        (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
        (ambientObservedHistory plan.1 F history)
        (fun q => W q.1.1 ⊔ plan.1.kind.latentAddition (plan.1.vector (history q.1.1)) q.1.2 q.2) p

/-- The cumulative span of an actual adaptive simulation has a marked degree
controlled solely by the certified chronological operations. -/
theorem ActionProgram.directAmbientBound_krylov (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (ops : Fin n → LatentOperation) (A : Module.End ℝ E) (u : E) (m : ℕ)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) (W : Ω → Submodule ℝ E)
    (N : Submodule ℝ E) (p : AmbientPairHistory E n Ω)
    (hW : W (AmbientPairHistory.seed E n p) ≤ powerKrylovSpace A u m ⊔ N)
    (hN : N.map A ≤ N) (hstarts : AmbientPairHistory.AllIn E N n p)
    (hlegal : plan.KrylovLegal d A u n ops F history W p) :
    plan.directAmbientBound d n F history W p ≤
      powerKrylovSpace A u (LatentOperation.finalDepth n ops m) ⊔ N := by
  induction n generalizing H Ω m with
  | zero => exact hW
  | succ n ih =>
    let q := AmbientPairHistory.seed E n p
    have hstep := (ops 0).step_bound A u m (W q.1.1) N
      (plan.1.vector (history q.1.1)) q.1.2 q.2 hW hN hstarts.1 hstarts.2.1 hlegal.2.1
    rw [hlegal.1] at hstep
    exact ih plan.2 (fun i => ops i.succ) ((ops 0).nextDepth m)
      (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history)
      (fun q => W q.1.1 ⊔ plan.1.kind.latentAddition (plan.1.vector (history q.1.1)) q.1.2 q.2)
      p hstep hstarts.2.2 hlegal.2.2

/-- Consequently the exact inverse-query subsequence, not just the exposed
frame, lies in the chronological Krylov bound. -/
theorem ActionProgram.selectedQueries_krylov (d n : ℕ) {H Ω : Type u}
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
    ∀ v ∈ plan.selectQueries n (plan.directAmbientTranscript d n F history p),
      v ∈ powerKrylovSpace A u (LatentOperation.finalDepth n ops m) ⊔ N := by
  rw [plan.selectQueries_directAmbient d n F history p]
  intro v hv
  exact (plan.directAmbientBound_krylov d n ops A u m F history W N p hW hN hstarts hlegal)
    (plan.directAmbientQueries_mem d n F history W p hsupport hknown hgood v hv)

end RandomizedFO2003.Rotations
