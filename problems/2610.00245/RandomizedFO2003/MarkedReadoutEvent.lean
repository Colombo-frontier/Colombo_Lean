import RandomizedFO2003.MarkedSpectral

namespace RandomizedFO2003.Rotations

open MeasureTheory SpectralCoordinates

universe u

/-- The inverse-query response in each of the fixed three-slot rounds. -/
def markedQueryTrace (E : Type) : (t : ℕ) → {H : Type u} →
    ActionHistory E (markedActionCount t) H → Fin t → E
  | 0, _, _ => Fin.elim0
  | t + 1, H, p => Fin.cons
      ((ActionHistory.seed E (markedActionCount t + 1) (H := (H × E) × E) p).2)
      (markedQueryTrace E t p)

theorem markedQueryTrace_measurable {E : Type} [MeasurableSpace E] (t : ℕ)
    {H : Type u} [MeasurableSpace H] (i : Fin t) :
    Measurable (fun p : ActionHistory E (markedActionCount t) H => markedQueryTrace E t p i) := by
  induction t generalizing H with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (ActionHistory.seed_measurable (markedActionCount t + 1)).snd
    · exact ih j

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem MarkedProgram.selectQueries_eq (t : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram E t H) (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark)
    (p : ActionHistory E (markedActionCount t) H) :
    (plan.compile A t mark hm).selectQueries (markedActionCount t) p = List.ofFn (markedQueryTrace E t p) := by
  induction t generalizing H with
  | zero => rfl
  | succ t ih =>
    simp only [MarkedProgram.compile, markedActionCount, ActionProgram.selectQueries,
      markedVectorRequest, matrixResponseRequest, markedQueryTrace, List.ofFn_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [ih plan.2 (mark ∘ ActionHistory.seed E 3) (hm.comp (ActionHistory.seed_measurable 3))]

end RandomizedFO2003.Rotations

namespace RandomizedFO2003.SpectralCoordinates

open MeasureTheory

theorem measurable_direction {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ) :
    Measurable (fun u => direction K u r) := by
  have h := (continuousDiagonal K r).continuous.measurable
  exact h.norm.inv.smul h

end RandomizedFO2003.SpectralCoordinates

namespace RandomizedFO2003.Rotations

open MeasureTheory SpectralCoordinates

universe u

/-- An event determined entirely by the ordinary transcript: whenever its
authorization depth is at most `m`, every latent query has small readout. -/
def MarkedProgram.readoutEvent {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ) (m t : ℕ)
    {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) (c : ℝ) : Set (ActionHistory (BlockSpace K) (markedActionCount t) H) :=
  {p | markedDepth t (plan.authorizationTrace t p) 0 ≤ m →
    ∀ i, |inner (𝕜 := ℝ) (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
      (markedQueryTrace (BlockSpace K) t p i)| ≤ c * ‖markedQueryTrace (BlockSpace K) t p i‖}

theorem MarkedProgram.measurableSet_readoutEvent {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ) (m t : ℕ)
    {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) (hm : Measurable mark) (c : ℝ) :
    MeasurableSet (plan.readoutEvent K r m t mark c) := by
  have hd : Measurable (fun p => markedDepth t (plan.authorizationTrace t p) 0) :=
    (measurable_of_countable (fun a : Fin t → Bool => markedDepth t a 0)).comp
      (measurable_pi_lambda _ (fun i => plan.authorizationTrace_measurable t i))
  have hu : Measurable (fun p : ActionHistory (BlockSpace K) (markedActionCount t) H =>
      direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r) :=
    (measurable_direction K r).comp (hm.comp (ActionHistory.seed_measurable _))
  have hqueries : MeasurableSet {p : ActionHistory (BlockSpace K) (markedActionCount t) H |
      ∀ i, |inner (𝕜 := ℝ) (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
        (markedQueryTrace (BlockSpace K) t p i)| ≤ c * ‖markedQueryTrace (BlockSpace K) t p i‖} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (continuous_abs.measurable.comp (hu.inner (markedQueryTrace_measurable t i)))
      (measurable_const.mul (markedQueryTrace_measurable t i).norm)
  convert (measurableSet_le hd measurable_const).compl.union hqueries using 1
  ext p
  simp only [readoutEvent, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
  tauto

theorem MarkedProgram.simulation_mem_readoutEvent {J : ℕ} (K : Fin J → ℕ) (node r : Fin J → ℝ)
    (d t m : ℕ) {H Ω : Type u} [MeasurableSpace H] [MeasurableSpace Ω]
    (plan : MarkedProgram (BlockSpace K) t H) (mark : H → BlockSpace K) (hm : Measurable mark)
    (F : Ω → ExposureFrame (Coordinates (d + markedActionCount t)) (BlockSpace K)) (history : Ω → H)
    (c : ℝ) (p : AmbientPairHistory (BlockSpace K) (markedActionCount t) Ω)
    (hsupport : (F (AmbientPairHistory.seed (BlockSpace K) (markedActionCount t) p)).KnownSupport)
    (hknown : embeddingComplement (F (AmbientPairHistory.seed (BlockSpace K) (markedActionCount t) p)).latent = ⊥)
    (hgood : (plan.compile (continuousDiagonal K node) t mark hm).directAmbientGood
      d (markedActionCount t) F history p)
    (hgeometry : ∀ z ∈ shortKrylovSpace K
        (mark (history (AmbientPairHistory.seed (BlockSpace K) (markedActionCount t) p))) node m ⊔
          multiStartKrylovSpace K node (AmbientPairHistory.starts (BlockSpace K) (markedActionCount t) p),
      |inner (𝕜 := ℝ) (direction K (mark (history (AmbientPairHistory.seed (BlockSpace K) (markedActionCount t) p))) r) z| ≤
        c * ‖z‖) :
    (plan.compile (continuousDiagonal K node) t mark hm).directAmbientTranscript
      d (markedActionCount t) F history p ∈ plan.readoutEvent K r m t mark c := by
  let transcript := (plan.compile (continuousDiagonal K node) t mark hm).directAmbientTranscript
    d (markedActionCount t) F history p
  intro hdepth i
  have hv : markedQueryTrace (BlockSpace K) t transcript i ∈
      (plan.compile (continuousDiagonal K node) t mark hm).selectQueries (markedActionCount t) transcript := by
    rw [plan.selectQueries_eq t]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hspace := plan.selectedQueries_spectral K node d t mark hm F history p hsupport hknown hgood _ hv
  have hg := hgeometry _ ((sup_le_sup_right (shortKrylovSpace_mono K _ node hdepth) _) hspace)
  have hs := (plan.compile (continuousDiagonal K node) t mark hm).directAmbientTranscript_seed
    d (markedActionCount t) F history p
  simpa only [hs] using hg

end RandomizedFO2003.Rotations
