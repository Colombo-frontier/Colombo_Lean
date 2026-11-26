import RandomizedFO2003.MarkedPrefixSpectral
import RandomizedFO2003.SphereWeights

namespace RandomizedFO2003.Rotations

open MeasureTheory SpectralCoordinates

universe u

/-- This event controls each query when its own prefix depth is small,
regardless of the final depth or future authorization decisions. -/
def MarkedProgram.prefixReadoutEvent {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ) (m t : ℕ)
    {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) (c : ℝ) : Set (ActionHistory (BlockSpace K) (markedActionCount t) H) :=
  {p | ∀ i, markedQueryDepth t (plan.authorizationTrace t p) 0 i ≤ m →
    |inner (𝕜 := ℝ) (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
      (markedQueryTrace (BlockSpace K) t p i)| ≤ c * ‖markedQueryTrace (BlockSpace K) t p i‖}

theorem MarkedProgram.measurableSet_prefixReadoutEvent {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ) (m t : ℕ)
    {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) (hm : Measurable mark) (c : ℝ) :
    MeasurableSet (plan.prefixReadoutEvent K r m t mark c) := by
  have ha : Measurable (fun p => plan.authorizationTrace t p) :=
    measurable_pi_lambda _ (fun i => plan.authorizationTrace_measurable t i)
  have hu : Measurable (fun p : ActionHistory (BlockSpace K) (markedActionCount t) H =>
      direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r) :=
    (measurable_direction K r).comp (hm.comp (ActionHistory.seed_measurable _))
  unfold prefixReadoutEvent
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hd : Measurable (fun p => markedQueryDepth t (plan.authorizationTrace t p) 0 i) :=
    (measurable_of_countable (fun a : Fin t → Bool => markedQueryDepth t a 0 i)).comp ha
  have hq : MeasurableSet {p : ActionHistory (BlockSpace K) (markedActionCount t) H |
      |inner (𝕜 := ℝ) (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
        (markedQueryTrace (BlockSpace K) t p i)| ≤ c * ‖markedQueryTrace (BlockSpace K) t p i‖} :=
    measurableSet_le (continuous_abs.measurable.comp (hu.inner (markedQueryTrace_measurable t i)))
      (measurable_const.mul (markedQueryTrace_measurable t i).norm)
  convert (measurableSet_le hd measurable_const).compl.union hq using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
  tauto

/-- The initial mark's spectral weights, retained on the same history event
as the query barrier rather than assigned a separate multiplicity choice. -/
def historyWeightEvent {J : ℕ} (K : Fin J → ℕ) (w : Fin J → ℝ) (t : ℕ)
    {H : Type u} (mark : H → BlockSpace K) (δ : ℝ) :
    Set (ActionHistory (BlockSpace K) (markedActionCount t) H) :=
  {p | ∀ j, |SpectralCoordinates.weight K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) j -
    w j| ≤ δ * w j}

theorem measurableSet_historyWeightEvent {J : ℕ} (K : Fin J → ℕ) (w : Fin J → ℝ) (t : ℕ)
    {H : Type u} [MeasurableSpace H] (mark : H → BlockSpace K) (hm : Measurable mark) (δ : ℝ) :
    MeasurableSet (historyWeightEvent K w t mark δ) := by
  unfold historyWeightEvent
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (continuous_abs.measurable.comp
    (((Spherical.continuous_weight K j).measurable.comp (hm.comp (ActionHistory.seed_measurable _))).sub measurable_const))
    measurable_const

theorem MarkedProgram.simulation_mem_prefixReadoutEvent {J : ℕ} (K : Fin J → ℕ) (node r : Fin J → ℝ)
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
      d (markedActionCount t) F history p ∈ plan.prefixReadoutEvent K r m t mark c := by
  intro i hdepth
  have hspace := plan.query_prefix_spectral K node d t mark hm F history p hsupport hknown hgood i
  have hg := hgeometry _ ((sup_le_sup_right (shortKrylovSpace_mono K _ node hdepth) _) hspace)
  have hs := (plan.compile (continuousDiagonal K node) t mark hm).directAmbientTranscript_seed
    d (markedActionCount t) F history p
  simpa only [hs] using hg

end RandomizedFO2003.Rotations
