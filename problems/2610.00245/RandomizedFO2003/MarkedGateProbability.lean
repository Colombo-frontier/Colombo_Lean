import RandomizedFO2003.MarkedHaarProbability
import RandomizedFO2003.RadialGate

namespace RandomizedFO2003.Rotations

open MeasureTheory SpectralCoordinates Primitives

universe u

/-- The actual radial readouts stay in the gate's flat region whenever the
authorization depth in this transcript is within the spectral design budget. -/
def MarkedProgram.flatReadoutEvent {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ) (m t : ℕ)
    {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) (B α : ℝ) : Set (ActionHistory (BlockSpace K) (markedActionCount t) H) :=
  {p | markedDepth t (plan.authorizationTrace t p) 0 ≤ m → ∀ i,
    |radialReadout (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
      B α (markedQueryTrace (BlockSpace K) t p i)| ≤ 1 / 4}

theorem MarkedProgram.measurableSet_flatReadoutEvent {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ) (m t : ℕ)
    {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) (hm : Measurable mark) (B α : ℝ) :
    MeasurableSet (plan.flatReadoutEvent K r m t mark B α) := by
  have hd : Measurable (fun p => markedDepth t (plan.authorizationTrace t p) 0) :=
    (measurable_of_countable (fun a : Fin t → Bool => markedDepth t a 0)).comp
      (measurable_pi_lambda _ (fun i => plan.authorizationTrace_measurable t i))
  have hu : Measurable (fun p : ActionHistory (BlockSpace K) (markedActionCount t) H =>
      direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r) :=
    (measurable_direction K r).comp (hm.comp (ActionHistory.seed_measurable _))
  have hqueries : MeasurableSet {p : ActionHistory (BlockSpace K) (markedActionCount t) H |
      ∀ i, |radialReadout
        (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
        B α (markedQueryTrace (BlockSpace K) t p i)| ≤ 1 / 4} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    apply continuous_abs.measurable.comp
    exact (hu.inner (((radialSquash_contDiff B 0).continuous.measurable).comp
      (markedQueryTrace_measurable t i))).div_const α
  convert (measurableSet_le hd measurable_const).compl.union hqueries using 1
  ext p
  simp only [flatReadoutEvent, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
  tauto

theorem MarkedProgram.readoutEvent_subset_flatReadoutEvent {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ)
    (m t : ℕ) {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) {B α c : ℝ} (hB : 0 < B) (hα : 0 < α) (hc : 0 ≤ c)
    (hmargin : c * (2 * B) ≤ α / 4) :
    plan.readoutEvent K r m t mark c ⊆ plan.flatReadoutEvent K r m t mark B α := by
  intro p hp hdepth i
  exact radialReadout_small hB hα hc hmargin _ _ (hp hdepth i)

/-- The probability event guarantees both a zero gate value and vanishing
derivatives of every order at each recorded query. -/
theorem MarkedProgram.flatReadoutEvent_vanishing {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ)
    (m t : ℕ) {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) (B α : ℝ)
    {p : ActionHistory (BlockSpace K) (markedActionCount t) H}
    (hp : p ∈ plan.flatReadoutEvent K r m t mark B α)
    (hdepth : markedDepth t (plan.authorizationTrace t p) 0 ≤ m) (i : Fin t) :
    let a := direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r
    let x := markedQueryTrace (BlockSpace K) t p i
    radialGate a B α x = 0 ∧ ∀ n : ℕ, iteratedFDeriv ℝ n (radialGate a B α) x = 0 := by
  exact ⟨radialGate_zero _ B α (hp hdepth i), fun n => radialGate_iteratedFDeriv_zero _ B α (hp hdepth i) n⟩

end RandomizedFO2003.Rotations

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical Rotations Primitives
open scoped BigOperators ENNReal

universe u

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- An actual smooth radial gate barrier for every single-block marked
strategy. Multiplicities precede the arbitrary seed space and algorithm.
No correlation or gate-margin assumption remains: their accuracy is chosen
from the given positive radius and gate scale. -/
theorem marked_haar_gate_probability (hγ : 0 < γ) {B α ζ : ℝ}
    (hB : 0 < B) (hα : 0 < α) (hζ : 0 < ζ) (t Rmin Nmin : ℕ) :
    ∃ K : Fin D.size → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ markedActionCount t ≤ ∑ j, K j ∧
      0 < ∑ j, K j ∧ (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (plan : MarkedProgram (BlockSpace K) t (BlockSpace K × Ω)),
        1 - ENNReal.ofReal ζ ≤
          (((sphereLaw (BlockSpace K)).prod μ).prod (haarLaw (BlockSpace K))).map
            (fun p => (plan.compile (continuousDiagonal K D.node) t Prod.fst measurable_fst).run
              (markedActionCount t) (p.2 : BlockSpace K →L[ℝ] BlockSpace K) p.1)
            (plan.flatReadoutEvent K D.residual m t Prod.fst B α) := by
  let δ : ℝ := min (1 / 4) (α / (64 * B))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hα (by positivity))
  have hδhalf : δ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hmargin : (4 * (δ + δ)) * (2 * B) ≤ α / 4 := by
    have hh : δ * (64 * B) ≤ α := (le_div_iff₀ (by positivity : 0 < 64 * B)).mp (min_le_right _ _)
    nlinarith
  obtain ⟨K, hK, hN, hdim, htotal, hunit, hprob⟩ :=
    D.marked_haar_readout_probability hγ δ δ ζ hδ hδhalf hδ hδhalf hζ t Rmin Nmin
  refine ⟨K, hK, hN, hdim, htotal, hunit, ?_⟩
  intro Ω _ μ _ plan
  exact (hprob Ω μ plan).trans (measure_mono
    (plan.readoutEvent_subset_flatReadoutEvent K D.residual m t Prod.fst hB hα
      (by positivity) hmargin))

end RandomizedFO2003.FiniteSpectralDesign
