import RandomizedFO2003.SpectralStationarity
import RandomizedFO2003.FiniteBlockProbability
import RandomizedFO2003.SphericalDesign
import RandomizedFO2003.HaarSphere

namespace RandomizedFO2003

open MeasureTheory
open scoped ENNReal

/-- The finite-block union bound specialized to a family with no external
parameter. -/
theorem finite_pi_good_probability {I X : Type*} [Fintype I] [MeasurableSpace X]
    (σ : Measure X) [IsProbabilityMeasure σ]
    (G : I → Set X) (hG : ∀ i, MeasurableSet (G i)) (ε : ℝ)
    (hprob : ∀ i, 1 - ENNReal.ofReal ε ≤ σ (G i)) :
    MeasurableSet {x : I → X | ∀ i, x i ∈ G i} ∧
      1 - ENNReal.ofReal ((Fintype.card I : ℝ) * ε) ≤
        Measure.pi (fun _ : I => σ) {x | ∀ i, x i ∈ G i} := by
  have h := finite_block_good_probability (Measure.dirac ()) σ
    (fun i => Set.univ ×ˢ G i) (fun i => MeasurableSet.univ.prod (hG i)) ε
    (fun i => by simpa only [Measure.prod_prod, measure_univ, one_mul] using hprob i)
  have heq : {p : Unit × (I → X) | ∀ i, (p.1, p.2 i) ∈ Set.univ ×ˢ G i} =
      Set.univ ×ˢ {x : I → X | ∀ i, x i ∈ G i} := by ext p; simp
  refine ⟨?_, ?_⟩
  · simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, true_and] using
      h.1.preimage (measurable_const.prodMk measurable_id : Measurable (fun x : I → X => ((), x)))
  · rw [heq, Measure.prod_prod, measure_univ, one_mul] at h
    exact h.2

end RandomizedFO2003

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical Cascade Rotations
open scoped ENNReal BigOperators

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- A closed, explicitly measurable event on the independent spectral
directions. Its definition contains no stationarity or oracle conclusions. -/
def cascadeGoodEvent (K : Fin S.size → ℕ) (N : ℕ) : Set (Fin (N + 1) → BlockSpace K) :=
  {u | ∀ i, ‖u i‖ = 1 ∧ ∀ j,
    |SpectralCoordinates.weight K (u i) j - S.weight j| ≤ (1 / 32) * S.weight j}

theorem measurable_cascadeGoodEvent (K : Fin S.size → ℕ) (N : ℕ) :
    MeasurableSet (S.cascadeGoodEvent K N) := by
  unfold cascadeGoodEvent
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun (measurable_pi_apply i).norm measurable_const
  · change MeasurableSet {x : Fin (N + 1) → BlockSpace K | ∀ j,
      |SpectralCoordinates.weight K (x i) j - S.weight j| ≤ (1 / 32) * S.weight j}
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le
      ((((continuous_weight K j).comp (continuous_apply i)).sub continuous_const).abs.measurable)
      measurable_const

/-- Multiplicities are fixed before any rotations, algorithm, or candidate
point. Every block is a unit vector with controlled spectral weights on the
same event, whose failure probability is at most the prescribed budget. -/
theorem choose_cascade_good_multiplicities (ζ : ℝ) (hζ : 0 < ζ) (N Rmin Nmin : ℕ) :
    ∃ K : Fin S.size → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      1 - ENNReal.ofReal ζ ≤
        Measure.pi (fun _ : Fin (N + 1) => sphereLaw (BlockSpace K)) (S.cascadeGoodEvent K N) := by
  let ε := ζ / (N + 1)
  have hden : (0 : ℝ) < N + 1 := by positivity
  have hε : 0 < ε := div_pos hζ hden
  obtain ⟨K, hK, hN, htotal, hunit, _hbad, hweight⟩ :=
    S.choose_concentrated_multiplicities (1 / 32) ε (by norm_num) (by norm_num) hε Rmin Nmin
  let G : Set (BlockSpace K) := {u | ‖u‖ = 1 ∧ ∀ j,
    |SpectralCoordinates.weight K u j - S.weight j| ≤ (1 / 32) * S.weight j}
  have hG : MeasurableSet G := by
    change MeasurableSet ({u : BlockSpace K | ‖u‖ = 1} ∩ {u | ∀ j,
      |SpectralCoordinates.weight K u j - S.weight j| ≤ (1 / 32) * S.weight j})
    apply MeasurableSet.inter (measurableSet_eq_fun measurable_norm measurable_const)
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (((continuous_weight K j).sub continuous_const).abs.measurable) measurable_const
  have hGprob : 1 - ENNReal.ofReal ε ≤ sphereLaw (BlockSpace K) G := by
    have heq : sphereLaw (BlockSpace K) G = sphereLaw (BlockSpace K) {u | ∀ j,
        |SpectralCoordinates.weight K u j - S.weight j| ≤ (1 / 32) * S.weight j} := by
      apply measure_congr
      filter_upwards [hunit] with u hu
      change (‖u‖ = 1 ∧ _) = _
      simp only [hu, true_and]
      rfl
    rw [heq]
    exact hweight
  have hall := finite_pi_good_probability (sphereLaw (BlockSpace K)) (fun _ : Fin (N + 1) => G)
    (fun _ => hG) ε (fun _ => hGprob)
  refine ⟨K, hK, hN, htotal, ?_⟩
  have hbudget : ((N + 1 : ℕ) : ℝ) * ε = ζ := by
    dsimp [ε]
    push_cast
    exact mul_div_cancel₀ ζ hden.ne'
  simpa only [Fintype.card_fin, hbudget] using hall.2

/-- The actual joint law of independent sphere directions and independent
Haar rotations. This is a law on the parameters of the constructed cascade. -/
noncomputable def cascadeParameterLaw (K : Fin S.size → ℕ) (N : ℕ) :
    Measure ((Fin (N + 1) → BlockSpace K) × (Fin (N + 1) → Rotation (BlockSpace K))) :=
  (Measure.pi (fun _ : Fin (N + 1) => sphereLaw (BlockSpace K))).prod
    (Measure.pi (fun _ : Fin (N + 1) => haarLaw (BlockSpace K)))

instance cascadeParameterLaw_probability (K : Fin S.size → ℕ) (N : ℕ) :
    IsProbabilityMeasure (S.cascadeParameterLaw K N) := by
  unfold cascadeParameterLaw
  infer_instance

theorem cascadeParameterLaw_good (K : Fin S.size → ℕ) (N : ℕ) :
    S.cascadeParameterLaw K N (S.cascadeGoodEvent K N ×ˢ Set.univ) =
      Measure.pi (fun _ : Fin (N + 1) => sphereLaw (BlockSpace K)) (S.cascadeGoodEvent K N) := by
  simp only [cascadeParameterLaw, Measure.prod_prod, measure_univ, mul_one]

/-- The same spectral event works for every rotation and every candidate
point, so no union bound over either is required. -/
theorem cascadeGoodEvent_stationarity (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    {u : Fin (N + 1) → BlockSpace K} (hu : u ∈ S.cascadeGoodEvent K N)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (hH : 512 * ε ≤ h)
    (z : BlockProduct (N + 1) (BlockSpace K))
    (hz : ‖gradient (S.cascade K N U u h).energy z‖ ≤ ε) :
    let d := S.cascade K N U u h
    (∀ i, ‖z i‖ ≤ d.B) ∧
    (∀ i, |forcingReadout (d.b i) d.D (z i)| ≤ d.K) ∧
    (∀ i, d.gate i (z i) = 1) ∧
    ‖d.A (Fin.last N) (z (Fin.last N)) - d.b (Fin.last N)‖ ≤ ε :=
  S.cascade_stationarity hγ K N U u hh hε hH (fun i => (hu i).1) (fun i => (hu i).2) z hz

end RandomizedFO2003.FiniteSpectralDesign
