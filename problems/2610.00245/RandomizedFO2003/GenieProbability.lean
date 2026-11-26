import RandomizedFO2003.GenieLawTransfer

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations Spherical
open scoped BigOperators ENNReal

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- One multiplicity choice controls the sum of the actual block failure
probabilities. It is made before the seed space, seed law, and algorithm. -/
theorem choose_genie_multiplicities (hγ : 0 < γ) {h ζ : ℝ} (hh : 0 < h) (hζ : 0 < ζ)
    (N T Rmin Nmin : ℕ) :
    ∃ K : Fin S.size → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧
      markedActionCount (T + 1) ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed),
        ∑ i : Fin (N + 1), ((S.cascadeParameterLaw K N).prod ν)
          (S.censoredGenieGoodEvent K N h A T i)ᶜ ≤ ENNReal.ofReal ζ := by
  let δ : ℝ := ζ / (N + 1)
  have hden : (0 : ℝ) < N + 1 := by positivity
  have hδ : 0 < δ := div_pos hζ hden
  have hB : 0 < radiusCoefficient * h / γ := div_pos (mul_pos radiusCoefficient_pos hh) hγ
  have hα : 0 < h / (64 * γ) := div_pos hh (by positivity)
  obtain ⟨K, hK, hN, hdim, htotal, hunit, hprob⟩ :=
    S.marked_haar_prefix_gate_probability hγ hB hα hδ (T + 1) Rmin Nmin
  refine ⟨K, hK, hN, hdim, htotal, hunit, ?_⟩
  intro Seed _ ν _ A
  have hb (i : Fin (N + 1)) : ((S.cascadeParameterLaw K N).prod ν)
      (S.censoredGenieGoodEvent K N h A T i)ᶜ ≤ ENNReal.ofReal δ := by
    rw [prob_compl_eq_one_sub (S.measurableSet_censoredGenieGoodEvent K N h A T i)]
    apply tsub_le_iff_tsub_le.mp
    rw [S.censoredGenieGoodEvent_probability_eq K N h ν A T i]
    exact hprob (Coefficients N (BlockSpace K) × Seed) ((S.publicCascadeLaw K N h i).prod ν)
      (S.censoredGenieProgram K N h A T i)
  have hbudget : ((N + 1 : ℕ) : ℝ) * δ = ζ := by
    dsimp only [δ]
    push_cast
    exact mul_div_cancel₀ ζ hden.ne'
  calc
    _ ≤ ∑ _i : Fin (N + 1), ENNReal.ofReal δ := Finset.sum_le_sum (fun i _ => hb i)
    _ = ENNReal.ofReal (((N + 1 : ℕ) : ℝ) * δ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_natCast]
    _ = _ := by rw [hbudget]

/-- Unit sphere support lifts to the common original sample and private seed. -/
theorem cascade_seed_unit (K : Fin S.size → ℕ) (N : ℕ)
    (hunit : ∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1)
    {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed) [SFinite ν] :
    ∀ᵐ p ∂(S.cascadeParameterLaw K N).prod ν, ∀ i, ‖p.1.1 i‖ = 1 := by
  have hp : ∀ᵐ u ∂Measure.pi (fun _ : Fin (N + 1) => sphereLaw (BlockSpace K)),
      ∀ i, ‖u i‖ = 1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (N + 1) => sphereLaw (BlockSpace K)) (i := i)).eventually hunit
  have hm : MeasurableSet {p : Sample K N | ∀ i, ‖p.1 i‖ = 1} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_eq_fun (((measurable_pi_apply i).comp measurable_fst).norm) measurable_const
  have hbase : ∀ᵐ p ∂S.cascadeParameterLaw K N, ∀ i, ‖p.1 i‖ = 1 := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    exact hp.mono (fun _ hu => Filter.Eventually.of_forall (fun _ => hu))
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage measurable_fst)).mpr
  exact hbase.mono (fun _ hu => Filter.Eventually.of_forall (fun _ => hu))

/-- Bad spectral data is contained almost everywhere in the union of the
same block failures used for the terminal obstruction. -/
theorem spectral_bad_probability_le_genie_bad (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (hunit : ∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1)
    {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) :
    Measure.pi (fun _ : Fin (N + 1) => sphereLaw (BlockSpace K)) (S.cascadeGoodEvent K N)ᶜ ≤
      ∑ i : Fin (N + 1), ((S.cascadeParameterLaw K N).prod ν)
        (S.censoredGenieGoodEvent K N h A T i)ᶜ := by
  have hsub : (((S.cascadeGoodEvent K N)ᶜ ×ˢ Set.univ) ×ˢ Set.univ) ≤ᵐ[(S.cascadeParameterLaw K N).prod ν]
      ⋃ i : Fin (N + 1), (S.censoredGenieGoodEvent K N h A T i)ᶜ := by
    filter_upwards [S.cascade_seed_unit K N hunit ν] with p hp
    intro hbad
    by_contra hn
    change p ∉ ⋃ i : Fin (N + 1), (S.censoredGenieGoodEvent K N h A T i)ᶜ at hn
    simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hn
    exact hbad.1.1 (S.cascadeGoodEvent_of_genie_events K N h A T hp hn)
  calc
    _ = ((S.cascadeParameterLaw K N).prod ν)
        (((S.cascadeGoodEvent K N)ᶜ ×ˢ Set.univ) ×ˢ Set.univ) := by
      simp only [cascadeParameterLaw, Measure.prod_prod, measure_univ, mul_one]
    _ ≤ ((S.cascadeParameterLaw K N).prod ν)
        (⋃ i : Fin (N + 1), (S.censoredGenieGoodEvent K N h A T i)ᶜ) := measure_mono_ae hsub
    _ ≤ _ := measure_iUnion_fintype_le _ _

end RandomizedFO2003.FiniteSpectralDesign
