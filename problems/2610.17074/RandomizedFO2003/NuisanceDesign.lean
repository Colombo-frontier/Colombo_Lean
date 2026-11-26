import RandomizedFO2003.NuisanceProbability
import RandomizedFO2003.SphericalDesign

namespace RandomizedFO2003.SpectralCoordinates

open MeasureTheory Spherical
open scoped BigOperators ENNReal

variable {J : ℕ}

def blockGoodEvent {Ω : Type*} (K : Fin J → ℕ) (ν : Fin J → ℝ)
    (W : Ω → (j : Fin J) → Submodule ℝ (ComponentSpace K j)) (δ η : ℝ) :
    Set (Ω × BlockSpace K) := {p |
      (∀ j, |weight K p.2 j - ν j| ≤ δ * ν j) ∧
      (∀ j, ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖ < η)}

theorem measurableSet_blockGoodEvent {Ω : Type*} [MeasurableSpace Ω]
    (K : Fin J → ℕ) (ν : Fin J → ℝ)
    (W : Ω → (j : Fin J) → Submodule ℝ (ComponentSpace K j))
    (hW : ∀ j, Measurable (fun p : Ω × BlockSpace K =>
      ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖)) (δ η : ℝ) :
    MeasurableSet (blockGoodEvent K ν W δ η) := by
  apply MeasurableSet.inter
  · have hs : MeasurableSet (⋂ j, {p : Ω × BlockSpace K |
        |weight K p.2 j - ν j| ≤ δ * ν j}) :=
      MeasurableSet.iInter (fun j => measurableSet_le
        (((continuous_weight K j).sub continuous_const).abs.measurable.comp measurable_snd)
        measurable_const)
    convert hs using 1
    ext p
    simp
    rfl
  · have hs : MeasurableSet (⋂ j, {p : Ω × BlockSpace K |
        ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖ < η}) :=
      MeasurableSet.iInter (fun j => measurableSet_lt (hW j) measurable_const)
    convert hs using 1
    ext p
    simp
    rfl

theorem blockGoodEvent_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Fin J → ℕ) (hK : ∀ j, 0 < K j) (ν : Fin J → ℝ)
    (W : Ω → (j : Fin J) → Submodule ℝ (ComponentSpace K j))
    (hW : ∀ j, Measurable (fun p : Ω × BlockSpace K =>
      ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖))
    (T : ℕ) (hdim : ∀ ω j, Module.finrank ℝ (W ω j) ≤ T)
    (δ η ζ : ℝ) (hη : 0 < η) (hζ : 0 ≤ ζ)
    (hweight : sphereLaw (BlockSpace K) {u | ∃ j, δ * ν j < |weight K u j - ν j|} ≤
      ENNReal.ofReal (ζ / 2))
    (hnuisance : (∑ j, ENNReal.ofReal ((T : ℝ) / ((K j : ℝ) * η ^ 2))) ≤
      ENNReal.ofReal (ζ / 2)) :
    1 - ENNReal.ofReal ζ ≤ (μ.prod (sphereLaw (BlockSpace K))) (blockGoodEvent K ν W δ η) := by
  let B : Set (BlockSpace K) := {u | ∃ j, δ * ν j < |weight K u j - ν j|}
  let N : Set (Ω × BlockSpace K) := {p | ∃ j,
    η ≤ ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖}
  have hB : (μ.prod (sphereLaw (BlockSpace K))) (Set.univ ×ˢ B) ≤ ENNReal.ofReal (ζ / 2) := by
    simpa only [Measure.prod_prod, measure_univ, one_mul] using hweight
  have hN : (μ.prod (sphereLaw (BlockSpace K))) N ≤ ENNReal.ofReal (ζ / 2) :=
    (independent_nuisance_tail μ K hK W hW T hdim η hη).trans hnuisance
  have hcompl : (blockGoodEvent K ν W δ η)ᶜ = (Set.univ ×ˢ B) ∪ N := by
    ext p
    simp only [blockGoodEvent, B, N, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_union, Set.mem_prod, Set.mem_univ, true_and, not_and_or, not_forall, not_le, not_lt]
  have hb : (μ.prod (sphereLaw (BlockSpace K))) (blockGoodEvent K ν W δ η)ᶜ ≤
      ENNReal.ofReal ζ := by
    rw [hcompl]
    calc
      _ ≤ (μ.prod (sphereLaw (BlockSpace K))) (Set.univ ×ˢ B) +
        (μ.prod (sphereLaw (BlockSpace K))) N := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) := add_le_add hB hN
      _ = ENNReal.ofReal ζ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hc := prob_compl_eq_one_sub (μ := μ.prod (sphereLaw (BlockSpace K)))
    (measurableSet_blockGoodEvent K ν W hW δ η).compl
  rw [compl_compl] at hc
  rw [hc]
  exact tsub_le_tsub_left hb 1

/-- Multiplicities are chosen before the independent parameter law and nuisance
family. A polynomial tail suffices here; no logarithmic multiplicity claim is made. -/
theorem exists_good_block_geometry (ν : Fin J → ℝ)
    (hν : ∀ j, 0 < ν j) (hsum : ∑ j, ν j = 1)
    (δ η ζ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) (hζ : 0 < ζ)
    (T Rmin Nmin : ℕ) :
    ∃ K : Fin J → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → (j : Fin J) → Submodule ℝ (ComponentSpace K j)),
        (∀ j, Measurable (fun p : Ω × BlockSpace K =>
          ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖)) →
        (∀ ω j, Module.finrank ℝ (W ω j) ≤ T) →
        1 - ENNReal.ofReal ζ ≤
          (μ.prod (sphereLaw (BlockSpace K))) (blockGoodEvent K ν W δ η) := by
  obtain ⟨R, hR⟩ := exists_nat_gt (max 1 (2 * (J : ℝ) * T / (η ^ 2 * ζ)))
  have hRreal : (0 : ℝ) < R := by
    have ht := (le_max_left (1 : ℝ) (2 * (J : ℝ) * T / (η ^ 2 * ζ))).trans_lt hR
    linarith
  have hRnat : 0 < R := by exact_mod_cast hRreal
  have hlarge : 2 * (J : ℝ) * T ≤ (R : ℝ) * (η ^ 2 * ζ) := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hη) hζ)).mp
    exact ((le_max_right _ _).trans_lt hR).le
  have hbound : (J : ℝ) * T / ((R : ℝ) * η ^ 2) ≤ ζ / 2 := by
    apply (div_le_iff₀ (mul_pos hRreal (sq_pos_of_pos hη))).mpr
    nlinarith only [hlarge]
  obtain ⟨K, hK, hN, htotal, hunit, hweight, _⟩ :=
    exists_good_spherical_weights ν hν hsum δ (ζ / 2) hδ hδone (by positivity)
      (max R Rmin) Nmin
  refine ⟨K, (fun j => ⟨(hK j).1, (Nat.le_max_right R Rmin).trans (hK j).2⟩),
    hN, htotal, hunit, ?_⟩
  intro Ω _ μ _ W hW hdim
  apply blockGoodEvent_probability μ K (fun j => (hK j).1) ν W hW T hdim δ η ζ hη hζ.le hweight
  exact (nuisance_tail_uniform_multiplicity K R T hRnat
    (fun j => (Nat.le_max_left R Rmin).trans (hK j).2) η hη).trans
    (ENNReal.ofReal_le_ofReal hbound)

end RandomizedFO2003.SpectralCoordinates
