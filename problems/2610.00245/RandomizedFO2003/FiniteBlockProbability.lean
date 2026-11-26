import RandomizedFO2003.MultiStart
import Mathlib.MeasureTheory.Constructions.Pi

namespace RandomizedFO2003

open MeasureTheory
open scoped BigOperators ENNReal

theorem pi_coordinate_preserving {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (i : I) :
    MeasurePreserving (fun x : I → X => x i) (Measure.pi (fun _ => μ)) μ := by
  classical
  refine ⟨measurable_pi_apply i, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have heq : (fun x : I → X => x i) ⁻¹' s =
      Set.univ.pi (Function.update (fun _ : I => Set.univ) i s) := by
    ext x
    simp [Set.mem_pi, Function.update_apply, apply_ite]
  rw [heq, Measure.pi_pi]
  simp [Function.update_apply, apply_ite]

/-- Pull back one event per block under the actual finite product sphere law.
The events may share an arbitrary common independent parameter. -/
theorem finite_block_good_probability {I Ω X : Type*} [Fintype I]
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (σ : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure σ]
    (G : I → Set (Ω × X)) (hG : ∀ i, MeasurableSet (G i))
    (ε : ℝ)
    (hprob : ∀ i, 1 - ENNReal.ofReal ε ≤ (μ.prod σ) (G i)) :
    MeasurableSet {p : Ω × (I → X) | ∀ i, (p.1, p.2 i) ∈ G i} ∧
      1 - ENNReal.ofReal ((Fintype.card I : ℝ) * ε) ≤
        (μ.prod (Measure.pi (fun _ : I => σ))) {p | ∀ i, (p.1, p.2 i) ∈ G i} := by
  let ρ := μ.prod (Measure.pi (fun _ : I => σ))
  let F := fun i (p : Ω × (I → X)) => (p.1, p.2 i)
  have hF (i : I) : MeasurePreserving (F i) ρ (μ.prod σ) :=
    (MeasurePreserving.id μ).prod (pi_coordinate_preserving σ i)
  have hset : {p : Ω × (I → X) | ∀ i, (p.1, p.2 i) ∈ G i} = ⋂ i, F i ⁻¹' G i := by
    ext p
    simp [F]
  have hmeas : MeasurableSet {p : Ω × (I → X) | ∀ i, (p.1, p.2 i) ∈ G i} := by
    rw [hset]
    exact MeasurableSet.iInter (fun i => (hG i).preimage (hF i).measurable)
  refine ⟨hmeas, ?_⟩
  have hbad (i : I) : ρ (F i ⁻¹' (G i)ᶜ) ≤ ENNReal.ofReal ε := by
    rw [(hF i).measure_preimage (hG i).compl.nullMeasurableSet, prob_compl_eq_one_sub (hG i)]
    exact tsub_le_iff_tsub_le.mp (hprob i)
  have hb : ρ {p : Ω × (I → X) | ∀ i, (p.1, p.2 i) ∈ G i}ᶜ ≤
      ENNReal.ofReal ((Fintype.card I : ℝ) * ε) := by
    rw [hset, Set.compl_iInter]
    simp only [← Set.preimage_compl]
    calc
      _ ≤ ∑ i, ρ (F i ⁻¹' (G i)ᶜ) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : I, ENNReal.ofReal ε := Finset.sum_le_sum (fun i _ => hbad i)
      _ = _ := by simp [ENNReal.ofReal_mul, nsmul_eq_mul]
  have hc := prob_compl_eq_one_sub (μ := ρ) hmeas.compl
  rw [compl_compl] at hc
  change 1 - ENNReal.ofReal ((Fintype.card I : ℝ) * ε) ≤ ρ _
  rw [hc]
  exact tsub_le_tsub_left hb 1

end RandomizedFO2003

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical
open scoped BigOperators ENNReal

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- The simultaneous high-multiplicity event for any prescribed finite number
of blocks. Starts can be correlated across blocks; the whole start parameter
is independent of the sphere-vector family. -/
theorem simultaneous_independent_high_multiplicity (hγ : 0 < γ)
    (δ η ζ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hζ : 0 < ζ) (N T Rmin Nmin : ℕ) :
    ∃ K : Fin D.size → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (g : Ω → Fin N → Fin T → BlockSpace K),
        (∀ i t, Measurable (fun ω => g ω i t)) →
        ∃ G : Set (Ω × (Fin N → BlockSpace K)), MeasurableSet G ∧
          1 - ENNReal.ofReal ζ ≤
            (μ.prod (Measure.pi (fun _ : Fin N => sphereLaw (BlockSpace K)))) G ∧
          ∀ p ∈ G, ∀ i,
            (∀ j, |SpectralCoordinates.weight K (p.2 i) j - D.weight j| ≤ δ * D.weight j) ∧
            (∀ j, ‖(startsSubspace K (g p.1 i) j).orthogonalProjection
              (blockDirection K j (p.2 i))‖ ≤ η) ∧
            ‖direction K (p.2 i) D.residual‖ = 1 ∧
            ∀ z ∈ shortKrylovSpace K (p.2 i) D.node m ⊔ multiStartKrylovSpace K D.node (g p.1 i),
              |inner (𝕜 := ℝ) (direction K (p.2 i) D.residual) z| ≤ 4 * (δ + η) * ‖z‖ := by
  have hden : (0 : ℝ) < N + 1 := by positivity
  let ε := ζ / ((N : ℝ) + 1)
  have hε : 0 < ε := div_pos hζ hden
  obtain ⟨K, hK, hN, htotal, hunit, hgood⟩ :=
    D.independent_high_multiplicity hγ δ η ε hδ hδhalf hη hηhalf hε T Rmin Nmin
  refine ⟨K, hK, hN, htotal, hunit, ?_⟩
  intro Ω _ μ _ g hg
  have hall := fun i => hgood Ω μ (fun ω => g ω i) (hg i)
  choose G hG hprob hprops using hall
  obtain ⟨hF, hFprob⟩ := finite_block_good_probability μ (sphereLaw (BlockSpace K)) G hG ε hprob
  have hbudget : (N : ℝ) * ε ≤ ζ := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hζ]
  refine ⟨{p | ∀ i, (p.1, p.2 i) ∈ G i}, hF, ?_, ?_⟩
  · apply (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hbudget) 1).trans
    simpa only [Fintype.card_fin] using hFprob
  · intro p hp i
    exact hprops i (p.1, p.2 i) (hp i)

end RandomizedFO2003.FiniteSpectralDesign
