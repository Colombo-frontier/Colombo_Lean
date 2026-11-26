import MatchingBounds1005.OracleMeasurability
import MatchingBounds1005.SmoothClass
import Mathlib.Probability.ConditionalProbability

/-! Conditioning the instance law while keeping the function family
pointwise in the exact manuscript class on every sample. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace MatchingBounds1005.Model

theorem zero_inFunctionClass (p d : ℕ) : InFunctionClass p (fun _ : Space d => (0 : ℝ)) := by
  apply inFunctionClass_of_operator_bounds contDiff_const
  · intro x; norm_num
  · intro q _ _ x
    rw [iteratedFDeriv_const_of_ne (by omega : q + 1 ≠ 0)]
    simp

def goodFamily {Ω : Type*} {d : ℕ} (F : Ω → Space d → ℝ) (G : Set Ω) :
    Ω → Space d → ℝ := by
  classical
  exact fun sample => if sample ∈ G then F sample else fun _ => 0

theorem goodFamily_eq {Ω : Type*} {d : ℕ} (F : Ω → Space d → ℝ) (G : Set Ω)
    {sample : Ω} (hsample : sample ∈ G) : goodFamily F G sample = F sample := if_pos hsample

theorem goodFamily_class {Ω : Type*} {d p : ℕ} (F : Ω → Space d → ℝ) (G : Set Ω)
    (hclass : ∀ sample ∈ G, InFunctionClass p (F sample)) (sample : Ω) :
    InFunctionClass p (goodFamily F G sample) := by
  classical
  by_cases hsample : sample ∈ G
  · rw [goodFamily_eq F G hsample]
    exact hclass sample hsample
  · simpa only [goodFamily, if_neg hsample] using zero_inFunctionClass p d

theorem goodFamily_oracle_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (F : Ω → Space d → ℝ) (G : Set Ω) (hG : MeasurableSet G)
    (hF : Measurable (fun z : Ω × Space d => oracle (F z.1) z.2)) :
    Measurable (fun z : Ω × Space d => oracle (goodFamily F G z.1) z.2) := by
  classical
  have he : (fun z : Ω × Space d => oracle (goodFamily F G z.1) z.2) =
      fun z => if z.1 ∈ G then oracle (F z.1) z.2 else (0 : Response d) := by
    funext z
    by_cases hz : z.1 ∈ G
    · simp [goodFamily, hz]
    · simp [goodFamily, hz, oracle, gradient]
  rw [he]
  exact hF.ite (hG.preimage measurable_fst) measurable_const

theorem cond_prod_apply {Ω Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) (ν : Measure Seed) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (G : Set Ω) (S : Set (Ω × Seed)) (hS : MeasurableSet S) :
    ((ProbabilityTheory.cond μ G).prod ν) S = (μ G)⁻¹ * (μ.prod ν) (S ∩ (G ×ˢ Set.univ)) := by
  rw [Measure.prod_apply hS]
  rw [ProbabilityTheory.cond, lintegral_smul_measure]
  rw [← Measure.prod_apply hS, Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply hS]
  rfl

theorem cond_prod_real {Ω Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) (ν : Measure Seed) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (G : Set Ω) (S : Set (Ω × Seed)) (hS : MeasurableSet S) :
    ((ProbabilityTheory.cond μ G).prod ν).real S = (μ.prod ν).real (S ∩ (G ×ˢ Set.univ)) / μ.real G := by
  unfold Measure.real
  rw [cond_prod_apply μ ν G S hS, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- Actual normalized restriction plus a zero function off the good event.
The remaining premise is a genuine all-policy probability bound under the
unconditioned instance-and-seed law, not a hard-distribution assumption. -/
theorem hardDistribution_of_conditioning {Ω : Type} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {p d T : ℕ} (ε : ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Space d → ℝ)
    (G : Set Ω) (hG : MeasurableSet G) (hmass : μ G ≠ 0)
    (hF : Measurable (fun z : Ω × Space d => oracle (F z.1) z.2))
    (hclass : ∀ sample ∈ G, InFunctionClass p (F sample))
    (hbound : ∀ (Seed : Type) [MeasurableSpace Seed] [StandardBorelSpace Seed]
      (ν : Measure Seed) [IsProbabilityMeasure ν] (A : Algorithm d Seed),
      (μ.prod ν).real ({z : Ω × Seed | z.2 ∈ Success A (F z.1) ε T} ∩
        (G ×ˢ Set.univ)) / μ.real G ≤ 1 / 3) :
    HardDistribution p d T ε := by
  letI : IsProbabilityMeasure (ProbabilityTheory.cond μ G) := cond_isProbabilityMeasure hmass
  let F' := goodFamily F G
  have hf' := goodFamily_oracle_measurable F G hG hF
  refine ⟨Ω, inferInstance, inferInstance, ProbabilityTheory.cond μ G, inferInstance, F', hf',
    goodFamily_class F G hclass, ?_⟩
  intro Seed _ _ ν _ A
  have hs := success_measurable F' hf' A ε T
  refine ⟨hs, ?_⟩
  have he : {z : Ω × Seed | z.2 ∈ Success A (F' z.1) ε T} ∩ (G ×ˢ Set.univ) =
      {z : Ω × Seed | z.2 ∈ Success A (F z.1) ε T} ∩ (G ×ˢ Set.univ) := by
    ext z
    by_cases hz : z.1 ∈ G
    · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, F', goodFamily_eq F G hz]
    · simp [Set.mem_inter_iff, Set.mem_prod, hz]
  have hb : ((ProbabilityTheory.cond μ G).prod ν).real {z : Ω × Seed | z.2 ∈ Success A (F' z.1) ε T} ≤ 1 / 3 := by
    rw [cond_prod_real μ ν G _ hs, he]
    exact hbound Seed ν A
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num : (1 / 3 : ℝ≥0∞) ≠ ∞)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hb

end MatchingBounds1005.Model

