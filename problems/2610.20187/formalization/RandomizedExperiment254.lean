import HardExperiment254
import HardIntegrability254
import FiniteDerandomization254

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Paper254

def jointWeights {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ProbabilityWeights ι) (q : ι → ProbabilityWeights κ) : ProbabilityWeights (ι × κ) where
  weight z := p.weight z.1*(q z.1).weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) ((q z.1).nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ProbabilityWeights.total, mul_one]

theorem joint_expectation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ProbabilityWeights ι) (q : ι → ProbabilityWeights κ) (F : ι × κ → ℝ) :
    finiteExpectation (jointWeights p q) F =
      finiteExpectation p (fun i => finiteExpectation (q i) (fun k => F (i,k))) := by
  unfold finiteExpectation jointWeights
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]

theorem randomized_hard_experiment_lower {κ : Type*} [Fintype κ] [DecidableEq κ] {d T : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin T → κ) (coordinate : Fin T → Fin d)
    (A : Ω → OnlineLearner (ballDomain d) T) (hA : SeedMeasurable A)
    (u : (κ → Bool) → Fin T → (ballDomain d).carrier)
    (hu : ∀ s t, (u s t).val (coordinate t) = signedMean θ (s (query t)))
    (P : ℝ) (hpath : ∀ s, pathLength (u s) ≤ P) (good : Finset (Fin T))
    (hinfo : ∀ t ∈ good, (∑ i : Fin t.val, if query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩ = query t then θ^2 else 0) ≤ 1/32) :
    ∃ (s : Fin T → Fin d × Bool) (v : Fin T → (ballDomain d).carrier),
      pathLength v ≤ P ∧ (good.card : ℝ)*θ^2/4 ≤ ∫ ω, regret (A ω) (hardSequence s) v ∂μ := by
  let p := jointWeights (uniformFinite (κ → Bool))
    (fun s => productWeights (fun r => signObservation θ hθ s (query r)))
  let R := fun (z : (κ → Bool) × (Fin T → Bool)) (ω : Ω) =>
    regret (A ω) (hardSequence (fun t => (coordinate t,z.2 t))) (u z.1)
  obtain ⟨z,hz⟩ := finite_oblivious_derandomization μ p R ((good.card : ℝ)*θ^2/4)
    (fun z => hard_regret_integrable μ A hA _ _)
    (by
      intro ω
      change _ ≤ finiteExpectation p (fun z => R z ω)
      rw [joint_expectation]
      exact hard_experiment_lower θ hθ query coordinate (A ω) u hu good hinfo)
  exact ⟨(fun t => (coordinate t,z.2 t)),u z.1,hpath z.1,hz⟩

end Paper254
#print axioms Paper254.randomized_hard_experiment_lower
