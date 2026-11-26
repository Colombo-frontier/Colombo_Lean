import Bilevel.CachedExpectedAccuracy
import Bilevel.StochasticOuter

/-! Expected loss for an actual independent uniform terminal index.
The good-event assumption bounds the average over indices, not every iterate.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Bilevel.CachedUniformOutput

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

theorem expected_selected_loss (n : ℕ) [NeZero n] (loss : ℕ → Ω → ℝ)
    (bad : Set Ω) (hbad : MeasurableSet bad)
    (hmeas : ∀ i < n, AEStronglyMeasurable (loss i) ν)
    {ε G δ : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hpos : ∀ i < n, ∀ ω, 0 ≤ loss i ω)
    (hcap : ∀ i < n, ∀ ω, loss i ω ≤ G)
    (hgood : ∀ ω ∉ bad, (∑ i ∈ Finset.range n, loss i ω) / n ≤ ε/2)
    (hprob : ν.real bad ≤ δ) (hbudget : δ*G ≤ ε/2) :
    Integrable (fun p : Fin n × Ω => loss p.1 p.2) (StochasticOuter.outputLaw n ν) ∧
      (∫ p : Fin n × Ω, loss p.1 p.2 ∂StochasticOuter.outputLaw n ν) ≤ ε := by
  have hi (i : ℕ) (hin : i < n) : Integrable (loss i) ν :=
    (integrable_const G).mono' (hmeas i hin) (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_of_nonneg (hpos i hin ω)]
      exact hcap i hin ω))
  let avg := fun ω => (∑ i ∈ Finset.range n, loss i ω) / n
  have hsum : Integrable (fun ω => ∑ i ∈ Finset.range n, loss i ω) ν :=
    integrable_finset_sum _ (fun i hin => hi i (Finset.mem_range.mp hin))
  have havg : Integrable avg ν := hsum.div_const _
  have hnn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_neZero n)
  have havg0 (ω : Ω) : 0 ≤ avg ω :=
    div_nonneg (Finset.sum_nonneg (fun i hin => hpos i (Finset.mem_range.mp hin) ω)) hnn.le
  have havgcap (ω : Ω) : avg ω ≤ G := by
    apply (div_le_iff₀ hnn).mpr
    calc
      _ ≤ ∑ _i ∈ Finset.range n, G :=
        Finset.sum_le_sum (fun i hin => hcap i (Finset.mem_range.mp hin) ω)
      _ = G*n := by simp [mul_comm]
  have hacc := CachedExpectedAccuracy.accuracy_from_cap avg bad hbad havg.aestronglyMeasurable
    hε hG havg0 havgcap hgood hprob hbudget
  have hp := StochasticOuter.integrable_uniform_output n loss hi
  refine ⟨hp, ?_⟩
  rw [StochasticOuter.uniform_output_integral n loss hp]
  have hidentity : (∫ ω, avg ω ∂ν) =
      (∑ i ∈ Finset.range n, ∫ ω, loss i ω ∂ν) / n := by
    dsimp [avg]
    rw [integral_div, integral_finset_sum _ (fun i hin => hi i (Finset.mem_range.mp hin))]
  rw [hidentity] at hacc
  exact hacc.2

end Bilevel.CachedUniformOutput
