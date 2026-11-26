import FreshGradientMinimax.HistoryEmbedding
import FreshGradientMinimax.EntropyChain

/-! Uniform one-response KL bounds accumulate linearly along the actual
adaptive history law, including the algorithm's arbitrary random seed. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace Algorithm
variable {dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)
  (ν : Measure Seed) [IsProbabilityMeasure ν]
  {K J : Kernel (Joint dx dy) (Joint dx dy)} [IsMarkovKernel K] [IsMarkovKernel J]

theorem historyLaw_kl_bound {c : ℝ} (hc : 0 ≤ c)
    (hK : ∀ z, klDiv (K z) (J z) ≤ ENNReal.ofReal c) (n : ℕ) :
    klDiv (A.historyLaw ν K n) (A.historyLaw ν J n) ≤ ENNReal.ofReal (n * c) := by
  induction n with
  | zero =>
    change klDiv (A.historyLaw ν K 0) (A.historyLaw ν K 0) ≤ _
    simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) * c := mul_nonneg (Nat.cast_nonneg _) hc
    have hstep := compProd_kl_bound (K := A.responseKernel K n) (J := A.responseKernel J n)
      hn hc ih (fun s => hK (A.query n s))
    have hb := finite_kl_information_bound (add_nonneg hn hc) hstep
    rw [A.historyLaw_succ ν K n, A.historyLaw_succ ν J n,
      klDiv_map_embedding (A.append_measurableEmbedding n) hb.1 hb.2.1]
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hstep

omit [IsProbabilityMeasure ν] [IsMarkovKernel K] in
theorem outputLaw_real_event {E : Set (Euclid dx)} (hE : MeasurableSet E) (n : ℕ) :
    (A.outputLaw ν K n).real E = (A.historyLaw ν K n).real (A.output n ⁻¹' E) := by
  rw [A.outputLaw_historyLaw, measureReal_def, Measure.map_apply (A.output_measurable n) hE]
  rfl

theorem output_testing_information {c : ℝ} (hc : 0 ≤ c)
    (hK : ∀ z, klDiv (K z) (J z) ≤ ENNReal.ofReal c)
    {E : Set (Euclid dx)} (hE : MeasurableSet E) (n : ℕ)
    (hP : 2 / 3 ≤ (A.outputLaw ν K n).real E)
    (hQ : (A.outputLaw ν J n).real E ≤ 1 / 3) :
    Real.log 2 / 3 ≤ (n : ℝ) * c := by
  rw [A.outputLaw_real_event ν hE n] at hP hQ
  have ht := testing_event_kl ((A.output_measurable n) hE) hP hQ
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) hc)).mp
    (ht.trans (A.historyLaw_kl_bound ν hc hK n))

end Algorithm
end FreshGradientMinimax
