import HandleExpectation
import HardFamily

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Task006.Full

noncomputable section

def nonzeroStatus (g : ℝ) : ℝ := if g = 0 then 0 else 1

lemma nonzeroStatus_measurable : Measurable nonzeroStatus :=
  Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

lemma nonzeroStatus_nonneg (g : ℝ) : 0 ≤ nonzeroStatus g := by
  unfold nonzeroStatus
  split_ifs <;> norm_num

lemma nonzeroStatus_le_one (g : ℝ) : nonzeroStatus g ≤ 1 := by
  unfold nonzeroStatus
  split_ifs <;> norm_num

namespace OracleAlgorithm

variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

def informativeHandles (A : OracleAlgorithm d N S) (F : Space d → ℝ → ℝ)
    (tape : ℕ → ℝ) (seed : S) : Finset ℕ :=
  (A.queriedHandles F tape seed).filter (fun h => tape h ≠ 0)

theorem weightedHandles_nonzero_eq (A : OracleAlgorithm d N S) (F : Space d → ℝ → ℝ)
    (seed : S) (tape : ℕ → ℝ) :
    A.weightedHandles F seed nonzeroStatus tape =
      ((A.informativeHandles F tape seed).card : ℝ≥0∞) := by
  classical
  unfold weightedHandles
  rw [tsum_eq_sum (s := A.informativeHandles F tape seed)]
  · calc
      _ = ∑ _h ∈ A.informativeHandles F tape seed, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro h hh
        rcases Finset.mem_filter.mp hh with ⟨hh,hz⟩
        have hq := (A.mem_queriedHandles F tape seed h).mp hh
        simp [queriedIndicator,Set.indicator,hq,nonzeroStatus,hz]
      _ = _ := by simp
  · intro h hh
    by_cases hq : A.queriedBefore F tape seed h N
    · have hz : tape h = 0 := by
        by_contra hz
        exact hh (Finset.mem_filter.mpr ⟨(A.mem_queriedHandles F tape seed h).mpr hq,hz⟩)
      simp [nonzeroStatus,hz]
    · simp [queriedIndicator,Set.indicator,hq]

theorem informativeHandles_card_le (A : OracleAlgorithm d N S) (F : Space d → ℝ → ℝ)
    (seed : S) (tape : ℕ → ℝ) : (A.informativeHandles F tape seed).card ≤ N :=
  (Finset.card_filter_le _ _).trans (A.queriedHandles_card_le F tape seed)

theorem expected_informativeHandles (A : OracleAlgorithm d N S)
    (F : Space d → ℝ → ℝ) (hF : Measurable (Function.uncurry F))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (seed : S) :
    (∫ tape, ((A.informativeHandles F tape seed).card : ℝ) ∂iidHandleLaw μ) ≤
      (∫ g, nonzeroStatus g ∂μ) * N := by
  have he := A.expected_weighted_handles F hF μ seed 0 nonzeroStatus
    nonzeroStatus_measurable nonzeroStatus_nonneg nonzeroStatus_le_one
  simpa only [A.weightedHandles_nonzero_eq F seed,ENNReal.toReal_natCast] using he

end OracleAlgorithm

namespace HardFamily

lemma integral_nonzeroStatus (L A : ℝ) (hL : 0 < L) (hA : 16 ≤ A) :
    (∫ g, nonzeroStatus g ∂law L A hA) = 4096 / A ^ 3 := by
  have hB : L * A ^ 2 / 256 ≠ 0 := by positivity
  rw [law,integral_bernoulliMeasure]
  simp [nonzeroStatus,hB,Task006LowerAudit.rareParameter,smul_eq_mul]

theorem informative_handle_budget {d N : ℕ} {S : Type*} [MeasurableSpace S]
    (alg : OracleAlgorithm d N S) (L A : ℝ) (hL : 0 < L) (hA : 16 ≤ A)
    (θ : Space d) (seed : S) :
    (∫ tape, ((alg.informativeHandles (fun x g => g * inner ℝ θ x) tape seed).card : ℝ)
      ∂iidHandleLaw (law L A hA)) ≤ (4096 / A ^ 3) * N := by
  have hm : Measurable (Function.uncurry (fun x : Space d => fun g : ℝ => g * inner ℝ θ x)) :=
    measurable_snd.mul (measurable_const.inner measurable_fst)
  simpa only [integral_nonzeroStatus L A hL hA] using
    alg.expected_informativeHandles (fun x g => g * inner ℝ θ x) hm (law L A hA) seed

end HardFamily
end
end Task006.Full
