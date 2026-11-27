import ReadOnceExpectation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Task006.Full
namespace OracleAlgorithm

noncomputable section

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

def queriedHandles (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion (fun i : Fin N =>
    ((A.executedAction F tape seed i).map Prod.fst).toFinset)

theorem mem_queriedHandles (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (h : ℕ) :
    h ∈ A.queriedHandles F tape seed ↔ A.queriedBefore F tape seed h N := by
  classical
  simp only [queriedHandles,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Option.mem_toFinset,queriedBefore]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨i,i.isLt,hi⟩
  · rintro ⟨i,_,hi⟩; exact ⟨i,hi⟩

theorem queriedHandles_card_le (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) : (A.queriedHandles F tape seed).card ≤ N := by
  classical
  calc
    _ ≤ ∑ i : Fin N, (((A.executedAction F tape seed i).map Prod.fst).toFinset).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin N, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases (A.executedAction F tape seed i).map Prod.fst <;> simp
    _ = N := by simp

theorem queriedIndicator_nonneg (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (seed : S) (h : ℕ) (tape : ℕ → Ω) : 0 ≤ A.queriedIndicator F seed h tape := by
  exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem queriedIndicator_le_one (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (seed : S) (h : ℕ) (tape : ℕ → Ω) : A.queriedIndicator F seed h tape ≤ 1 := by
  classical
  unfold queriedIndicator
  by_cases hq : A.queriedBefore F tape seed h N <;> simp [Set.indicator,hq]

theorem tsum_queriedIndicator (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (seed : S) (tape : ℕ → Ω) :
    (∑' h, ENNReal.ofReal (A.queriedIndicator F seed h tape)) =
      ((A.queriedHandles F tape seed).card : ℝ≥0∞) := by
  classical
  rw [tsum_eq_sum (s := A.queriedHandles F tape seed)]
  · calc
      _ = ∑ _h ∈ A.queriedHandles F tape seed, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro h hh
        have hq := (A.mem_queriedHandles F tape seed h).mp hh
        simp [queriedIndicator,Set.indicator,hq]
      _ = _ := by simp
  · intro h hh
    have hq : ¬ A.queriedBefore F tape seed h N := by
      simpa only [A.mem_queriedHandles F tape seed h] using hh
    simp [queriedIndicator,Set.indicator,hq]

theorem tsum_queriedIndicator_le (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (seed : S) (tape : ℕ → Ω) :
    (∑' h, ENNReal.ofReal (A.queriedIndicator F seed h tape)) ≤ (N : ℝ≥0∞) := by
  rw [A.tsum_queriedIndicator F seed tape]
  exact_mod_cast A.queriedHandles_card_le F tape seed

end
end OracleAlgorithm
end Task006.Full
