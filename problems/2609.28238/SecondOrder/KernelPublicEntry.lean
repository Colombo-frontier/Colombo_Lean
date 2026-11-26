import SecondOrder.KernelFirstEntry
import SecondOrder.KernelHiddenIndependence

open MeasureTheory ProbabilityTheory

universe u
namespace SecondOrder
noncomputable section
variable {S U A : Type u} [MeasurableSpace S] [MeasurableSpace U] [MeasurableSpace A]

theorem kernelSurvivalSet_mapInitial (f : S → U) (safe : ∀ n, Set (FiniteHistory U A n)) :
    ∀ n, kernelSurvivalSet (fun m => finiteHistoryMapInitial f m ⁻¹' safe m) n=
      finiteHistoryMapInitial f n ⁻¹' kernelSurvivalSet safe n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [kernelSurvivalSet,ih]
    rfl

theorem kernelBeforeSet_mapInitial (f : S → U) (safe : ∀ n, Set (FiniteHistory U A n)) (n : ℕ) :
    kernelBeforeSet (fun m => finiteHistoryMapInitial f m ⁻¹' safe m) n=
      finiteHistoryMapInitial f n ⁻¹' kernelBeforeSet safe n := by
  cases n with
  | zero => rfl
  | succ n =>
    change Prod.fst ⁻¹' kernelSurvivalSet (fun m => finiteHistoryMapInitial f m ⁻¹' safe m) n=_
    rw [kernelSurvivalSet_mapInitial]
    rfl

theorem kernelFirstExitSet_mapInitial (f : S → U) (safe : ∀ n, Set (FiniteHistory U A n)) (n : ℕ) :
    kernelFirstExitSet (fun m => finiteHistoryMapInitial f m ⁻¹' safe m) n=
      finiteHistoryMapInitial f n ⁻¹' kernelFirstExitSet safe n := by
  rw [kernelFirstExitSet,kernelBeforeSet_mapInitial]
  rfl

end
end SecondOrder
