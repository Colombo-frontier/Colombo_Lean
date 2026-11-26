import LowRank.BlockReveal

/-! Recover the newly exposed scalar pivot and column from the actual Gram
reply. The recovery is a total measurable formula; its correctness requires
the pivot to be nonzero, an event already proved almost sure for Gaussians. -/

namespace LowRank
open MeasureTheory Matrix
open scoped Matrix
noncomputable section

def recoveredPivot {r : ℕ} (w : Fin (r + 1) → ℝ) : ℝ := Real.sqrt (w 0)

def recoveredColumn {r : ℕ} (w : Fin (r + 1) → ℝ) : Fin r → ℝ :=
  fun i => w i.succ / recoveredPivot w

theorem measurable_recoveredPivot (r : ℕ) : Measurable (recoveredPivot (r := r)) := by
  unfold recoveredPivot
  fun_prop

theorem measurable_recoveredColumn (r : ℕ) : Measurable (recoveredColumn (r := r)) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.succ).div (measurable_recoveredPivot r)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {r s : ℕ}

theorem recoveredPivot_gram (b : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    recoveredPivot (fun i => (D * Dᵀ) i 0) = ‖(basisCoordinates b).symm (D 0)‖ := by
  rw [recoveredPivot, revealGaussianBlock_gram_pivot b D, Real.sqrt_sq (norm_nonneg _)]

theorem recoveredColumn_gram (b : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ)
    (hρ : ‖(basisCoordinates b).symm (D 0)‖ ≠ 0) :
    recoveredColumn (fun i => (D * Dᵀ) i 0) = (revealGaussianBlock b D).1.2 := by
  funext i
  rw [recoveredColumn, recoveredPivot_gram b D, revealGaussianBlock_gram_column b D]
  exact mul_div_cancel_left₀ _ hρ

theorem measurable_nextExposedA {S : Type*} [MeasurableSpace S] {q r : ℕ}
    (A : S → Matrix (Fin q) (Fin q) ℝ) (C : S → Matrix (Fin (r + 1)) (Fin q) ℝ)
    (ρ : S → ℝ) (hA : Measurable A) (hC : Measurable C) (hρ : Measurable ρ) :
    Measurable (fun st => nextExposedA (A st) (C st) (ρ st)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases hρ (fun j => ?_) j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply 0).comp hC)
  · refine Fin.cases measurable_const (fun j => ?_) j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)

theorem measurable_nextExposedC {S : Type*} [MeasurableSpace S] {q r : ℕ}
    (C : S → Matrix (Fin (r + 1)) (Fin q) ℝ) (c : S → Fin r → ℝ)
    (hC : Measurable C) (hc : Measurable c) :
    Measurable (fun st => nextExposedC (C st) (c st)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  refine Fin.cases ((measurable_pi_apply i).comp hc) (fun j => ?_) j
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i.succ).comp hC)

end
end LowRank
