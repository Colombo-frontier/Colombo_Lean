import FreshGradientMinimax.OuterInduction

/-! The outer descent sum is now proved for the implemented program's
successive output distributions, without postulated process accuracy or
integrability. No common-trajectory or independence assumption is needed. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem finite_budget_telescope {H M R : ℕ → ℝ} (η : ℝ) (n : ℕ)
    (hs : ∀ j < n, H (j + 1) + M j + R j ≤ H j + η) :
    H n + (∑ j ∈ Finset.range n, M j) + (∑ j ∈ Finset.range n, R j) ≤ H 0 + n * η := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun j hj => hs j (by omega))
    have hn := hs n (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    linarith

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem outerRunLaw_telescope (O : FreshOracle F σ) {Δ η Ec Ew : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hc : 0 < Ec) (hw : 0 < Ew)
    (hinit : F.proximalStartEnergy (recenterProximal (0 : Euclid dx × Joint dx dy)) ≤ Ec)
    (T : ℕ) (hW : outerWarmEnvelope Δ η T ≤ Ew) :
    (∫ p, F.primalHeight Δ p.2.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel T) +
      (∑ j ∈ Finset.range T, ∫ p, proximalMoveEnergy L p ∂outerRunLaw L σ μ η Ec Ew O.kernel (j + 1)) +
      (∑ j ∈ Finset.range T, ∫ p, F.proximalResidualEnergy p.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel (j + 1)) ≤ Δ + T * η := by
  have h := finite_budget_telescope
    (H := fun j => ∫ p, F.primalHeight Δ p.2.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel j)
    (M := fun j => ∫ p, proximalMoveEnergy L p ∂outerRunLaw L σ μ η Ec Ew O.kernel (j + 1))
    (R := fun j => ∫ p, F.proximalResidualEnergy p.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel (j + 1))
    η T (fun j hj => F.outerRunLaw_descent O hΔ hη hc hw hinit T hW hj)
  simpa only [outerRunLaw_zero, integral_dirac, Prod.fst_zero, Prod.snd_zero, F.primalHeight_zero] using h

theorem outerRunLaw_movement_bound (O : FreshOracle F σ) {Δ η Ec Ew : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hc : 0 < Ec) (hw : 0 < Ew)
    (hinit : F.proximalStartEnergy (recenterProximal (0 : Euclid dx × Joint dx dy)) ≤ Ec)
    (T : ℕ) (hW : outerWarmEnvelope Δ η T ≤ Ew) :
    (∑ j ∈ Finset.range T, ∫ p, proximalMoveEnergy L p ∂outerRunLaw L σ μ η Ec Ew O.kernel (j + 1)) ≤ Δ + T * η := by
  have h := F.outerRunLaw_telescope O hΔ hη hc hw hinit T hW
  have hh := integral_nonneg (f := fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1)
    (fun p => F.primalHeight_nonneg hΔ p.2.1)
    (μ := outerRunLaw L σ μ η Ec Ew O.kernel T)
  have hr : 0 ≤ ∑ j ∈ Finset.range T, ∫ p, F.proximalResidualEnergy p.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel (j + 1) :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun p => F.proximalResidualEnergy_nonneg p.1))
  linarith

theorem outerRunLaw_residual_bound (O : FreshOracle F σ) {Δ η Ec Ew : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hc : 0 < Ec) (hw : 0 < Ew)
    (hinit : F.proximalStartEnergy (recenterProximal (0 : Euclid dx × Joint dx dy)) ≤ Ec)
    (T : ℕ) (hW : outerWarmEnvelope Δ η T ≤ Ew) :
    (∑ j ∈ Finset.range T, ∫ p, F.proximalResidualEnergy p.1 ∂outerRunLaw L σ μ η Ec Ew O.kernel (j + 1)) ≤ Δ + T * η := by
  have h := F.outerRunLaw_telescope O hΔ hη hc hw hinit T hW
  have hh := integral_nonneg (f := fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1)
    (fun p => F.primalHeight_nonneg hΔ p.2.1)
    (μ := outerRunLaw L σ μ η Ec Ew O.kernel T)
  have hm : 0 ≤ ∑ j ∈ Finset.range T, ∫ p, proximalMoveEnergy L p ∂outerRunLaw L σ μ η Ec Ew O.kernel (j + 1) :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun p => mul_nonneg F.L_pos.le (sq_nonneg ‖p.2.1 - p.1‖)))
  linarith

end NCObjective
end FreshGradientMinimax
