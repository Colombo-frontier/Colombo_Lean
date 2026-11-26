import Bilevel.MultiscaleOracle
import Bilevel.ZeroChainScheduleBudgets

/-! Summation by parts rewrites the exact inactive potential entirely in
terms of flattened residuals, including the zero-level case J=0. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean SmallGapProfiles ZeroChain ZeroChainSchedule
open ZeroChainFlatteningBounds ZeroChainFlatteningMap ZeroChainFlatteningCutoff
set_option maxHeartbeats 500000

def successiveDifference (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | j+1 => a (j+1)-a j

theorem weighted_differences (a q : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N+1),successiveDifference a j*q j) =
      a N*q N+∑ j ∈ Finset.range N,a j*(q j-q (j+1)) := by
  induction N with
  | zero => simp [successiveDifference]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ,successiveDifference]
    ring

theorem flattenMap_scaling (n : ℕ) (β δ : ℝ) (_hβ : β ≠ 0) (z : Space n) :
    β⁻¹ • flattenMap n (β*δ) z = flattenMap n δ (β⁻¹ • z) := by
  ext j
  simp only [flattenMap,coordinateMap_apply,PiLp.smul_apply,smul_eq_mul,flatten]
  have he : z j/(β*δ) = (β⁻¹*z j)/δ := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

def carriedApproximation (j : ℕ) (u : E) : ℝ :=
  P.amplitude*ZeroChainMultiscale.approximation n (levels P.θ) (resolution P.c 1 P.θ) j
    (P.β⁻¹ • WrappedChain.coordinates n P.R P.U u)

def flatApproximation (j : ℕ) (u : E) : ℝ :=
  flattenedResidual n P.amplitude P.β (resolution P.c P.β P.θ j)
    (WrappedChain.coordinates n P.R P.U u)

theorem pieces_difference (u : E) (j : ℕ) :
    P.pieces j u = successiveDifference (fun i => P.carriedApproximation i u) j := by
  cases j with
  | zero => rfl
  | succ j =>
    change P.amplitude*(_-_) = P.amplitude*_-P.amplitude*_
    ring

theorem carriedApproximation_last (u : E) : P.carriedApproximation (levels P.θ) u = P.residual u := by
  simp only [carriedApproximation,ZeroChainMultiscale.approximation,lt_self_iff_false,if_false]
  rfl

theorem carriedApproximation_flat (j : ℕ) (hj : j < levels P.θ) :
    P.carriedApproximation j = P.flatApproximation j := by
  funext u
  have he : resolution P.c P.β P.θ j = P.β*resolution P.c 1 P.θ j := by
    simp only [resolution,mul_one]
    ring
  simp only [carriedApproximation,ZeroChainMultiscale.approximation,if_pos hj,flatApproximation,
    flattenedResidual,ZeroChainResidualScaled.R,ZeroChainResidualScaled.scaled,he,
    flattenMap_scaling n P.β _ P.β_pos.ne']

theorem flatApproximation_contDiff (j : ℕ) : ContDiff ℝ 3 (P.flatApproximation j) :=
  (flattenedResidual_contDiff n P.amplitude P.β (resolution P.c P.β P.θ j)).comp
    (ZeroChainWrappedResidual.coordinates_contDiff n P.R P.U)

omit [CompleteSpace E] in
theorem signalResolution_le_resolution (j : ℕ) (hj : j < levels P.θ) :
    P.signalResolution ≤ resolution P.c P.β P.θ j := by
  have hp : (4:ℝ)^(j+1) ≤ 2*4^(levels P.θ) := by
    have hh : (4:ℝ)^(j+1) ≤ 4^(levels P.θ) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hz : 0 ≤ (4:ℝ)^(levels P.θ) := by positivity
    linarith
  have hi := one_div_le_one_div_of_le (show 0 < (4:ℝ)^(j+1) by positivity) hp
  have he : aExponent j ≤ bExponent (levels P.θ) := by
    dsimp [aExponent,bExponent]
    linarith
  apply P.signalResolution_le_width.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg P.c_pos.le P.β_pos.le)
  exact Real.rpow_le_rpow_of_exponent_le P.θ_ge_one (neg_le_neg he)

theorem inactivePerturbation_flat_formula (y : LowerSpace E) :
    P.inactivePerturbation y = P.μ/(2*P.L^2)*P.inactiveResidual (uProj E y)^2-
      P.μ/P.L*(P.inactiveResidual (uProj E y)*normal P.finalWidth (sProj E y)+
        ∑ j ∈ Finset.range (levels P.θ),P.flatApproximation j (uProj E y)*
          (normal (width P.c P.β P.θ j) (sProj E y)-normal (width P.c P.β P.θ (j+1)) (sProj E y))) := by
  have hw := weighted_differences (fun j => P.carriedApproximation j (uProj E y))
    (fun j => normal (width P.c P.β P.θ j) (sProj E y)) (levels P.θ)
  simp only [← P.pieces_difference,P.carriedApproximation_last] at hw
  have he : (∑ j ∈ Finset.range (levels P.θ),P.carriedApproximation j (uProj E y)*
      (normal (width P.c P.β P.θ j) (sProj E y)-normal (width P.c P.β P.θ (j+1)) (sProj E y))) =
      ∑ j ∈ Finset.range (levels P.θ),P.flatApproximation j (uProj E y)*
      (normal (width P.c P.β P.θ j) (sProj E y)-normal (width P.c P.β P.θ (j+1)) (sProj E y)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [P.carriedApproximation_flat j (Finset.mem_range.mp hj)]
  rw [he] at hw
  simp only [inactivePerturbation,CompensatedMean.Data.perturbation,data,signal]
  rw [hw]
  simp only [residualDifference,finalWidth]
  ring

end Parameters
end Bilevel.MultiscaleMean
