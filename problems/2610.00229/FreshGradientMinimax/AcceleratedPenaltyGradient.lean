import FreshGradientMinimax.WeightedFlatEnergy
import FreshGradientMinimax.AcceleratedPrimal

/-! The exact flattened primal penalty of the accelerated construction.
Its gradient is a weighted, zero-padded flat slope. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def acceleratedPenaltyWeight {k : ℕ} (j : Fin (k * 2)) : ℝ :=
  (![1, 1 / 4] : Fin 2 → ℝ) (finProdFinEquiv.symm j).2

@[simp]
theorem acceleratedPenaltyWeight_block {k : ℕ} (i : Fin k) (a : Fin 2) :
    acceleratedPenaltyWeight (finProdFinEquiv (i,a)) = (![1,1/4] : Fin 2 → ℝ) a := by
  simp only [acceleratedPenaltyWeight, Equiv.symm_apply_apply]

theorem acceleratedPenaltyWeight_bound {k : ℕ} (j : Fin (k * 2)) : |acceleratedPenaltyWeight j| ≤ 1 := by
  obtain ⟨⟨i,a⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [acceleratedPenaltyWeight_block]
  fin_cases a
  · change |(1 : ℝ)| ≤ 1
    norm_num
  · change |(1 / 4 : ℝ)| ≤ 1
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 4)]
    norm_num

def acceleratedPenalty (n k : ℕ) (δ : ℝ) (q : Euclid (k * 2 + 1)) : ℝ :=
  2 * robinSmallC (n + 2) * weightedFlatEnergy acceleratedPenaltyWeight δ (euclidDropLast (k * 2) q)

def acceleratedPenaltyGradient (n k : ℕ) (δ : ℝ) (q : Euclid (k * 2 + 1)) : Euclid (k * 2 + 1) :=
  (2 * robinSmallC (n + 2)) • pathPadLeft (k * 2)
    (weightedFlatSlope acceleratedPenaltyWeight δ (euclidDropLast (k * 2) q))

theorem acceleratedPenalty_formula (n k : ℕ) (δ : ℝ) (q : Euclid (k * 2 + 1)) :
    acceleratedPenalty n k δ q = 2 * robinSmallC (n + 2) *
      ∑ i : Fin k, (flatEdge δ (q (interleavedX i)) + flatEdge δ (q (interleavedZ i)) / 4) := by
  unfold acceleratedPenalty weightedFlatEnergy
  rw [sum_fin_blocks]
  simp [Fin.sum_univ_two, interleavedX, interleavedZ, div_eq_mul_inv, mul_comm]

theorem acceleratedPrimal_penalty (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) :
    acceleratedPrimal n k δ u = acceleratedNonlinear (clipVector 2 u) +
      acceleratedPenalty n k δ (clipVector 2 u) := by
  rw [acceleratedPenalty_formula]
  rfl

theorem acceleratedPenalty_hasFDerivAt (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (q : Euclid (k * 2 + 1)) :
    HasFDerivAt (acceleratedPenalty n k δ) (innerSL ℝ (acceleratedPenaltyGradient n k δ q)) q := by
  have h := ((weightedFlatEnergy_hasFDerivAt acceleratedPenaltyWeight hδ (euclidDropLast (k * 2) q)).comp q
    (euclidDropLast (k * 2)).hasFDerivAt).const_mul (2 * robinSmallC (n + 2))
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [acceleratedPenaltyGradient, ← euclidDropLast_adjoint, ContinuousLinearMap.adjoint_inner_left,
    innerSL_apply, real_inner_smul_left]

theorem acceleratedPenalty_coefficient {n : ℕ} (hn : 10 ≤ n + 2) :
    0 ≤ 2 * robinSmallC (n + 2) ∧ 2 * robinSmallC (n + 2) ≤ 84 := by
  have hc := robin_coefficients_bounds hn
  constructor <;> linarith only [hc.2.2.1, hc.2.2.2]

theorem acceleratedPenaltyGradient_norm {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (q : Euclid (k * 2 + 1)) : ‖acceleratedPenaltyGradient n k δ q‖ ≤ 84 * ‖q‖ := by
  have hc := acceleratedPenalty_coefficient hn
  unfold acceleratedPenaltyGradient
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.1, pathPadLeft_norm]
  exact mul_le_mul hc.2 ((weightedFlatSlope_norm acceleratedPenaltyWeight_bound hδ _).trans
    (euclidDropLast_norm q)) (norm_nonneg _) (by norm_num)

theorem acceleratedPenaltyGradient_difference {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (q p : Euclid (k * 2 + 1)) :
    ‖acceleratedPenaltyGradient n k δ q - acceleratedPenaltyGradient n k δ p‖ ≤ 84 * ‖q - p‖ := by
  have hc := acceleratedPenalty_coefficient hn
  unfold acceleratedPenaltyGradient
  rw [← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.1, pathPadLeft_norm]
  have h := weightedFlatSlope_difference acceleratedPenaltyWeight_bound hδ
    (euclidDropLast (k * 2) q) (euclidDropLast (k * 2) p)
  rw [← map_sub] at h
  exact mul_le_mul hc.2 (h.trans (euclidDropLast_norm (q - p))) (norm_nonneg _) (by norm_num)

theorem acceleratedPenaltyGradient_perturbation {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (q : Euclid (k * 2 + 1)) :
    ‖acceleratedPenaltyGradient n k δ q - acceleratedPenaltyGradient n k 0 q‖ ≤
      84 * δ * Real.sqrt (k * 2 : ℕ) := by
  have hc := acceleratedPenalty_coefficient hn
  unfold acceleratedPenaltyGradient
  rw [← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.1, pathPadLeft_norm]
  simpa only [mul_assoc] using mul_le_mul hc.2
    (weightedFlatSlope_perturbation acceleratedPenaltyWeight_bound hδ _) (norm_nonneg _) (by norm_num)

theorem acceleratedPenaltyGradient_coordinate {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (q : Euclid (k * 2 + 1)) (j : Fin (k * 2 + 1)) :
    |acceleratedPenaltyGradient n k δ q j| ≤ 84 * |q j| := by
  have hc := acceleratedPenalty_coefficient hn
  refine Fin.lastCases ?_ (fun a => ?_) j
  · simp only [acceleratedPenaltyGradient, PiLp.smul_apply, pathPadLeft_apply, Fin.snoc_last,
      smul_eq_mul, mul_zero, abs_zero]
    positivity
  · simp only [acceleratedPenaltyGradient, PiLp.smul_apply, pathPadLeft_apply, Fin.snoc_castSucc,
      smul_eq_mul, abs_mul, abs_of_nonneg hc.1]
    exact mul_le_mul hc.2 (by simpa only [euclidDropLast_apply] using
      weightedFlatSlope_coordinate acceleratedPenaltyWeight_bound hδ (euclidDropLast (k * 2) q) a)
      (abs_nonneg _) (by norm_num)

end FreshGradientMinimax
