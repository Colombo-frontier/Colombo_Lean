import FreshGradientMinimax.RobinMultiBounds
import FreshGradientMinimax.CoreChainSmooth

/-! The original interleaved nonlinear term N, primal D_delta and ideal J.
There are k=T−1 pairs and k*2+1 primal coordinates. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def acceleratedNonlinear {k : ℕ} (q : Euclid (k * 2 + 1)) : ℝ :=
  -coreTheta (q 0) + ∑ i : Fin k, coreLinkTerm (q (interleavedZ i)) (q (interleavedNextX i))

def acceleratedPrimal (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) : ℝ :=
  acceleratedNonlinear (clipVector 2 u) + 2 * robinSmallC (n + 2) *
    ∑ i : Fin k, (flatEdge δ (clipVector 2 u (interleavedX i)) + flatEdge δ (clipVector 2 u (interleavedZ i)) / 4)

def acceleratedIdealValue {k : ℕ} (u : Euclid (k * 2 + 1)) : ℝ :=
  acceleratedNonlinear (clipVector 2 u) +
    6 * ∑ i : Fin k, (clipVector 2 u (interleavedX i) - clipVector 2 u (interleavedZ i) / 2) ^ 2

theorem acceleratedNonlinear_contDiff {k : ℕ} {r : ℕ∞} : ContDiff ℝ r (@acceleratedNonlinear k) := by
  have hp (i : Fin (k * 2 + 1)) : ContDiff ℝ r (fun u : Euclid (k * 2 + 1) => u i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  apply ((coreTheta_contDiff.comp (hp 0)).neg).add
  apply ContDiff.sum
  intro i _
  exact ((coreGate_contDiff.comp (hp (interleavedZ i)).neg).mul
    (coreTheta_contDiff.comp (hp (interleavedNextX i)).neg)).sub
    ((coreGate_contDiff.comp (hp (interleavedZ i))).mul (coreTheta_contDiff.comp (hp (interleavedNextX i))))

theorem acceleratedNonlinear_bound {k : ℕ} (q : Euclid (k * 2 + 1)) :
    |acceleratedNonlinear q| ≤ 9 * (k + 1 : ℕ) := by
  have hs : |coreTheta (q 0)| ≤ 3 := by rw [abs_of_pos (coreTheta_pos _)]; exact (coreTheta_lt_three _).le
  have he : (∑ i : Fin k, |coreLinkTerm (q (interleavedZ i)) (q (interleavedNextX i))|) ≤ 9 * k := by
    calc
      _ ≤ ∑ _ : Fin k, (9 : ℝ) := Finset.sum_le_sum (fun i _ => coreLinkTerm_bound _ _)
      _ = _ := by simp [mul_comm]
  have h := abs_add_le (-coreTheta (q 0)) (∑ i : Fin k, coreLinkTerm (q (interleavedZ i)) (q (interleavedNextX i)))
  rw [abs_neg] at h
  have hsum := Finset.abs_sum_le_sum_abs (fun i : Fin k => coreLinkTerm (q (interleavedZ i)) (q (interleavedNextX i))) Finset.univ
  change |acceleratedNonlinear q| ≤ _ at h
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith only [hs, he, h, hsum]

theorem flatEdge_zero_quadratic (t : ℝ) : flatEdge 0 t = t ^ 2 / 2 := by
  rw [flatEdge_formula (le_refl 0), sub_zero, max_eq_left (abs_nonneg _), sq_abs]

theorem acceleratedPrimal_zero (n k : ℕ) (u : Euclid (k * 2 + 1)) :
    acceleratedPrimal n k 0 u = acceleratedNonlinear (clipVector 2 u) + robinSmallC (n + 2) *
      ∑ i : Fin k, (clipVector 2 u (interleavedX i) ^ 2 + (clipVector 2 u (interleavedZ i) / 2) ^ 2) := by
  unfold acceleratedPrimal
  simp only [flatEdge_zero_quadratic]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem acceleratedPrimal_contDiff (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (acceleratedPrimal n k δ) := by
  have hc := (clipVector_contDiff (n := k * 2 + 1) 2).of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  apply (acceleratedNonlinear_contDiff.comp hc).add
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i _
  exact ((flatEdge_contDiff hδ).comp ((EuclideanSpace.proj (𝕜 := ℝ) (interleavedX i)).contDiff.comp hc)).add
    (((flatEdge_contDiff hδ).comp ((EuclideanSpace.proj (𝕜 := ℝ) (interleavedZ i)).contDiff.comp hc)).div_const 4)

theorem acceleratedPrimal_lower {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) : -9 * (k + 1 : ℕ) ≤ acceleratedPrimal n k δ u := by
  have hN := (abs_le.mp (acceleratedNonlinear_bound (clipVector 2 u))).1
  have hc := (robin_coefficients_bounds hn).2.2.1
  have he : 0 ≤ ∑ i : Fin k, (flatEdge δ (clipVector 2 u (interleavedX i)) + flatEdge δ (clipVector 2 u (interleavedZ i)) / 4) :=
    Finset.sum_nonneg (fun i _ => add_nonneg (flatEdge_bounds hδ _).1 (div_nonneg (flatEdge_bounds hδ _).1 (by norm_num)))
  unfold acceleratedPrimal
  nlinarith only [hN, mul_nonneg (show 0 ≤ 2 * robinSmallC (n + 2) by positivity) he]

end FreshGradientMinimax
