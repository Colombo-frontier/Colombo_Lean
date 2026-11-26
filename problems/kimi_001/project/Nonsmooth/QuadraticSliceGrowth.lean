import Nonsmooth.SoftSliceGrowthBounds
import Nonsmooth.QuadraticSliceConstraints

open Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {ι : Type} [Fintype ι]

theorem softSlice_growth_of_constraint_bounds (ρ : ℝ) (D : SmoothSliceConstraints ι)
    (h : ∀ t, ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Metric.ball t 1, ∀ i x,
      |D.dt i r x| ≤ C * (1 + |x| ^ 2) ∧ |D.dtt i r x| ≤ C) :
    SoftSlicePolynomialGrowth ρ D := by
  intro t
  obtain ⟨C, hC, hb⟩ := h t
  let P := |ρ| * (|t| + 1) + (Fintype.card ι : ℝ) * C
  let Q := |ρ| + (Fintype.card ι : ℝ) * (2 * C ^ 2 + C)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨P + Q, add_nonneg hP hQ, ?_⟩
  intro r hr x
  have hr1 : |r - t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
  have hrt : |r| ≤ |t| + 1 := by
    have hh := abs_add_le (r - t) t
    rw [sub_add_cancel] at hh
    linarith
  constructor
  · have hs := softSlice_score_growth_bound ρ D r hC hrt (fun i x => (hb r hr i x).1) x
    apply hs.trans
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hQ) (by positivity)
  · have hs := softSlice_gamma_growth_bound ρ D r hC
      (fun i x => (hb r hr i x).1) (fun i x => (hb r hr i x).2) x
    apply hs.trans
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hP) (by positivity)

theorem quadraticSliceConstraints_local_bounds (A B C D E F : ι → ℝ) (t : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Metric.ball t 1, ∀ i x,
      |(quadraticSliceConstraints A B C D E F).dt i r x| ≤ K * (1 + |x| ^ 2) ∧
      |(quadraticSliceConstraints A B C D E F).dtt i r x| ≤ K := by
  let L : ι → ℝ := fun i => 2 * |A i| * (|t| + 1) + 2 * |B i| + |D i| + 2 * |A i|
  let K : ℝ := ∑ i, L i
  have hL (i : ι) : 0 ≤ L i := by dsimp [L]; positivity
  have hKi (i : ι) : L i ≤ K := Finset.single_le_sum (fun j _ => hL j) (Finset.mem_univ i)
  refine ⟨K, Finset.sum_nonneg (fun i _ => hL i), ?_⟩
  intro r hr i x
  have hr1 : |r - t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
  have hrt : |r| ≤ |t| + 1 := by
    have hh := abs_add_le (r - t) t
    rw [sub_add_cancel] at hh
    linarith
  have hx : |x| ≤ 1 + |x| ^ 2 := by nlinarith [sq_nonneg (|x| - 1)]
  have hcoeff := hKi i
  dsimp only [L] at hcoeff
  constructor
  · dsimp only [quadraticSliceConstraints]
    have hab := (abs_add_le (2 * A i * r + 2 * B i * x) (D i)).trans
      (add_le_add (abs_add_le (2 * A i * r) (2 * B i * x)) le_rfl)
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hab
    have h1 := mul_le_mul_of_nonneg_left hrt (show 0 ≤ 2 * |A i| by positivity)
    have h2 := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * |B i| by positivity)
    have h3 := mul_nonneg (show 0 ≤ 2 * |A i| * (|t| + 1) + |D i| + 2 * |A i| by positivity)
      (sq_nonneg |x|)
    have h4 := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ 1 + |x| ^ 2 by positivity)
    nlinarith [abs_nonneg (A i)]
  · dsimp only [quadraticSliceConstraints]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h0 : 0 ≤ 2 * |A i| * (|t| + 1) + 2 * |B i| + |D i| := by positivity
    linarith

theorem quadraticSoftSlice_polynomial_growth (ρ : ℝ) (A B C D E F : ι → ℝ) :
    SoftSlicePolynomialGrowth ρ (quadraticSliceConstraints A B C D E F) :=
  softSlice_growth_of_constraint_bounds ρ _ (quadraticSliceConstraints_local_bounds A B C D E F)

end
end Nonsmooth
