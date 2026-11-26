import NCBall.GaussianLinearImage
import NCBall.PosteriorSmallBall

/-! # Small balls for actual Gaussian linear images -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_linear_image_smallBall {k : ℕ} (b : OrthonormalBasis (Fin k) ℝ F)
    (T : E →L[ℝ] F) (v : Fin k → E)
    (hcoords : ∀ z i, ⟪b i, T z⟫_ℝ = ⟪v i, z⟫_ℝ)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0)
    (u : F) (S : Finset (Fin k)) {a : ℝ} (ha : 0 < a)
    (hS : 3 * a / 4 ≤ (S.card : ℝ))
    (hv : ∀ i ∈ S, 1 / (2 * a) ≤ ‖v i‖ ^ 2) :
    (euclideanGaussianLaw E).real {z | ‖T z - u‖ ≤ 1 / 16} ≤ Real.exp (-a / 8) := by
  let c : Fin k → ℝ := fun i => ⟪b i, u⟫_ℝ
  let A := {x : Fin k → ℝ | ∑ i, (x i - c i) ^ 2 ≤ 1 / 256}
  have hA : MeasurableSet A := by
    apply measurableSet_le
    · exact (by fun_prop : Continuous (fun x : Fin k → ℝ => ∑ i, (x i - c i) ^ 2)).measurable
    · exact measurable_const
  have he : {z : E | ‖T z - u‖ ≤ 1 / 16} = (fun z i => ⟪v i, z⟫_ℝ) ⁻¹' A := by
    ext z
    have hs : (∑ i, (⟪v i, z⟫_ℝ - c i) ^ 2) = ‖T z - u‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs, inner_sub_right, hcoords, c] using
        b.sum_sq_norm_inner (T z - u)
    change ‖T z - u‖ ≤ 1 / 16 ↔ (∑ i, (⟪v i, z⟫_ℝ - c i) ^ 2) ≤ 1 / 256
    rw [hs]
    constructor <;> intro hh <;> nlinarith [norm_nonneg (T z - u)]
  rw [he, ← map_measureReal_apply (by fun_prop) hA, gaussian_orthogonal_coordinates v horth]
  exact diagonalGaussian_smallBall_on (fun _ => 0) c _ S ha hS hv

end NCBall
