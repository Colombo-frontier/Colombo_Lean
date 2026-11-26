import Mathlib.Probability.Variance

/-! Moment convergence under genuine L2 convergence, used to state the
smooth-approximation extension of Gaussian Poincare in its usual topology. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {Ω V : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem integral_norm_square_eq_L2_norm {f : Ω → V} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  calc
    _ = ∫ x, ⟪(hf.toLp f) x, (hf.toLp f) x⟫_ℝ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    _ = ⟪hf.toLp f, hf.toLp f⟫_ℝ := rfl
    _ = _ := real_inner_self_eq_norm_sq _

theorem integral_norm_square_tendsto_of_L2 {F : ℕ → Ω → V} {f : Ω → V}
    (hF : ∀ n, MemLp (F n) 2 μ) (hf : MemLp f 2 μ)
    (hconv : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => ∫ x, ‖F n x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  have he : (fun n => ∫ x, ‖F n x‖ ^ 2 ∂μ) = fun n => ‖(hF n).toLp (F n)‖ ^ 2 :=
    funext (fun n => integral_norm_square_eq_L2_norm (hF n))
  rw [he, integral_norm_square_eq_L2_norm hf]
  exact hconv.norm.pow 2

variable [IsFiniteMeasure μ]

theorem integral_eq_L2_inner_one {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) =
      ⟪(memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ)), hf.toLp f⟫_ℝ := by
  change _ = ∫ x, ⟪((memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp
    (fun _ : Ω => (1 : ℝ))) x, (hf.toLp f) x⟫_ℝ ∂μ
  apply integral_congr_ae
  filter_upwards [(memLp_const (μ := μ) (p := 2) (1 : ℝ)).coeFn_toLp, hf.coeFn_toLp] with x h1 hx
  rw [h1, hx]
  simp

theorem integral_tendsto_of_L2 {F : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hf : MemLp f 2 μ)
    (hconv : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have he : (fun n => ∫ x, F n x ∂μ) = fun n =>
      ⟪(memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ)),
        (hF n).toLp (F n)⟫_ℝ :=
    funext (fun n => integral_eq_L2_inner_one (hF n))
  rw [he, integral_eq_L2_inner_one hf]
  exact tendsto_const_nhds.inner hconv

end GradientHessian.GaussianConcentration
