import Nonsmooth.SoftInequalityPotential
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def softGaussianDamping (n : ℕ) (x : E) : ℝ :=
  Real.exp (-(‖x‖ ^ 2 / ((n : ℝ) + 1)))

theorem softGaussianDamping_pos (n : ℕ) (x : E) : 0 < softGaussianDamping n x := Real.exp_pos _

theorem softGaussianDamping_le_one (n : ℕ) (x : E) : softGaussianDamping n x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity))

theorem softGaussianDamping_contDiff (n : ℕ) : ContDiff ℝ ⊤ (softGaussianDamping (E := E) n) := by
  exact Real.contDiff_exp.comp (((contDiff_norm_sq ℝ).div_const ((n : ℝ) + 1)).neg)

theorem softGaussianDamping_tendsto (x : E) :
    Tendsto (fun n => softGaussianDamping n x) atTop (𝓝 (1 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => -(‖x‖ ^ 2 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, neg_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (‖x‖ ^ 2)).neg
  simpa only [softGaussianDamping, mul_one_div, Real.exp_zero, Function.comp_def] using
    (Real.continuous_exp.tendsto 0).comp h

variable [Fintype ι]

def strictSoftInequalityWeight (f : ι → E → ℝ) (n : ℕ) (x : E) : ℝ :=
  softGaussianDamping n x * softInequalityWeight f n x

theorem strictSoftInequalityWeight_bounds (f : ι → E → ℝ) (n : ℕ) (x : E) :
    0 < strictSoftInequalityWeight f n x ∧ strictSoftInequalityWeight f n x ≤ 1 := by
  exact ⟨mul_pos (softGaussianDamping_pos n x) (softInequalityWeight_pos f n x),
    mul_le_one₀ (softGaussianDamping_le_one n x) (softInequalityWeight_pos f n x).le
      (softInequalityWeight_le_one f n x)⟩

theorem strictSoftInequalityWeight_contDiff (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ ⊤ (f i)) (n : ℕ) :
    ContDiff ℝ ⊤ (strictSoftInequalityWeight f n) :=
  (softGaussianDamping_contDiff n).mul (softInequalityWeight_contDiff f hf n)

theorem strictSoftInequalityWeight_ae_tendsto [MeasurableSpace E] (μ : Measure E)
    (f : ι → E → ℝ) (hzero : ∀ i, μ {x | f i x = 0} = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n => strictSoftInequalityWeight f n x) atTop
      (𝓝 ((softInequalityRegion f).indicator (fun _ => (1 : ℝ)) x)) := by
  filter_upwards [softInequalityWeight_ae_tendsto μ f hzero] with x hx
  simpa only [strictSoftInequalityWeight, one_mul] using (softGaussianDamping_tendsto x).mul hx

theorem strictSoftInequalityWeight_potential (ρ : ℝ) (f : ι → E → ℝ) (n : ℕ) (x : E) :
    Real.exp (-(ρ / 2 * ‖x‖ ^ 2)) * strictSoftInequalityWeight f n x =
      Real.exp (-((ρ + 2 / ((n : ℝ) + 1)) / 2 * ‖x‖ ^ 2 + softInequalityPenalty f n x)) := by
  rw [strictSoftInequalityWeight, softGaussianDamping, softInequalityWeight_eq_exp,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem strictSoftInequalityPotential_strongConvex (ρ : ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ConvexOn ℝ univ (f i)) (n : ℕ) :
    StrongConvexOn univ (ρ + 2 / ((n : ℝ) + 1))
      (fun x : E => (ρ + 2 / ((n : ℝ) + 1)) / 2 * ‖x‖ ^ 2 + softInequalityPenalty f n x) := by
  apply softInequalityPotential_strongConvex _ _ ?_ hf n
  apply strongConvexOn_iff_convex.mpr
  simp only [sub_self]
  exact convexOn_const 0 convex_univ

end
end Nonsmooth
