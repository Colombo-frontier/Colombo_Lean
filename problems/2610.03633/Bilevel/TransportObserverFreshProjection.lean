import Bilevel.TransportObserverProtectedAngle
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! A scalar Frobenius projection event supplies the fresh-complement angle.
The probability theorem consumes an actual projection second moment; it does
not postulate or manufacture a conditional Haar distribution. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open ProjectionGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem residual_norm_le (W : Submodule ℝ E) (v : E) :
    ‖ProjectionGeometry.residual W v‖ ≤ ‖v‖ := by
  have hh := residual_norm_square W v
  have he : 0 ≤ energy W v := sq_nonneg _
  nlinarith [norm_nonneg v,norm_nonneg (ProjectionGeometry.residual W v)]

/-- The adjoint form of the frame-energy bound. This converts the scalar
Frobenius event into an operator bound for all vectors in the fresh range. -/
theorem projected_frame_range_bound {ι : Type*} [Fintype ι]
    (Q W : Submodule ℝ E) (b : OrthonormalBasis ι ℝ Q) {a : ℝ}
    (henergy : frameEnergy W (fun i => (b i : E)) Finset.univ ≤ a)
    (v : E) (hv : v ∈ Q) : ‖project W v‖ ≤ Real.sqrt a*‖v‖ := by
  let p := project W v
  have hpQ := hard_projection_bound Q W b henergy p (project_mem W v)
  have hi : ‖p‖^2 = ⟪project Q p,v⟫ := by
    have hh := project_inner W v v
    rw [real_inner_self_eq_norm_sq] at hh
    have hhQ := inner_project_mem Q p v hv
    exact hh.symm.trans hhQ
  have hb := (real_inner_le_norm (project Q p) v).trans
    (mul_le_mul_of_nonneg_right hpQ (norm_nonneg v))
  rw [← hi] at hb
  by_cases hp : ‖p‖ = 0
  · change ‖p‖ ≤ Real.sqrt a*‖v‖
    rw [hp]
    positivity
  · have hpp : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)
    change ‖p‖ ≤ Real.sqrt a*‖v‖
    nlinarith

theorem fresh_projection_of_frobenius {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] (Q W : Submodule ℝ E) (b : OrthonormalBasis ι ℝ Q)
    (fresh : F → E) (hQ : ∀ u, fresh u ∈ Q) (hnorm : ∀ u, ‖fresh u‖ ≤ ‖u‖)
    (henergy : frameEnergy W (fun i => (b i : E)) Finset.univ ≤ (1:ℝ)/64) :
    ∀ u, ‖project W (fresh u)‖ ≤ ‖u‖/8 := by
  intro u
  have hh := projected_frame_range_bound Q W b henergy (fresh u) (hQ u)
  have hs : Real.sqrt ((1:ℝ)/64) = 1/8 := by
    rw [show (1:ℝ)/64 = ((1:ℝ)/8)^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/8)]
  rw [hs] at hh
  have hn := mul_le_mul_of_nonneg_left (hnorm u) (by norm_num : (0:ℝ) ≤ 1/8)
  exact hh.trans (by simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using hn)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Markov's step at the exact source threshold. Supplying the conditional
Haar projection moment is a separate theorem, not an independence assumption. -/
theorem fresh_projection_failure_of_moment {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hf : Integrable f ν) {m : ℝ}
    (hm : (∫ ω, f ω ∂ν) ≤ m) :
    ν.real {ω | (1:ℝ)/64 < f ω} ≤ 64*m := by
  have hh := (mul_meas_ge_le_integral_of_nonneg (μ := ν)
    (Filter.Eventually.of_forall hf0) hf ((1:ℝ)/64)).trans hm
  have hp : ν.real {ω | (1:ℝ)/64 ≤ f ω} ≤ 64*m := by nlinarith
  exact (measureReal_mono (μ := ν)
    (show {ω | (1:ℝ)/64 < f ω} ⊆ {ω | (1:ℝ)/64 ≤ f ω} from by
      intro ω h
      change (1:ℝ)/64 < f ω at h
      change (1:ℝ)/64 ≤ f ω
      exact h.le)).trans hp

end Bilevel.TransportObserver
