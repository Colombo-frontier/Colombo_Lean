import Bilevel.Bowl
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # A necessary gradient budget for the manuscript's radial wrapper

On a unit ray in the kernel of the frame projection, the chain and residual
are constant. The derivative of the radial wrapper at distance R is νR/√2.
Consequently a global gradient bound C forces νR ≤ √2 C. This necessary
condition is proved without adding it to any manuscript theorem statement.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace Bilevel.WrapperBudget

def radial (ν R t : ℝ) : ℝ := ν * R ^ 2 * (Real.sqrt (1 + (t / R) ^ 2) - 1)

theorem radial_derivative_at_radius (ν R : ℝ) (hR : 0 < R) :
    HasDerivAt (radial ν R) (ν * R / Real.sqrt 2) R := by
  have hi : HasDerivAt (fun t : ℝ => t / R) (1 / R) R := (hasDerivAt_id R).div_const R
  have h := ((Bowl.hasDerivAt_value 1 (R / R)).comp (h := fun t : ℝ => t / R) R hi).const_mul (ν * R ^ 2)
  convert h using 1
  · funext t
    simp [radial, Bowl.value]
  · simp only [Bowl.slope, div_self hR.ne', one_mul, one_pow, one_add_one_eq_two]
    field_simp
    ring

theorem derivative_budget (ν R C K : ℝ) (hν : 0 ≤ ν) (hR : 0 < R)
    (f : ℝ → ℝ) (hf : ∀ t, f t = K + radial ν R t)
    (hbound : |deriv f R| ≤ C) : ν * R ≤ Real.sqrt 2 * C := by
  have he : f = fun t => K + radial ν R t := funext hf
  have hd := (radial_derivative_at_radius ν R hR).const_add K
  rw [he, hd.deriv, abs_of_nonneg (by positivity)] at hbound
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have h := (div_le_iff₀ hs).mp hbound
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_budget_on_ray (ν R C K : ℝ) (hν : 0 ≤ ν) (hR : 0 < R)
    (f : E → ℝ) (w df : E) (hw : ‖w‖ = 1)
    (hf : HasGradientAt f df (R • w))
    (hray : ∀ t : ℝ, f (t • w) = K + radial ν R t)
    (hbound : ‖df‖ ≤ C) : ν * R ≤ Real.sqrt 2 * C := by
  apply derivative_budget ν R C K hν hR (fun t => f (t • w)) hray
  have hd := hf.hasFDerivAt.comp_hasDerivAt R ((hasDerivAt_id R).smul_const w)
  simp only [Function.comp_def, id_eq, one_smul] at hd
  rw [hd.deriv]
  simpa [InnerProductSpace.toDual_apply, hw] using
    (abs_real_inner_le_norm df w).trans (by simpa [hw] using hbound)

def compression (R : ℝ) (u : E) : E :=
  (Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2))⁻¹ • u

def carried {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ν R : ℝ) (A : Z → ℝ) (projection : E →L[ℝ] Z) (u : E) : ℝ :=
  A (projection (compression R u)) + ν * R ^ 2 * (Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) - 1)

omit [CompleteSpace E] in
theorem carried_on_kernel_ray {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ν R : ℝ) (A : Z → ℝ) (projection : E →L[ℝ] Z)
    (w : E) (hw : ‖w‖ = 1) (hker : projection w = 0) (t : ℝ) :
    carried ν R A projection (t • w) = A 0 + radial ν R t := by
  simp [carried, compression, hker, norm_smul, hw, Real.norm_eq_abs, sq_abs, radial, div_pow]

theorem carried_gradient_budget {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ν R C : ℝ) (hν : 0 ≤ ν) (hR : 0 < R)
    (A : Z → ℝ) (projection : E →L[ℝ] Z) (w df : E)
    (hw : ‖w‖ = 1) (hker : projection w = 0)
    (hf : HasGradientAt (carried ν R A projection) df (R • w)) (hb : ‖df‖ ≤ C) :
    ν * R ≤ Real.sqrt 2 * C :=
  gradient_budget_on_ray ν R C (A 0) hν hR _ w df hw hf
    (carried_on_kernel_ray ν R A projection w hw hker) hb

theorem normalized_radius_necessary (η₀ η K β T L C : ℝ)
    (hL : 0 < L) (h : (η₀ * η * L) * (K * β * Real.sqrt T) ≤ Real.sqrt 2 * (C * L)) :
    η₀ * η * K * β * Real.sqrt T ≤ Real.sqrt 2 * C := by
  nlinarith [hL]

theorem unbounded_chain_radius (A C : ℝ) (hA : 0 < A) :
    ∃ T : ℕ, 0 < T ∧ Real.sqrt 2 * C < A * Real.sqrt T := by
  obtain ⟨T, hT⟩ := exists_nat_gt ((Real.sqrt 2 * C / A) ^ 2)
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt (sq_nonneg _) hT
  have hs : Real.sqrt 2 * C / A < Real.sqrt T := Real.lt_sqrt_of_sq_lt hT
  refine ⟨T, by exact_mod_cast hT0, ?_⟩
  have h := (div_lt_iff₀ hA).mp hs
  nlinarith

/-- A fixed global gradient bound cannot hold for these wrapped rays for all
chain lengths. This is a necessary-budget obstruction, not a replacement
assumption for the manuscript's lower theorem. -/
theorem no_uniform_wrapper_budget (ν K β C : ℝ)
    (hν : 0 < ν) (hK : 0 < K) (hβ : 0 < β) :
    ∃ T : ℕ, 0 < T ∧ ∀ (f : E → ℝ) (w df : E) (c : ℝ), ‖w‖ = 1 →
      (∀ t : ℝ, f (t • w) = c + radial ν (K * β * Real.sqrt T) t) →
      HasGradientAt f df ((K * β * Real.sqrt T) • w) → C < ‖df‖ := by
  obtain ⟨T, hT, hexceed⟩ := unbounded_chain_radius (ν * K * β) C (by positivity)
  refine ⟨T, hT, ?_⟩
  intro f w df c hw hray hf
  have hR : 0 < K * β * Real.sqrt T := by positivity
  by_contra h
  have hb := gradient_budget_on_ray ν (K * β * Real.sqrt T) C c hν.le hR
    f w df hw hf hray (le_of_not_gt h)
  nlinarith

end Bilevel.WrapperBudget
