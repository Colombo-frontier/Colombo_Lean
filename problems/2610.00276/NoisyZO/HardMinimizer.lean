import NoisyZO.HardFamily
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Exact center of the hard family

This module formalizes the deterministic minimizer geometry in Lemma 3.2 of
`2401.tex`.  The only analytic input still needed by the final admissibility
module is the strong first-order inequality and stationarity of the displayed
center; once those are available, global minimality and uniqueness are proved
here.
-/

open scoped BigOperators InnerProductSpace

namespace NoisyZO

noncomputable section

def signPoint {d : ℕ} (s : Fin d → ℝ) : Point d :=
  WithLp.toLp 2 s

@[simp] theorem signPoint_apply {d : ℕ} (s : Fin d → ℝ) (i : Fin d) :
    signPoint s i = s i := rfl

theorem real_inner_signPoint {d : ℕ} (s : Fin d → ℝ) (x : Point d) :
    ⟪signPoint s, x⟫_ℝ = signedSum s x := by
  simp [PiLp.inner_apply, signPoint, signedSum, mul_comm]

/-- Candidate minimizer for `‖x‖² - ρ ⟨s,x⟩` in the flat cutoff region. -/
def hardCenter {d : ℕ} (ρ : ℝ) (s : Fin d → ℝ) : Point d :=
  (ρ / 2) • signPoint s

@[simp] theorem hardCenter_apply {d : ℕ} (ρ : ℝ) (s : Fin d → ℝ)
    (i : Fin d) : hardCenter ρ s i = (ρ / 2) * s i := by
  simp [hardCenter]

/-- Completing the square wherever the cutoff is identically one. -/
theorem hardValue_eq_completedSquare {d : ℕ} (cutoff : Point d → ℝ)
    (ρ : ℝ) (s : Fin d → ℝ) (x : Point d) (hcut : cutoff x = 1) :
    hardValue cutoff ρ s x =
      ‖x - hardCenter ρ s‖ ^ 2 - ‖hardCenter ρ s‖ ^ 2 := by
  rw [hardValue, hcut, mul_one, norm_sub_sq_real]
  have hinner : ⟪x, hardCenter ρ s⟫_ℝ = (ρ / 2) * signedSum s x := by
    rw [real_inner_comm]
    rw [hardCenter, real_inner_smul_left, real_inner_signPoint]
  rw [hinner]
  ring

/-- Outside the support of the cutoff every hypothesis is the common
quadratic `‖x‖²`. -/
theorem hardValue_eq_norm_sq_of_cutoff_zero {d : ℕ}
    (cutoff : Point d → ℝ) (ρ : ℝ) (s : Fin d → ℝ) (x : Point d)
    (hcut : cutoff x = 0) :
    hardValue cutoff ρ s x = ‖x‖ ^ 2 := by
  simp [hardValue, hcut]

theorem norm_hardCenter_sq {d : ℕ} (ρ : ℝ) (s : Fin d → ℝ) :
    ‖hardCenter ρ s‖ ^ 2 = (ρ ^ 2 / 4) * ∑ i : Fin d, (s i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [hardCenter_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem norm_hardCenter_sq_of_signs {d : ℕ} (ρ : ℝ) (s : Fin d → ℝ)
    (hs : ∀ i, (s i) ^ 2 = 1) :
    ‖hardCenter ρ s‖ ^ 2 = ρ ^ 2 * d / 4 := by
  rw [norm_hardCenter_sq]
  simp_rw [hs]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

/-- A first-order formulation of `μ`-strong convexity using a supplied
gradient map. -/
def StrongGradientInequality {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : E → ℝ) (grad : E → E) (μ : ℝ) : Prop :=
  ∀ x y, f x + ⟪grad x, y - x⟫_ℝ + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y

/-- A stationary point of a positive strongly convex function is its unique
global minimizer. -/
theorem stationary_unique_minimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : StrongGradientInequality f grad μ) (xstar : E)
    (hstationary : grad xstar = 0) :
    (∀ y, f xstar ≤ f y) ∧
      (∀ y, f y = f xstar → y = xstar) := by
  constructor
  · intro y
    have h := hstrong xstar y
    rw [hstationary, inner_zero_left] at h
    simp only [add_zero] at h
    have hsq : 0 ≤ (μ / 2) * ‖y - xstar‖ ^ 2 := by positivity
    linarith
  · intro y hy
    have h := hstrong xstar y
    rw [hstationary, inner_zero_left] at h
    simp only [add_zero, hy] at h
    have hnorm : ‖y - xstar‖ = 0 := by
      have hsq : ‖y - xstar‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖y - xstar‖]
      nlinarith [norm_nonneg (y - xstar)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Specialization giving the manuscript's exact hard-family minimizer once
the analytic gradient calculation is supplied. -/
theorem hardCenter_unique_minimizer {d : ℕ}
    (cutoff : Point d → ℝ) (ρ : ℝ) (s : Fin d → ℝ)
    (grad : Point d → Point d) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : StrongGradientInequality (hardValue cutoff ρ s) grad μ)
    (hstationary : grad (hardCenter ρ s) = 0) :
    (∀ y, hardValue cutoff ρ s (hardCenter ρ s) ≤ hardValue cutoff ρ s y) ∧
      (∀ y, hardValue cutoff ρ s y = hardValue cutoff ρ s (hardCenter ρ s) →
        y = hardCenter ρ s) :=
  stationary_unique_minimizer (hardValue cutoff ρ s) grad hμ hstrong
    (hardCenter ρ s) hstationary

end

end NoisyZO
