import NoisyZO.Model

/-!
# Hard-family admissibility interface

This packages the analytic obligations for the radial cutoff into exactly the
fields of the normalized class.  The constructor itself is proved here; the
remaining radial-profile module must discharge these obligations for the
explicit cutoff in Appendix A.
-/

open scoped InnerProductSpace Gradient

namespace NoisyZO

noncomputable section

structure HardAnalyticCertificate (o : SmoothnessOrder) (d : ℕ)
    (cutoff : Point d → ℝ) (ρ : ℝ) (s : Fin d → ℝ) where
  smooth : ContDiff ℝ o.k (hardValue cutoff ρ s)
  center_mem : ‖hardCenter ρ s‖ ≤ 1
  strong : ∀ x y,
    hardValue cutoff ρ s x +
      ⟪∇ (hardValue cutoff ρ s) x, y - x⟫_ℝ +
        (1 / 2 : ℝ) * ‖y - x‖ ^ 2 ≤ hardValue cutoff ρ s y
  gradient_lipschitz : ∀ x y,
    ‖∇ (hardValue cutoff ρ s) x - ∇ (hardValue cutoff ρ s) y‖ ≤
      3 * ‖x - y‖
  higher_holder : ∀ x y,
    ‖iteratedFDeriv ℝ o.k (hardValue cutoff ρ s) x -
        iteratedFDeriv ℝ o.k (hardValue cutoff ρ s) y‖ ≤
      ‖x - y‖ ^ o.alpha
  center_stationary : ∇ (hardValue cutoff ρ s) (hardCenter ρ s) = 0

def hardNormalizedObjective {o : SmoothnessOrder} {d : ℕ}
    (cutoff : Point d → ℝ) (ρ : ℝ) (s : Fin d → ℝ)
    (cert : HardAnalyticCertificate o d cutoff ρ s) :
    NormalizedObjective o d where
  f := hardValue cutoff ρ s
  minimizer := hardCenter ρ s
  smooth := cert.smooth
  minimizer_mem := cert.center_mem
  strong := cert.strong
  gradient_lipschitz := cert.gradient_lipschitz
  higher_holder := cert.higher_holder
  minimizer_stationary := cert.center_stationary

theorem hardNormalizedObjective_exact_minimizer
    {o : SmoothnessOrder} {d : ℕ}
    (cutoff : Point d → ℝ) (ρ : ℝ) (s : Fin d → ℝ)
    (cert : HardAnalyticCertificate o d cutoff ρ s) :
    (∀ y, hardValue cutoff ρ s (hardCenter ρ s) ≤ hardValue cutoff ρ s y) ∧
      (∀ y, hardValue cutoff ρ s y = hardValue cutoff ρ s (hardCenter ρ s) →
        y = hardCenter ρ s) :=
  (hardNormalizedObjective cutoff ρ s cert).minimizer_is_unique

/-- Common-quadratic support statement for every family member. -/
theorem hardNormalizedObjective_common_outside
    {o : SmoothnessOrder} {d : ℕ}
    (cutoff : Point d → ℝ) (ρ : ℝ) (s : Fin d → ℝ)
    (cert : HardAnalyticCertificate o d cutoff ρ s)
    {x : Point d} (hcut : cutoff x = 0) :
    (hardNormalizedObjective cutoff ρ s cert).f x = ‖x‖ ^ 2 :=
  hardValue_eq_norm_sq_of_cutoff_zero cutoff ρ s x hcut

end

end NoisyZO
