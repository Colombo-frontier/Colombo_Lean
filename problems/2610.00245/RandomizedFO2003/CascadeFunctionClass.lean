import RandomizedFO2003.SpectralSmoothness
import RandomizedFO2003.Model

namespace RandomizedFO2003.Model

theorem inFunctionClass_of_derivative_bounds {d : ℕ} {f : Space d → ℝ}
    {Δ L₁ L₂ : ℝ} (hf : ContDiff ℝ 3 f) (hgap : ∀ x, f 0 - f x ≤ Δ)
    (hsecond : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ L₁)
    (hthird : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ L₂) : InFunctionClass f Δ L₁ L₂ :=
  ⟨hf.of_le (by decide), hgap,
    Calculus.gradient_lipschitz_of_second_bound (hf.of_le (by decide)) hsecond,
    Calculus.hessian_lipschitz_of_third_bound hf hthird⟩

end RandomizedFO2003.Model

namespace RandomizedFO2003.Cascade

open SpectralCoordinates
open scoped BigOperators

variable {J : ℕ}

theorem blockProduct_finrank (K : Fin J → ℕ) (N : ℕ) :
    Module.finrank ℝ (BlockProduct (N + 1) (BlockSpace K)) = (N + 1) * ∑ j, K j := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin (N + 1) → BlockSpace K)).finrank_eq]
  simp [Module.finrank_pi_fintype, BlockSpace]

/-- The dimension and coordinate change depend only on the multiplicities
and block count, before any algorithm or random realization. -/
noncomputable def cascadeCoordinates (K : Fin J → ℕ) (N : ℕ) :
    BlockProduct (N + 1) (BlockSpace K) ≃ₗᵢ[ℝ] Model.Space ((N + 1) * ∑ j, K j) := by
  rw [← blockProduct_finrank K N]
  exact (stdOrthonormalBasis ℝ (BlockProduct (N + 1) (BlockSpace K))).repr

end RandomizedFO2003.Cascade

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates Cascade
open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

noncomputable def cascadeFunction (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) : Model.Space ((N + 1) * ∑ j, K j) → ℝ :=
  (S.cascade K N U u h).energy ∘ (cascadeCoordinates K N).symm

theorem cascadeFunction_contDiff (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (n : ℕ) :
    ContDiff ℝ n (S.cascadeFunction K N U u h) :=
  ((S.cascade K N U u h).energy_contDiff n).comp
    (cascadeCoordinates K N).symm.toContinuousLinearEquiv.contDiff

/-- Membership in the target's exact function class, including the initial
gap and the actual gradient and Hessian inequalities. The three remaining
scalar premises are the explicit smoothness and gap budgets, independent of
the random realization and the algorithm. -/
theorem cascadeFunction_inFunctionClass (hγ : 0 < γ) (hL : 0 ≤ L)
    (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h Δ L₁ L₂ : ℝ} (hh : 0 < h) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hgap : ((N + 1 : ℕ) : ℝ) * forcingAmplitude * (h ^ 2 / γ) ≤ Δ)
    (hsecond : L + cascadeSecondConstant * γ ≤ L₁)
    (hthird : cascadeThirdConstant * γ ^ 2 / h ≤ L₂) :
    Model.InFunctionClass (S.cascadeFunction K N U u h) Δ L₁ L₂ := by
  apply Model.inFunctionClass_of_derivative_bounds (S.cascadeFunction_contDiff K N U u h 3)
  · intro x
    have heq : S.cascadeFunction K N U u h 0 - S.cascadeFunction K N U u h x =
        (S.cascade K N U u h).energy 0 -
        (S.cascade K N U u h).energy ((cascadeCoordinates K N).symm x) := by
      simp only [cascadeFunction, Function.comp_apply, map_zero]
    rw [heq]
    exact (S.cascade_initial_gap_bound hγ K N U u h _).trans hgap
  · intro x
    change ‖iteratedFDeriv ℝ 2 ((S.cascade K N U u h).energy ∘ (cascadeCoordinates K N).symm) x‖ ≤ L₁
    rw [(cascadeCoordinates K N).symm.norm_iteratedFDeriv_comp_right]
    exact (S.cascade_second_derivative_bound hγ hL K N U u hh hu _).trans hsecond
  · intro x
    change ‖iteratedFDeriv ℝ 3 ((S.cascade K N U u h).energy ∘ (cascadeCoordinates K N).symm) x‖ ≤ L₂
    rw [(cascadeCoordinates K N).symm.norm_iteratedFDeriv_comp_right]
    exact (S.cascade_third_derivative_bound hγ K N U u hh hu _).trans hthird

end RandomizedFO2003.FiniteSpectralDesign
