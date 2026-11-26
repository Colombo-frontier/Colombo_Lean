import RandomizedFO2003.SpectralCascade
import RandomizedFO2003.CascadeDerivativeBounds

namespace RandomizedFO2003.SpectralCoordinates

theorem direction_norm_le {J : ℕ} (K : Fin J → ℕ) (u : BlockSpace K) (r : Fin J → ℝ) :
    ‖direction K u r‖ ≤ 1 := by
  by_cases hz : diagonal K r u = 0
  · simp [direction, hz]
  · have hn : ‖diagonal K r u‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [direction, norm_smul, hn]

end RandomizedFO2003.SpectralCoordinates

namespace RandomizedFO2003.Cascade

noncomputable def cascadeSecondConstant : ℝ := forceScaleConstant 2 + 2 * couplingDerivativeConstant 2
noncomputable def cascadeThirdConstant : ℝ := forceScaleConstant 3 + 2 * couplingDerivativeConstant 3

theorem cascadeSecondConstant_pos : 0 < cascadeSecondConstant :=
  add_pos (forceScaleConstant_pos 2) (mul_pos (by norm_num) (couplingDerivativeConstant_pos 2))

theorem cascadeThirdConstant_pos : 0 < cascadeThirdConstant :=
  add_pos (forceScaleConstant_pos 3) (mul_pos (by norm_num) (couplingDerivativeConstant_pos 3))

end RandomizedFO2003.Cascade

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates Cascade Primitives

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

theorem cascade_direction_norm_le (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (i : Fin (N + 1)) :
    ‖(S.cascade K N U u h).a i‖ ≤ 1 := by
  change ‖U i (direction K (u i) S.residual)‖ ≤ 1
  rw [(U i).norm_map]
  exact direction_norm_le K (u i) S.residual

theorem cascade_rhs_norm_le (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h : ℝ} (hh : 0 < h)
    (hu : ∀ i, ‖u i‖ ≤ 1) (i : Fin (N + 1)) : ‖(S.cascade K N U u h).b i‖ ≤ h := by
  change ‖U i (h • u i)‖ ≤ h
  rw [(U i).norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  exact mul_le_of_le_one_right hh.le (hu i)

/-- The complete global Hessian bound for the actual cascade. Only unit-ball
support is used, so no good-weight or algorithm-dependent event is needed. -/
theorem cascade_second_derivative_bound (hγ : 0 < γ) (hL : 0 ≤ L)
    (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h : ℝ} (hh : 0 < h) (hu : ∀ i, ‖u i‖ ≤ 1)
    (x : BlockProduct (N + 1) (BlockSpace K)) :
    ‖iteratedFDeriv ℝ 2 (S.cascade K N U u h).energy x‖ ≤ L + cascadeSecondConstant * γ := by
  let d := S.cascade K N U u h
  have ha := S.cascade_direction_norm_le K N U u h
  have hb := S.cascade_rhs_norm_le K N U u hh hu
  have hforce (y : BlockSpace K) : ‖iteratedFDeriv ℝ 2 (d.force 0) y‖ ≤ forceScaleConstant 2 * γ := by
    apply (scaled_forcing_derivative_bound 2 (d.b 0) hh hγ (hb 0) y).trans_eq
    field_simp
    ring
  have hedge (j : Fin N) (p : BlockSpace K × BlockSpace K) :
      ‖iteratedFDeriv ℝ 2 (d.edgeFunction j) p‖ ≤ couplingDerivativeConstant 2 * γ :=
    localCoupling_second_derivative_bound (d.a j.castSucc) (d.b j.succ) (ha j.castSucc)
      hh hγ (hb j.succ) p
  apply (d.energy_second_derivative_bound (S.cascade_operator_selfAdjoint K N U u h) hL
    (mul_nonneg (couplingDerivativeConstant_pos 2).le hγ.le)
    (S.cascade_operator_norm_le hγ.le hL K N U u h) hforce hedge x).trans_eq
  unfold cascadeSecondConstant
  ring

/-- The complete global third derivative bound, independent of both block
dimension and block count. -/
theorem cascade_third_derivative_bound (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h : ℝ} (hh : 0 < h) (hu : ∀ i, ‖u i‖ ≤ 1)
    (x : BlockProduct (N + 1) (BlockSpace K)) :
    ‖iteratedFDeriv ℝ 3 (S.cascade K N U u h).energy x‖ ≤ cascadeThirdConstant * γ ^ 2 / h := by
  let d := S.cascade K N U u h
  have ha := S.cascade_direction_norm_le K N U u h
  have hb := S.cascade_rhs_norm_le K N U u hh hu
  have hforce (y : BlockSpace K) :
      ‖iteratedFDeriv ℝ 3 (d.force 0) y‖ ≤ forceScaleConstant 3 * γ ^ 2 / h := by
    apply (scaled_forcing_derivative_bound 3 (d.b 0) hh hγ (hb 0) y).trans_eq
    field_simp
    ring
  have hedge (j : Fin N) (p : BlockSpace K × BlockSpace K) :
      ‖iteratedFDeriv ℝ 3 (d.edgeFunction j) p‖ ≤ couplingDerivativeConstant 3 * γ ^ 2 / h :=
    localCoupling_third_derivative_bound (d.a j.castSucc) (d.b j.succ) (ha j.castSucc)
      hh hγ (hb j.succ) p
  apply (d.energy_third_derivative_bound (S.cascade_operator_selfAdjoint K N U u h)
    (by have hc := (couplingDerivativeConstant_pos 3).le; positivity) hforce hedge x).trans_eq
  unfold cascadeThirdConstant
  ring

theorem cascade_gradient_lipschitz (hγ : 0 < γ) (hL : 0 ≤ L)
    (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h : ℝ} (hh : 0 < h) (hu : ∀ i, ‖u i‖ ≤ 1)
    (x y : BlockProduct (N + 1) (BlockSpace K)) :
    ‖gradient (S.cascade K N U u h).energy x - gradient (S.cascade K N U u h).energy y‖ ≤
      (L + cascadeSecondConstant * γ) * ‖x - y‖ :=
  RandomizedFO2003.Calculus.gradient_lipschitz_of_second_bound
    ((S.cascade K N U u h).energy_contDiff 2)
    (S.cascade_second_derivative_bound hγ hL K N U u hh hu) x y

theorem cascade_hessian_lipschitz (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h : ℝ} (hh : 0 < h) (hu : ∀ i, ‖u i‖ ≤ 1)
    (x y : BlockProduct (N + 1) (BlockSpace K)) :
    ‖fderiv ℝ (gradient (S.cascade K N U u h).energy) x -
      fderiv ℝ (gradient (S.cascade K N U u h).energy) y‖ ≤
      (cascadeThirdConstant * γ ^ 2 / h) * ‖x - y‖ :=
  RandomizedFO2003.Calculus.hessian_lipschitz_of_third_bound
    ((S.cascade K N U u h).energy_contDiff 3)
    (S.cascade_third_derivative_bound hγ K N U u hh hu) x y

end RandomizedFO2003.FiniteSpectralDesign
