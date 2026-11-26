import RandomizedFO2003.CascadeFunctionClass
import RandomizedFO2003.SpectralStationarity

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates Cascade
open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- The standard-coordinate oracle gradient is exactly the isometric image
of the already verified block gradient. -/
theorem cascadeFunction_gradient (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (x : Model.Space ((N + 1) * ∑ j, K j)) :
    gradient (S.cascadeFunction K N U u h) x =
      cascadeCoordinates K N (gradient (S.cascade K N U u h).energy ((cascadeCoordinates K N).symm x)) := by
  let V := cascadeCoordinates K N
  have hg := RandomizedFO2003.Calculus.hasGradientAt_comp_linear
    V.symm.toContinuousLinearEquiv.toContinuousLinearMap (x := x)
    (((S.cascade K N U u h).energy_contDiff 1).differentiable (by norm_num) (V.symm x)).hasGradientAt
  have hadj : V.symm.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
      V.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_right ℝ
    intro z
    rw [ContinuousLinearMap.adjoint_inner_left]
    change inner (𝕜 := ℝ) y (V.symm z) = inner (𝕜 := ℝ) (V y) z
    simpa only [V.apply_symm_apply] using (V.inner_map_map y (V.symm z)).symm
  rw [hadj] at hg
  exact hg.gradient

theorem cascadeFunction_gradient_norm (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (x : Model.Space ((N + 1) * ∑ j, K j)) :
    ‖gradient (S.cascadeFunction K N U u h) x‖ =
      ‖gradient (S.cascade K N U u h).energy ((cascadeCoordinates K N).symm x)‖ := by
  rw [S.cascadeFunction_gradient K N U u h x, (cascadeCoordinates K N).norm_map]

/-- Near-stationarity for the exact Euclidean function used by
`Model.InFunctionClass` implies the block activation and final residual
properties. Thus the analytic and stationarity chains concern one function. -/
theorem cascadeFunction_stationarity (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h ε : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (hH : 512 * ε ≤ h)
    (hu : ∀ i, ‖u i‖ = 1)
    (hweight : ∀ i j, |SpectralCoordinates.weight K (u i) j - S.weight j| ≤ (1 / 32) * S.weight j)
    (x : Model.Space ((N + 1) * ∑ j, K j))
    (hx : ‖gradient (S.cascadeFunction K N U u h) x‖ ≤ ε) :
    let d := S.cascade K N U u h
    let z := (cascadeCoordinates K N).symm x
    (∀ i, ‖z i‖ ≤ d.B) ∧
    (∀ i, |forcingReadout (d.b i) d.D (z i)| ≤ d.K) ∧
    (∀ i, d.gate i (z i) = 1) ∧
    ‖d.A (Fin.last N) (z (Fin.last N)) - d.b (Fin.last N)‖ ≤ ε := by
  rw [S.cascadeFunction_gradient_norm K N U u h x] at hx
  exact S.cascade_stationarity hγ K N U u hh hε hH hu hweight _ hx

end RandomizedFO2003.FiniteSpectralDesign
