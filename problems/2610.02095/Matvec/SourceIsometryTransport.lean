import Matvec.PolicyOracleMap
import Matvec.SpectralBridge

/-! Exact zero-cost transport of an ordinary source solver between finite
Euclidean coordinate systems. Public right-hand sides, outputs, and oracle
queries are transported by the same fixed linear isometry. -/
namespace Matvec
open MeasureTheory MeasurableSimulation
open scoped InnerProductSpace
noncomputable section

variable {E F Seed : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace Seed] {K : ℕ}

def conjugateSource (e : F ≃ₗᵢ[ℝ] E) (H : F →L[ℝ] F) : E →L[ℝ] E :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (H.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem conjugateSource_apply (e : F ≃ₗᵢ[ℝ] E) (H : F →L[ℝ] F) (x : E) :
    conjugateSource e H x = e (H (e.symm x)) := rfl

theorem conjugateSource_symmetric (e : F ≃ₗᵢ[ℝ] E) (H : F →L[ℝ] F)
    (hH : H.toLinearMap.IsSymmetric) : (conjugateSource e H).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪e (H (e.symm x)), y⟫_ℝ = ⟪x, e (H (e.symm y))⟫_ℝ
  rw [← e.symm.inner_map_map (e (H (e.symm x))) y,
    ← e.symm.inner_map_map x (e (H (e.symm y)))]
  simp only [e.symm_apply_apply]
  exact hH (e.symm x) (e.symm y)

theorem conjugateSource_expansion (e : F ≃ₗᵢ[ℝ] E) (H : F →L[ℝ] F)
    (hH : ∀ x, ‖x‖ ≤ ‖H x‖) : ∀ x, ‖x‖ ≤ ‖conjugateSource e H x‖ := by
  intro x
  simpa only [conjugateSource_apply, e.norm_map, e.symm.norm_map] using hH (e.symm x)

theorem conjugateSource_norm_le (e : F ≃ₗᵢ[ℝ] E) (H : F →L[ℝ] F) :
    ‖conjugateSource e H‖ ≤ ‖H‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [conjugateSource_apply, e.norm_map, e.symm.norm_map] using H.le_opNorm (e.symm x)

def transportSourcePolicy (e : F ≃ₗᵢ[ℝ] E)
    (base : Policy E E E K (E × Seed)) : Policy F F F K (F × Seed) :=
  ((base.mapOracle e.symm e e.symm.continuous.measurable e.continuous.measurable).mapOutput
    (fun _ x => e.symm x) (e.symm.continuous.measurable.comp measurable_snd)).seedMap
      (fun p : F × Seed => (e p.1, p.2))
      ((e.continuous.measurable.comp measurable_fst).prodMk measurable_snd)

theorem transportSourcePolicy_run (e : F ≃ₗᵢ[ℝ] E)
    (base : Policy E E E K (E × Seed)) (H : F →L[ℝ] F) (r : F) (s : Seed) :
    (transportSourcePolicy e base).run H (r, s) =
      e.symm (base.run (conjugateSource e H) (e r, s)) := by
  rw [transportSourcePolicy, Policy.seedMap_run, Policy.mapOutput_run, Policy.mapOracle_run]
  rfl

theorem transportSourcePolicy_residual (e : F ≃ₗᵢ[ℝ] E)
    (base : Policy E E E K (E × Seed)) (H : F →L[ℝ] F) (r : F) (s : Seed) :
    ‖H ((transportSourcePolicy e base).run H (r, s)) - r‖ =
      ‖conjugateSource e H (base.run (conjugateSource e H) (e r, s)) - e r‖ := by
  rw [transportSourcePolicy_run, ← e.norm_map]
  rw [map_sub]
  rfl

theorem transportSourcePolicy_success (e : F ≃ₗᵢ[ℝ] E)
    (base : Policy E E E K (E × Seed)) (μ : Measure Seed) (L : ℝ)
    (hsuccess : ∀ H : E →L[ℝ] E, H.toLinearMap.IsSymmetric →
      (∀ w, ‖w‖ ≤ ‖H w‖) → ‖H‖ ≤ L →
      ∀ r, 3 / 5 ≤ μ.real {s | ‖H (base.run H (r, s)) - r‖ ≤ ‖r‖ / 2}) :
    ∀ H : F →L[ℝ] F, H.toLinearMap.IsSymmetric →
      (∀ w, ‖w‖ ≤ ‖H w‖) → ‖H‖ ≤ L →
      ∀ r, 3 / 5 ≤ μ.real
        {s | ‖H ((transportSourcePolicy e base).run H (r, s)) - r‖ ≤ ‖r‖ / 2} := by
  intro H hsym hexp hnorm r
  have h := hsuccess (conjugateSource e H) (conjugateSource_symmetric e H hsym)
    (conjugateSource_expansion e H hexp) ((conjugateSource_norm_le e H).trans hnorm) (e r)
  simpa only [transportSourcePolicy_residual, e.norm_map] using h

end
end Matvec
