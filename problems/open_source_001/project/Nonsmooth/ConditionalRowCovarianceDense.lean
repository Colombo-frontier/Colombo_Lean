import Nonsmooth.KernelCovarianceMeasurability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E α : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace α] {k : ℕ}

theorem conditional_rows_memLp (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → α) (hX : Measurable X)
    (hL : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q) :
    ∀ᵐ h ∂Q.map X, ∀ i, MemLp (fun a : Fin k → E => a i) 2 (condDistrib id X Q h) := by
  apply ae_all_iff.mpr
  intro i
  have hp : Integrable (fun p : α × (Fin k → E) => ‖p.2 i‖ ^ 2)
      (Q.map (fun a => (X a, a))) := (hL i).norm.integrable_sq.comp_snd_map_prodMk X
  filter_upwards [hp.condDistrib_ae_map (Y := id) aemeasurable_id] with h hh
  change Integrable (fun a : Fin k → E => ‖a i‖ ^ 2) (condDistrib id X Q h) at hh
  exact (memLp_two_iff_integrable_sq_norm (measurable_pi_apply i).aestronglyMeasurable).mpr hh

theorem directional_row_variance_continuous (μ : Measure (Fin k → E)) [IsProbabilityMeasure μ]
    (i : Fin k) (hL : MemLp (fun a : Fin k → E => a i) 2 μ) :
    Continuous (fun v : E => variance (fun a : Fin k → E => ⟪v, a i⟫_ℝ) μ) := by
  let ν := μ.map (fun a => a i)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  have hν : MemLp (fun z : E => z) 2 ν :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mpr hL
  have he : (fun v : E => variance (fun a : Fin k → E => ⟪v, a i⟫_ℝ) μ) =
      fun v : E => variance (fun z : E => ⟪v, z⟫_ℝ) ν := by
    funext v
    exact (variance_map_measurable μ (fun a => a i) (measurable_pi_apply i)
      (fun z : E => ⟪v, z⟫_ℝ) (by fun_prop)).symm
  rw [he]
  exact directional_variance_continuous ν hν

theorem conditional_covariance_from_dense (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → α) (hX : Measurable X)
    (hL : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q)
    (D : Set E) (hD : Dense D) (C : ℝ)
    (hbound : ∀ᵐ h ∂Q.map X, ∀ v ∈ D, ∀ i,
      variance (fun a : Fin k → E => ⟪v, a i⟫_ℝ) (condDistrib id X Q h) ≤ C * ‖v‖ ^ 2) :
    ∀ᵐ h ∂Q.map X, ∀ (v : E) (i : Fin k),
      variance (fun a : Fin k → E => ⟪v, a i⟫_ℝ) (condDistrib id X Q h) ≤ C * ‖v‖ ^ 2 := by
  filter_upwards [conditional_rows_memLp Q X hX hL, hbound] with h hL hb
  intro v i
  have hc : IsClosed {w : E | variance (fun a : Fin k → E => ⟪w, a i⟫_ℝ)
      (condDistrib id X Q h) ≤ C * ‖w‖ ^ 2} :=
    isClosed_le (directional_row_variance_continuous _ i (hL i))
      (continuous_const.mul (continuous_norm.pow 2))
  have hsub := closure_minimal (fun w hw => hb w hw i) hc
  rw [hD.closure_eq] at hsub
  exact hsub (mem_univ v)

end
end Nonsmooth
