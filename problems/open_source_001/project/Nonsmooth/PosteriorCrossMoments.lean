import Nonsmooth.IndependentInnerProduct

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace H] {k : ℕ}

def posteriorCenteredRowMean (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (i : Fin k) (h : H) : E :=
  ∫ a : Fin k → E, (a i - ∫ b : Fin k → E, b i ∂Q) ∂condDistrib id X Q h

theorem posterior_rows_memLp_two (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q) :
    ∀ᵐ h ∂Q.map X, ∀ i, MemLp (fun a : Fin k → E => a i) 2 (condDistrib id X Q h) := by
  apply ae_all_iff.mpr
  intro i
  have hi := (memLp_two_iff_integrable_sq_norm (hLp i).aestronglyMeasurable).mp (hLp i)
  have hipair : Integrable (fun p : H × (Fin k → E) => ‖p.2 i‖ ^ 2) (Q.map (fun a => (X a, a))) :=
    hi.comp_snd_map_prodMk X
  have hk := hipair.condDistrib_ae_map (Y := id) aemeasurable_id
  filter_upwards [hk] with h hh
  exact (memLp_two_iff_integrable_sq_norm (measurable_pi_apply i).aestronglyMeasurable).mpr hh

/-- Conditional independence factors the cross moment of actual posterior row
means; integrating it recovers the original cross moment. -/
theorem posterior_centered_cross_moment (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q)
    (hpost : ∀ᵐ h ∂Q.map X, iIndepFun (fun i (a : Fin k → E) => a i) (condDistrib id X Q h))
    (i j : Fin k) (hij : i ≠ j) :
    Integrable (fun h => ⟪posteriorCenteredRowMean Q X i h, posteriorCenteredRowMean Q X j h⟫_ℝ) (Q.map X) ∧
      (∫ h, ⟪posteriorCenteredRowMean Q X i h, posteriorCenteredRowMean Q X j h⟫_ℝ ∂Q.map X) =
        ∫ a : Fin k → E, ⟪a i - ∫ b : Fin k → E, b i ∂Q, a j - ∫ b : Fin k → E, b j ∂Q⟫_ℝ ∂Q := by
  let Fi : (Fin k → E) → E := fun a => a i - ∫ b : Fin k → E, b i ∂Q
  let Fj : (Fin k → E) → E := fun a => a j - ∫ b : Fin k → E, b j ∂Q
  let f : (Fin k → E) → ℝ := fun a => ⟪Fi a, Fj a⟫_ℝ
  have hFi : Measurable Fi := (measurable_pi_apply i).sub measurable_const
  have hFj : Measurable Fj := (measurable_pi_apply j).sub measurable_const
  have hfi : MemLp Fi 2 Q := (hLp i).sub (memLp_const _)
  have hfj : MemLp Fj 2 Q := (hLp j).sub (memLp_const _)
  have hf : Integrable f Q := integrable_inner_of_memLp hfi hfj
  have hfm : Measurable f := (continuous_inner.measurable.comp (hFi.prodMk hFj))
  have hpair : Integrable (fun p : H × (Fin k → E) => f p.2) (Q.map (fun a => (X a, a))) :=
    hf.comp_snd_map_prodMk X
  have hout := hpair.integral_condDistrib_map (Y := id) aemeasurable_id
  have hfact : (fun h => ∫ a, f a ∂condDistrib id X Q h) =ᵐ[Q.map X]
      (fun h => ⟪posteriorCenteredRowMean Q X i h, posteriorCenteredRowMean Q X j h⟫_ℝ) := by
    filter_upwards [hpost, posterior_rows_memLp_two Q X hLp] with h hI hL
    have hind := (hI.indepFun hij).comp
      (show Measurable (fun z : E => z - ∫ b : Fin k → E, b i ∂Q) from measurable_id.sub measurable_const)
      (show Measurable (fun z : E => z - ∫ b : Fin k → E, b j ∂Q) from measurable_id.sub measurable_const)
    exact independent_integral_inner _ Fi Fj hind ((hL i).sub (memLp_const _)) ((hL j).sub (memLp_const _))
  have hint : (∫ h, ∫ a, f a ∂condDistrib id X Q h ∂Q.map X) = ∫ a, f a ∂Q := by
    have hjoint : Integrable (fun p : H × (Fin k → E) => f p.2) ((Q.map X) ⊗ₘ condDistrib id X Q) := by
      rw [compProd_map_condDistrib aemeasurable_id]
      exact hpair
    rw [← Measure.integral_compProd hjoint, compProd_map_condDistrib aemeasurable_id]
    exact integral_map_of_stronglyMeasurable (hX.prodMk measurable_id) (hfm.comp measurable_snd).stronglyMeasurable
  exact ⟨hout.congr hfact, (integral_congr_ae hfact).symm.trans hint⟩

theorem posterior_centered_cross_zero (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q)
    (hprior : iIndepFun (fun i (a : Fin k → E) => a i) Q)
    (hpost : ∀ᵐ h ∂Q.map X, iIndepFun (fun i (a : Fin k → E) => a i) (condDistrib id X Q h))
    (i j : Fin k) (hij : i ≠ j) :
    (∫ h, ⟪posteriorCenteredRowMean Q X i h, posteriorCenteredRowMean Q X j h⟫_ℝ ∂Q.map X) = 0 := by
  rw [(posterior_centered_cross_moment Q X hX hLp hpost i j hij).2]
  exact independent_centered_inner_zero Q _ _ (hprior.indepFun hij) (hLp i) (hLp j)

end
end Nonsmooth
