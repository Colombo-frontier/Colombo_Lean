import Nonsmooth.OrthogonalHaar
import Nonsmooth.FrameGeometry
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Metric Filter Function
open scoped Topology InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

instance unitDirectionCompactSpace : CompactSpace (UnitDirection E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E) 1).of_isClosed_subset
    (isClosed_eq continuous_norm continuous_const)
  intro u hu
  simpa only [mem_closedBall, dist_zero_right] using (show ‖u‖ ≤ 1 from hu.le)

instance unitDirectionBorelSpace : BorelSpace (UnitDirection E) :=
  Subtype.borelSpace {u : E | ‖u‖ = 1}

theorem orthogonalHaar_orbit_integral_eq {u v : E} (hn : ‖u‖ = ‖v‖) (f : E → ℝ) :
    (∫ Q : OrthogonalTransform E, f (Q.val u) ∂orthogonalHaar E) =
      ∫ Q : OrthogonalTransform E, f (Q.val v) ∂orthogonalHaar E := by
  let R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (u - v))ᗮ.reflection
  let P : OrthogonalTransform E := Unitary.linearIsometryEquiv.symm R
  have hP : P.val u = v := Submodule.reflection_sub hn
  have h := orthogonalHaar_integral_mul_right P (fun Q : OrthogonalTransform E => f (Q.val u))
  change (∫ Q : OrthogonalTransform E, f (Q.val (P.val u)) ∂orthogonalHaar E) = _ at h
  rw [hP] at h
  exact h.symm

/-- Averaging any fixed unit vector under the actual orthogonal Haar probability gives exactly
the manuscript's actual spherical average, proved by invariance and compact Fubini. -/
theorem orthogonalHaar_sphere_integral {u : E} (hu : ‖u‖ = 1) {f : E → ℝ} (hf : Continuous f) :
    (∫ Q : OrthogonalTransform E, f (Q.val u) ∂orthogonalHaar E) =
      ∫ z : E, f z ∂sphericalLaw E := by
  have hjoint : Continuous (fun p : OrthogonalTransform E × UnitDirection E => f (p.1.val p.2.val)) :=
    hf.comp (orthogonalAction_continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hi : Integrable (fun p : OrthogonalTransform E × UnitDirection E => f (p.1.val p.2.val))
      ((orthogonalHaar E).prod (unitSphereLaw E)) :=
    hjoint.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hfirst (Q : OrthogonalTransform E) :
      (∫ w : UnitDirection E, f (Q.val w.val) ∂unitSphereLaw E) =
        ∫ z : E, f z ∂sphericalLaw E := by
    let e : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv Q
    have he := (sphericalLaw_measurePreserving e).integral_comp
      e.toMeasurableEquiv.measurableEmbedding f
    exact (unitSphereLaw_integral (fun z : E => f (Q.val z))).trans he
  have hsecond (w : UnitDirection E) :
      (∫ Q : OrthogonalTransform E, f (Q.val w.val) ∂orthogonalHaar E) =
        ∫ Q : OrthogonalTransform E, f (Q.val u) ∂orthogonalHaar E :=
    orthogonalHaar_orbit_integral_eq (w.property.trans hu.symm) f
  have hswap := integral_integral_swap (μ := orthogonalHaar E) (ν := unitSphereLaw E)
    (f := fun (Q : OrthogonalTransform E) (w : UnitDirection E) => f (Q.val w.val)) hi
  simp_rw [hfirst, hsecond] at hswap
  simpa only [integral_const, probReal_univ, one_smul] using hswap.symm

theorem orthogonalHaar_action_integrable {f : E → ℝ} (hf : Continuous f) (u : E) :
    Integrable (fun Q : OrthogonalTransform E => f (Q.val u)) (orthogonalHaar E) := by
  have hc : Continuous (fun Q : OrthogonalTransform E => f (Q.val u)) :=
    hf.comp (continuous_subtype_val.clm_apply continuous_const)
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

end
end Nonsmooth
