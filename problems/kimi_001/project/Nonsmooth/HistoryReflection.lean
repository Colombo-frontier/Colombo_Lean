import Nonsmooth.PerpendicularReflection
import Nonsmooth.AdaptiveIsometry
import Nonsmooth.QueryCompletion
import Nonsmooth.ConditionalMoments

open MeasureTheory Function
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

abbrev NonzeroPerpendicular (K : Submodule ℝ E) := {w : E // w ∈ Kᗮ ∧ w ≠ 0}

theorem nonzeroPerpendicular_reflection_continuous (K : Submodule ℝ E) :
    Continuous (fun p : NonzeroPerpendicular K × E => perpendicularReflection p.1.val p.2) := by
  have hw : Continuous (fun p : NonzeroPerpendicular K × E => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hn : ∀ p : NonzeroPerpendicular K × E, ‖p.1.val‖ ^ 2 ≠ 0 :=
    fun p => pow_ne_zero _ (norm_ne_zero_iff.mpr p.1.property.2)
  have hq := (hw.inner continuous_snd).div (hw.norm.pow 2) hn
  have h : Continuous (fun p : NonzeroPerpendicular K × E =>
      -(((2 : ℝ) * (⟪p.1.val, p.2⟫_ℝ / ‖p.1.val‖ ^ 2)) • p.1.val - p.2)) :=
    (((continuous_const.mul hq).smul hw).sub continuous_snd).neg
  simpa only [perpendicularReflection_formula] using h

theorem spherical_history_nonzero_reflection (K : Submodule ℝ E)
    (w : E → NonzeroPerpendicular K)
    (hw : @Measurable E (NonzeroPerpendicular K) (projectionInformation K) inferInstance w) :
    MeasurePreserving (fun x => perpendicularReflection (w x).val x) (sphericalLaw E) (sphericalLaw E) := by
  letI : SecondCountableTopology E := inferInstance
  letI : SecondCountableTopology (NonzeroPerpendicular K) :=
    TopologicalSpace.Subtype.secondCountableTopology {w : E | w ∈ Kᗮ ∧ w ≠ 0}
  letI : BorelSpace (NonzeroPerpendicular K) := Subtype.borelSpace {w : E | w ∈ Kᗮ ∧ w ≠ 0}
  apply spherical_history_continuous_family (mE := mE) (A := NonzeroPerpendicular K) K
    (fun a : NonzeroPerpendicular K => perpendicularReflection a.val)
    (fun a => sphericalLaw_measurePreserving (ℝ ∙ a.val)ᗮ.reflection)
    (nonzeroPerpendicular_reflection_continuous K)
    (fun a x => projection_reflection_perpendicular K a.property.1 x) w hw

/-- Any function measurable from a projection is constant on each projection fiber. -/
theorem projection_known_function_eq {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (K : Submodule ℝ E) (f : E → A)
    (hf : @Measurable E A (projectionInformation K) inferInstance f)
    {x y : E} (hxy : K.orthogonalProjection x = K.orthogonalProjection y) : f x = f y := by
  have hs := hf (measurableSet_singleton (f x))
  obtain ⟨t, ht, he⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hx : (K.orthogonalProjection x : E) ∈ t := by
    change x ∈ (fun z => (K.orthogonalProjection z : E)) ⁻¹' t
    rw [he]
    exact Set.mem_preimage.mpr rfl
  have hy : y ∈ f ⁻¹' {f x} := by
    rw [← he]
    change (K.orthogonalProjection y : E) ∈ t
    rwa [← hxy]
  exact hy.symm

/-- Zero normals are handled by the identity branch; the remaining normals form a continuous
family on the punctured perpendicular subspace. No countability restriction is imposed. -/
theorem spherical_history_reflection (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (w : E → E)
    (hw : @Measurable E E (projectionInformation K) mE w) (hwp : ∀ x, w x ∈ Kᗮ) :
    MeasurePreserving (fun x => perpendicularReflection (w x) x) (sphericalLaw E) (sphericalLaw E) := by
  classical
  let b := fallbackOrthogonal K
  have hb : b ∈ Kᗮ := fallbackOrthogonal_mem K
  have hbn : b ≠ 0 := by
    have h := fallbackOrthogonal_norm K hr
    intro hzero
    change ‖b‖ = 1 at h
    rw [hzero, norm_zero] at h
    exact zero_ne_one h
  let v : E → E := fun x => if w x = 0 then b else w x
  have hv (x : E) : v x ∈ Kᗮ ∧ v x ≠ 0 := by
    by_cases hx : w x = 0
    · simpa only [v, if_pos hx] using And.intro hb hbn
    · simpa only [v, if_neg hx] using And.intro (hwp x) hx
  let W : E → NonzeroPerpendicular K := fun x => ⟨v x, hv x⟩
  have hz : MeasurableSet[projectionInformation K] {x | w x = 0} := hw (measurableSet_singleton 0)
  have hvm : @Measurable E E (projectionInformation K) mE v :=
    Measurable.ite hz measurable_const hw
  have hW : @Measurable E (NonzeroPerpendicular K) (projectionInformation K) inferInstance W :=
    hvm.subtype_mk
  let G : E → E := fun x => perpendicularReflection (W x).val x
  have hG := spherical_history_nonzero_reflection K W hW
  have hGfix (x : E) : K.orthogonalProjection (G x) = K.orthogonalProjection x :=
    projection_reflection_perpendicular K (W x).property.1 x
  let F : Bool → E → E := fun c => if c then G else id
  let choice : E → Bool := fun x => if w x = 0 then false else true
  have hc : @Measurable E Bool (projectionInformation K) inferInstance choice :=
    Measurable.ite hz measurable_const measurable_const
  have hF (c : Bool) : MeasurePreserving (F c) (sphericalLaw E) (sphericalLaw E) := by
    cases c
    · exact MeasurePreserving.id _
    · exact hG
  have hfix (c : Bool) (x : E) : K.orthogonalProjection (F c x) = K.orthogonalProjection x := by
    cases c
    · rfl
    · exact hGfix x
  have hp := spherical_history_selected_map K F hF hfix choice hc
  have he : (fun x => F (choice x) x) = (fun x => perpendicularReflection (w x) x) := by
    funext x
    by_cases hx : w x = 0
    · simp only [choice, if_pos hx, F, Bool.false_eq_true, if_false, id_eq, hx,
        perpendicularReflection_zero]
    · simp only [choice, if_neg hx, F, if_true, G, W, v, if_neg hx]
  rwa [he] at hp

theorem history_reflection_involutive (K : Submodule ℝ E) (w : E → E)
    (hw : @Measurable E E (projectionInformation K) mE w) (hwp : ∀ x, w x ∈ Kᗮ) :
    Function.Involutive (fun x => perpendicularReflection (w x) x) := by
  intro x
  have hp : K.orthogonalProjection (perpendicularReflection (w x) x) = K.orthogonalProjection x :=
    projection_reflection_perpendicular K (hwp x) x
  have he := projection_known_function_eq K w hw hp
  change perpendicularReflection (w (perpendicularReflection (w x) x))
    (perpendicularReflection (w x) x) = x
  rw [he]
  exact Submodule.reflection_reflection _ x

/-- The history-dependent reflection is an actual measurable permutation. -/
def historyReflectionEquiv (K : Submodule ℝ E) (hr : 0 < Module.finrank ℝ Kᗮ)
    (w : E → E) (hw : @Measurable E E (projectionInformation K) mE w)
    (hwp : ∀ x, w x ∈ Kᗮ) : E ≃ᵐ E :=
  MeasurableEquiv.ofInvolutive (fun x => perpendicularReflection (w x) x)
    (history_reflection_involutive K w hw hwp)
    (spherical_history_reflection K hr w hw hwp).measurable

theorem historyReflectionEquiv_preserving (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (w : E → E)
    (hw : @Measurable E E (projectionInformation K) mE w) (hwp : ∀ x, w x ∈ Kᗮ) :
    MeasurePreserving (historyReflectionEquiv K hr w hw hwp) (sphericalLaw E) (sphericalLaw E) :=
  spherical_history_reflection K hr w hw hwp

end
end Nonsmooth
