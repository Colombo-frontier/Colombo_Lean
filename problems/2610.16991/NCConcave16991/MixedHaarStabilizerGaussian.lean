import NCConcave16991.MixedHaarOrbitReplacement
import NCConcave16991.MixedHaarSphereGaussian
import NCConcave16991.ConditionalHaarCompletion

/-! # Actual one-vector Gaussian reveal and independent Haar completion laws -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

theorem compact_haar_inverse_preserving {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    [Measure.IsHaarMeasure μ] [Measure.IsMulRightInvariant μ] :
    MeasurePreserving (Inv.inv : G → G) μ μ := by
  letI : IsProbabilityMeasure μ.inv := by
    change IsProbabilityMeasure (μ.map Inv.inv)
    infer_instance
  letI : Measure.IsHaarMeasure μ.inv :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior μ.inv univ isCompact_univ
      (by simp) (by simp) (by simp)
  refine ⟨measurable_inv,?_⟩
  change μ.inv = μ
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

variable {k : ℕ}

def pointStabilizer (e : SphereSpace k) : Subgroup (Haar.OrthogonalGroup k) :=
  Haar.inputStabilizer (fun _ : Fin 1 ↦ e)

theorem pointStabilizer_closed (e : SphereSpace k) :
    IsClosed (pointStabilizer e : Set (Haar.OrthogonalGroup k)) :=
  Haar.inputStabilizer_closed (fun _ : Fin 1 ↦ e)

def pointStabilizerLaw (e : SphereSpace k) : Measure (pointStabilizer e) :=
  Haar.subgroupHaarLaw (pointStabilizer e) (pointStabilizer_closed e)

instance pointStabilizerLaw_probability (e : SphereSpace k) : IsProbabilityMeasure (pointStabilizerLaw e) := by
  unfold pointStabilizerLaw
  infer_instance

instance pointStabilizerLaw_leftInvariant (e : SphereSpace k) :
    Measure.IsMulLeftInvariant (pointStabilizerLaw e) := by
  unfold pointStabilizerLaw
  infer_instance

def sphereSelector (e v : SphereSpace k) : Haar.OrthogonalGroup k := householderOrthogonal (e - v)

theorem sphereSelector_measurable (e : SphereSpace k) : Measurable (sphereSelector e) := by
  rw [show sphereSelector e = (fun v ↦ householderOrthogonal (e - v)) from rfl]
  have hm : Measurable ((fun _ : SphereSpace k ↦ e) - (id : SphereSpace k → SphereSpace k)) :=
    measurable_const.sub measurable_id
  simpa only [Function.comp_def,Pi.sub_apply,id_eq] using
    (householderOrthogonal_measurable.comp hm)

attribute [local irreducible] householder orthogonalOfIsometry householderOrthogonal sphereSelector

theorem sphereSelector_action (e v : SphereSpace k) (h : ‖e‖ = ‖v‖) :
    Haar.orthogonalLinearIsometryEquiv (sphereSelector e v) e = v := by
  rw [sphereSelector,householderOrthogonal,orthogonalOfIsometry_action]
  exact householder_swap e v h

theorem sphereSelector_relative_stabilizer (e : SphereSpace k) (Q : Haar.OrthogonalGroup k) :
    Q⁻¹ * sphereSelector e (Haar.orthogonalLinearIsometryEquiv Q e) ∈ pointStabilizer e := by
  intro i
  apply (Haar.orthogonalLinearIsometryEquiv Q).injective
  rw [← Haar.action_mul,mul_inv_cancel_left]
  exact sphereSelector_action e _ ((Haar.orthogonalLinearIsometryEquiv Q).norm_map e).symm

def gaussianForwardCompletion (e : SphereSpace k) (p : SphereSpace k × pointStabilizer e) :
    Haar.OrthogonalGroup k := sphereSelector e (normalize p.1) * p.2.val

/-- The fresh Gaussian sphere observation and a genuinely independent
normalized Haar point-stabilizer draw generate exactly the old Haar law. -/
theorem gaussianForwardCompletion_preserving (e : SphereSpace k) (he : ‖e‖ = 1) :
    MeasurePreserving (gaussianForwardCompletion e)
      ((stdGaussian (SphereSpace k)).prod (pointStabilizerLaw e)) (Haar.haarLaw k) := by
  exact orbit_selector_replacement_preserving (Haar.haarLaw k) (pointStabilizer e) (pointStabilizerLaw e)
    (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e)
    (Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable
    (sphereSelector e) (sphereSelector_measurable e) (sphereSelector_relative_stabilizer e)
    (stdGaussian (SphereSpace k)) normalize normalize_measurable
    (normalized_stdGaussian_eq_haarAction e he)

def gaussianInverseCompletion (e : SphereSpace k) (p : SphereSpace k × pointStabilizer e) :
    Haar.OrthogonalGroup k := (gaussianForwardCompletion e p)⁻¹

theorem gaussianInverseCompletion_preserving (e : SphereSpace k) (he : ‖e‖ = 1) :
    MeasurePreserving (gaussianInverseCompletion e)
      ((stdGaussian (SphereSpace k)).prod (pointStabilizerLaw e)) (Haar.haarLaw k) :=
  (compact_haar_inverse_preserving (Haar.haarLaw k)).comp (gaussianForwardCompletion_preserving e he)

theorem gaussianForwardCompletion_image (e : SphereSpace k) (he : ‖e‖ = 1)
    (g : SphereSpace k) (hg : g ≠ 0) (h : pointStabilizer e) :
    Haar.orthogonalLinearIsometryEquiv (gaussianForwardCompletion e (g,h)) e = normalize g := by
  have hh : Haar.orthogonalLinearIsometryEquiv h.val e = e := h.property (0 : Fin 1)
  rw [gaussianForwardCompletion,Haar.action_mul,hh]
  exact sphereSelector_action e _ (he.trans (normalize_norm hg).symm)

theorem gaussianInverseCompletion_image (e : SphereSpace k) (he : ‖e‖ = 1)
    (g : SphereSpace k) (hg : g ≠ 0) (h : pointStabilizer e) :
    Haar.orthogonalLinearIsometryEquiv (gaussianInverseCompletion e (g,h)) (normalize g) = e := by
  rw [← gaussianForwardCompletion_image e he g hg h,gaussianInverseCompletion,
    ← Haar.action_mul,inv_mul_cancel,Haar.action_one]

/-- The exact joint inverse-reveal law, not only its static marginal. -/
theorem gaussianInverseCompletion_jointLaw (e : SphereSpace k) (he : ‖e‖ = 1) :
    ((stdGaussian (SphereSpace k)).prod (pointStabilizerLaw e)).map
        (fun p ↦ (normalize p.1,gaussianInverseCompletion e p)) =
      (Haar.haarLaw k).map (fun Q ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)) := by
  let μ := (stdGaussian (SphereSpace k)).prod (pointStabilizerLaw e)
  let observe := fun Q : Haar.OrthogonalGroup k ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)
  have ho : Measurable observe :=
    ((Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable.comp measurable_inv).prodMk measurable_id
  have hgen := gaussianInverseCompletion_preserving e he
  have hfst : MeasurePreserving (Prod.fst : SphereSpace k × pointStabilizer e → SphereSpace k)
      μ (stdGaussian (SphereSpace k)) := measurePreserving_fst
  have hgood := hfst.quasiMeasurePreserving.ae (stdGaussian_ne_zero_ae e he)
  have heq : (fun p : SphereSpace k × pointStabilizer e ↦ (normalize p.1,gaussianInverseCompletion e p)) =ᵐ[μ]
      observe ∘ gaussianInverseCompletion e := by
    filter_upwards [hgood] with p hp
    apply Prod.ext
    · dsimp [observe,gaussianInverseCompletion]
      simp only [inv_inv,star_star]
      exact (gaussianForwardCompletion_image e he p.1 hp p.2).symm
    · rfl
  rw [Measure.map_congr heq]
  have hm := Measure.map_map (μ := μ) ho hgen.measurable
  rw [← hm,hgen.map_eq]

theorem gaussianInverseCompletion_physicalLaw (e : SphereSpace k) (he : ‖e‖ = 1)
    {Z : Type*} [MeasurableSpace Z] (physical : Haar.OrthogonalGroup k → Z) (hp : Measurable physical) :
    ((stdGaussian (SphereSpace k)).prod (pointStabilizerLaw e)).map
      (fun p ↦ physical (gaussianInverseCompletion e p)) = (Haar.haarLaw k).map physical := by
  have hphysical : MeasurePreserving physical (Haar.haarLaw k) ((Haar.haarLaw k).map physical) := ⟨hp,rfl⟩
  exact (hphysical.comp (gaussianInverseCompletion_preserving e he)).map_eq

/-- A dependent request makes no new reveal and retains the original Haar
completion, while the fresh Gaussian slot may still be consumed publicly. -/
theorem dependentCompletion_preserving (e : SphereSpace k) :
    MeasurePreserving (Prod.snd : SphereSpace k × Haar.OrthogonalGroup k → Haar.OrthogonalGroup k)
      ((stdGaussian (SphereSpace k)).prod (Haar.haarLaw k)) (Haar.haarLaw k) := measurePreserving_snd

end NCConcave16991.MixedHaar
