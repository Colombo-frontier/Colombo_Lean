import NCConcave16991.MixedHaarStabilizerGaussian
import NCConcave16991.MixedHaarGaussianComplement
import NCConcave16991.MixedHaarInverseCandidate

/-! # One actual inverse reveal from a fixed-dimensional Gaussian nuisance slot -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

def projectedSample (D : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] SphereSpace k) (g : E) : SphereSpace k :=
  U (normalize (D.orthogonalProjectionOnto g))

theorem projectedSample_measurable (D : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] SphereSpace k) :
    Measurable (projectedSample D U) :=
  U.continuous.measurable.comp (normalize_measurable.comp D.orthogonalProjectionOnto.continuous.measurable)

def projectedForwardCompletion (D : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] SphereSpace k)
    (e : SphereSpace k) (p : E × pointStabilizer e) : Haar.OrthogonalGroup k :=
  sphereSelector e (projectedSample D U p.1) * p.2.val

theorem projectedForwardCompletion_preserving (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e : SphereSpace k) (he : ‖e‖ = 1) :
    MeasurePreserving (projectedForwardCompletion D U e)
      ((stdGaussian E).prod (pointStabilizerLaw e)) (Haar.haarLaw k) := by
  exact orbit_selector_replacement_preserving (Haar.haarLaw k) (pointStabilizer e) (pointStabilizerLaw e)
    (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e)
    (Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable
    (sphereSelector e) (sphereSelector_measurable e) (sphereSelector_relative_stabilizer e)
    (stdGaussian E) (projectedSample D U) (projectedSample_measurable D U)
    (normalized_projection_eq_haarAction D U e he)

def projectedInverseCompletion (D : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] SphereSpace k)
    (e : SphereSpace k) (p : E × pointStabilizer e) : Haar.OrthogonalGroup k :=
  (projectedForwardCompletion D U e p)⁻¹

theorem projectedInverseCompletion_preserving (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e : SphereSpace k) (he : ‖e‖ = 1) :
    MeasurePreserving (projectedInverseCompletion D U e)
      ((stdGaussian E).prod (pointStabilizerLaw e)) (Haar.haarLaw k) :=
  (compact_haar_inverse_preserving (Haar.haarLaw k)).comp (projectedForwardCompletion_preserving D U e he)

theorem projectedForwardCompletion_image (D : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] SphereSpace k)
    (e : SphereSpace k) (he : ‖e‖ = 1) (g : E) (hg : D.orthogonalProjectionOnto g ≠ 0)
    (h : pointStabilizer e) :
    Haar.orthogonalLinearIsometryEquiv (projectedForwardCompletion D U e (g,h)) e = projectedSample D U g := by
  have hh : Haar.orthogonalLinearIsometryEquiv h.val e = e := h.property (0 : Fin 1)
  rw [projectedForwardCompletion,Haar.action_mul,hh]
  apply sphereSelector_action
  rw [he,projectedSample,U.norm_map,normalize_norm hg]

/-- The formal Gaussian slot stays in the fixed physical ambient space E;
only its residual is used. Both the original Haar marginal and the literal
inverse observation are proved jointly. -/
theorem projectedInverseCompletion_jointLaw (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e : SphereSpace k) (he : ‖e‖ = 1) :
    ((stdGaussian E).prod (pointStabilizerLaw e)).map
        (fun p ↦ (projectedSample D U p.1,projectedInverseCompletion D U e p)) =
      (Haar.haarLaw k).map (fun Q ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)) := by
  let μ := (stdGaussian E).prod (pointStabilizerLaw e)
  let observe := fun Q : Haar.OrthogonalGroup k ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)
  have ho : Measurable observe :=
    ((Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable.comp measurable_inv).prodMk measurable_id
  have hgen := projectedInverseCompletion_preserving D U e he
  have hfst : MeasurePreserving (Prod.fst : E × pointStabilizer e → E) μ (stdGaussian E) := measurePreserving_fst
  have hunit : ‖U.symm e‖ = 1 := (U.symm.norm_map e).trans he
  have hgood := hfst.quasiMeasurePreserving.ae (stdGaussian_projection_ne_zero_ae_of_unit D (U.symm e) hunit)
  have heq : (fun p : E × pointStabilizer e ↦
      (projectedSample D U p.1,projectedInverseCompletion D U e p)) =ᵐ[μ]
      observe ∘ projectedInverseCompletion D U e := by
    filter_upwards [hgood] with p hp
    apply Prod.ext
    · dsimp [observe,projectedInverseCompletion]
      simp only [inv_inv,star_star]
      exact (projectedForwardCompletion_image D U e he p.1 hp p.2).symm
    · rfl
  rw [Measure.map_congr heq]
  have hm := Measure.map_map (μ := μ) ho hgen.measurable
  rw [← hm,hgen.map_eq]

/-- Deterministic known/physical maps may be applied to both sides of the
actual one-step inverse-reveal joint law. -/
theorem projectedInverseCompletion_observedPhysicalLaw (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e : SphereSpace k) (he : ‖e‖ = 1)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (answer : SphereSpace k → A) (ha : Measurable answer)
    (physical : Haar.OrthogonalGroup k → B) (hb : Measurable physical) :
    ((stdGaussian E).prod (pointStabilizerLaw e)).map
        (fun p ↦ (answer (projectedSample D U p.1),physical (projectedInverseCompletion D U e p))) =
      (Haar.haarLaw k).map (fun Q ↦ (answer (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e),physical Q)) := by
  let transform := Prod.map answer physical
  have ht : Measurable transform := ha.prodMap hb
  have hleft : Measurable (fun p : E × pointStabilizer e ↦
      (projectedSample D U p.1,projectedInverseCompletion D U e p)) :=
    ((projectedSample_measurable D U).comp measurable_fst).prodMk
      (projectedInverseCompletion_preserving D U e he).measurable
  have hright : Measurable (fun Q : Haar.OrthogonalGroup k ↦
      (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)) :=
    ((Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable.comp measurable_inv).prodMk measurable_id
  have h := congrArg (fun ν : Measure (SphereSpace k × Haar.OrthogonalGroup k) ↦ ν.map transform)
    (projectedInverseCompletion_jointLaw D U e he)
  rw [Measure.map_map ht hleft,Measure.map_map ht hright] at h
  simpa only [Function.comp_def,transform,Prod.map] using h

theorem dependent_request_completion_preserving :
    MeasurePreserving (Prod.snd : E × Haar.OrthogonalGroup k → Haar.OrthogonalGroup k)
      ((stdGaussian E).prod (Haar.haarLaw k)) (Haar.haarLaw k) := measurePreserving_snd

theorem inverseCandidate_dependent_eq (D R : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] R)
    (x g : E) (hx : residual R x = 0) : inverseCandidate D R U x g = knownInverse D R U x := by
  simp only [inverseCandidate,hx,norm_zero,zero_div,zero_smul,add_zero]

theorem inverseCandidate_dependent_law (D R : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] R)
    (x : E) (hx : residual R x = 0) :
    (stdGaussian E).map (inverseCandidate D R U x) = Measure.dirac (knownInverse D R U x) := by
  have hf : inverseCandidate D R U x = fun _ : E ↦ knownInverse D R U x :=
    funext (fun g ↦ inverseCandidate_dependent_eq D R U x g hx)
  rw [hf]
  simp

end NCConcave16991.MixedHaar
