import NCConcave16991.MixedHaarTailCompletionLaw

/-! # The literal Se * tail * Sdirection inverse kernel used by full frames -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

attribute [local irreducible] sphereSelector householder householderOrthogonal orthogonalOfIsometry

variable {W : Type*} [MeasurableSpace W] {k m : ℕ}

def sphereFrameKernel (e₀ e : SphereSpace k) (sample : W → SphereSpace k)
    (f : Haar.OrthogonalGroup m →* pointStabilizer e₀) (p : W × Haar.OrthogonalGroup m) :
    Haar.OrthogonalGroup k :=
  sphereSelector e₀ e * (f p.2).val * (sphereSelector e₀ (sample p.1))⁻¹

theorem sphereFrameKernel_preserving (ρ : Measure W) [IsProbabilityMeasure ρ]
    (e₀ : SphereSpace k) (he₀ : ‖e₀‖ = 1) (e : SphereSpace k)
    (sample : W → SphereSpace k) (hs : Measurable sample)
    (hlaw : ρ.map sample = (Haar.haarLaw k).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e₀))
    (f : Haar.OrthogonalGroup m →* pointStabilizer e₀) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    MeasurePreserving (sphereFrameKernel e₀ e sample f) (ρ.prod (Haar.haarLaw m)) (Haar.haarLaw k) := by
  let base := fun p : W × pointStabilizer e₀ ↦ sphereSelector e₀ (sample p.1) * p.2.val
  have hb : MeasurePreserving base (ρ.prod (pointStabilizerLaw e₀)) (Haar.haarLaw k) :=
    orbit_selector_replacement_preserving (Haar.haarLaw k) (pointStabilizer e₀) (pointStabilizerLaw e₀)
      (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e₀)
      (Haar.continuous_orthogonalLinearIsometryEquiv_apply e₀).measurable
      (sphereSelector e₀) (sphereSelector_measurable e₀) (sphereSelector_relative_stabilizer e₀)
      ρ sample hs hlaw
  have hi := (compact_haar_inverse_preserving (Haar.haarLaw k)).comp hb
  have ht := (measurePreserving_mul_left (Haar.haarLaw k) (sphereSelector e₀ e)).comp hi
  have hfi := (pointStabilizerHaar_transport e₀ f hf hsurj).comp
    (compact_haar_inverse_preserving (Haar.haarLaw m))
  have hsource := (MeasurePreserving.id ρ).prod hfi
  have h := ht.comp hsource
  convert h using 1
  funext p
  simp only [sphereFrameKernel,Function.comp_def,base,Prod.map,id_eq,map_inv,
    Subgroup.coe_inv,mul_inv_rev,inv_inv,mul_assoc]

theorem sphereFrameKernel_image (e₀ e : SphereSpace k) (he₀ : ‖e₀‖ = 1) (he : ‖e‖ = 1)
    (sample : W → SphereSpace k) (f : Haar.OrthogonalGroup m →* pointStabilizer e₀)
    (w : W) (hw : ‖sample w‖ = 1) (z : Haar.OrthogonalGroup m) :
    Haar.orthogonalLinearIsometryEquiv (sphereFrameKernel e₀ e sample f (w,z)) (sample w) = e := by
  have hS := sphereSelector_action e₀ (sample w) (he₀.trans hw.symm)
  have hSinv : Haar.orthogonalLinearIsometryEquiv (sphereSelector e₀ (sample w))⁻¹ (sample w) = e₀ := by
    apply (Haar.orthogonalLinearIsometryEquiv (sphereSelector e₀ (sample w))).injective
    rw [← Haar.action_mul,mul_inv_cancel,Haar.action_one]
    exact hS.symm
  have hfix : Haar.orthogonalLinearIsometryEquiv (f z).val e₀ = e₀ := (f z).property (0 : Fin 1)
  rw [sphereFrameKernel,Haar.action_mul,Haar.action_mul,hSinv,hfix]
  exact sphereSelector_action e₀ e (he₀.trans he.symm)

/-- The exact coordinate joint law for the literal full-frame completion
factorization; the ordinary smaller Haar coordinate occurs without inversion. -/
theorem sphereFrameKernel_jointLaw (ρ : Measure W) [IsProbabilityMeasure ρ]
    (e₀ e : SphereSpace k) (he₀ : ‖e₀‖ = 1) (he : ‖e‖ = 1)
    (sample : W → SphereSpace k) (hs : Measurable sample)
    (hlaw : ρ.map sample = (Haar.haarLaw k).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e₀))
    (hunit : ∀ᵐ w ∂ρ, ‖sample w‖ = 1)
    (f : Haar.OrthogonalGroup m →* pointStabilizer e₀) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    (ρ.prod (Haar.haarLaw m)).map (fun p ↦ (sample p.1,sphereFrameKernel e₀ e sample f p)) =
      (Haar.haarLaw k).map (fun Q ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)) := by
  let μ := ρ.prod (Haar.haarLaw m)
  let observe := fun Q : Haar.OrthogonalGroup k ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)
  have ho : Measurable observe :=
    ((Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable.comp measurable_inv).prodMk measurable_id
  have hgen := sphereFrameKernel_preserving ρ e₀ he₀ e sample hs hlaw f hf hsurj
  have hfst : MeasurePreserving (Prod.fst : W × Haar.OrthogonalGroup m → W) μ ρ := measurePreserving_fst
  have hgood := hfst.quasiMeasurePreserving.ae hunit
  have heq : (fun p : W × Haar.OrthogonalGroup m ↦ (sample p.1,sphereFrameKernel e₀ e sample f p)) =ᵐ[μ]
      observe ∘ sphereFrameKernel e₀ e sample f := by
    filter_upwards [hgood] with p hp
    apply Prod.ext
    · change sample p.1 = Haar.orthogonalLinearIsometryEquiv (sphereFrameKernel e₀ e sample f p)⁻¹ e
      apply (Haar.orthogonalLinearIsometryEquiv (sphereFrameKernel e₀ e sample f p)).injective
      rw [← Haar.action_mul,mul_inv_cancel,Haar.action_one]
      exact sphereFrameKernel_image e₀ e he₀ he sample f p.1 hp p.2
    · rfl
  rw [Measure.map_congr heq]
  have hm := Measure.map_map (μ := μ) ho hgen.measurable
  rw [← hm,hgen.map_eq]

end NCConcave16991.MixedHaar
