import SphereSmoothingPolarBridge
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import SphereSmoothingRadialMean

open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise Matrix

namespace Task006.SphereSmoothing

open Task006.HaarRebalancing
noncomputable section
variable {d : ℕ}
abbrev SphereSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

def ambientSurface (d : ℕ) : Measure (SphereSpace d) :=
  Measure.map (Subtype.val : UnitSphere d → SphereSpace d)
    (volume : Measure (SphereSpace d)).toSphere

instance : IsFiniteMeasure (ambientSurface d) := by unfold ambientSurface; infer_instance

theorem ambientSurface_unit : ∀ᵐ x ∂ambientSurface d, ‖x‖ = 1 := by
  rw [ambientSurface,ae_map_iff measurable_subtype_coe.aemeasurable
    ((isClosed_eq continuous_norm continuous_const).measurableSet)]
  exact Filter.Eventually.of_forall (fun x => by simpa using x.property)

theorem sphere_cone_preimage (U : SphereSpace d ≃ₗᵢ[ℝ] SphereSpace d) (s : Set (SphereSpace d)) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' ((fun u : UnitSphere d => U u.val) ⁻¹' s)) =
      U ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' ((Subtype.val : UnitSphere d → SphereSpace d) ⁻¹' s))) := by
  ext x
  constructor
  · rintro ⟨r,hr,_,⟨u,hu,rfl⟩,rfl⟩
    refine ⟨r,hr,U u.val,?_,?_⟩
    · exact ⟨⟨U u.val,by simpa using u.property⟩,hu,rfl⟩
    · simp
  · rintro ⟨r,hr,_,⟨u,hu,rfl⟩,he⟩
    let v : UnitSphere d := ⟨U.symm u.val,by simpa using u.property⟩
    refine ⟨r,hr,v.val,?_,?_⟩
    · refine ⟨v,?_,rfl⟩
      simpa only [v,Set.mem_preimage,U.apply_symm_apply] using hu
    · apply U.injective
      simpa only [map_smul,v,U.apply_symm_apply] using he

theorem ambientSurface_rotation (U : SphereSpace d ≃ₗᵢ[ℝ] SphereSpace d) :
    Measure.map U (ambientSurface d) = ambientSurface d := by
  ext s hs
  rw [ambientSurface,Measure.map_map U.continuous.measurable measurable_subtype_coe,
    Measure.map_apply (U.continuous.measurable.comp measurable_subtype_coe) hs,
    Measure.map_apply measurable_subtype_coe hs,
    Measure.toSphere_apply' _ ((U.continuous.measurable.comp measurable_subtype_coe) hs),
    Measure.toSphere_apply' _ (measurable_subtype_coe hs)]
  simp only [Function.comp_def]
  rw [sphere_cone_preimage]
  congr 1
  exact U.measurePreserving.measure_preimage_emb U.toHomeomorph.measurableEmbedding _

theorem invariant_unit_finite_eq_haar (μ : Measure (SphereSpace d)) [IsFiniteMeasure μ]
    (hunit : ∀ᵐ x ∂μ, ‖x‖ = 1)
    (hrot : ∀ U : SphereSpace d ≃ₗᵢ[ℝ] SphereSpace d, Measure.map U μ = μ)
    (j : Fin d) :
    μ = μ Set.univ • Measure.map (fun Q : OrthogonalGroup d => column Q j) (orthogonalHaarProbability d) := by
  ext s hs
  let f : SphereSpace d → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hbasis (Q : OrthogonalGroup d) :
      action Q ((EuclideanSpace.basisFun (Fin d) ℝ) j) = column Q j := by
    apply WithLp.ofLp_injective 2
    funext i
    change (∑ k : Fin d, (Q : Matrix (Fin d) (Fin d) ℝ) i k *
      (EuclideanSpace.basisFun (Fin d) ℝ j) k) = _
    simp [EuclideanSpace.basisFun_apply,column]
  have hfixed (Q : OrthogonalGroup d) :
      (∫⁻ x, f (action Q x) ∂μ) = ∫⁻ x, f x ∂μ := by
    rw [← lintegral_map hf (action Q).continuous.measurable,hrot]
  have hcalc : (∫⁻ x, f x ∂μ) =
      μ Set.univ * ∫⁻ Q : OrthogonalGroup d, f (column Q j) ∂orthogonalHaarProbability d := by
    calc
      _ = ∫⁻ Q, ∫⁻ x, f (action Q x) ∂μ ∂orthogonalHaarProbability d := by simp_rw [hfixed]; simp
      _ = ∫⁻ x, ∫⁻ Q, f (action Q x) ∂orthogonalHaarProbability d ∂μ := by
        exact lintegral_lintegral_swap (hf.comp action_joint_continuous.measurable).aemeasurable
      _ = ∫⁻ _x, ∫⁻ Q, f (column Q j) ∂orthogonalHaarProbability d ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hunit] with x hx
        have hbase : ‖(EuclideanSpace.basisFun (Fin d) ℝ j)‖ = 1 :=
          (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one j
        simpa only [hbasis] using
          (orbit_lintegral_eq f x ((EuclideanSpace.basisFun (Fin d) ℝ) j) (hx.trans hbase.symm))
      _ = _ := by simp [mul_comm]
  have hr : (∫⁻ Q : OrthogonalGroup d, f (column Q j) ∂orthogonalHaarProbability d) =
      (Measure.map (fun Q : OrthogonalGroup d => column Q j) (orthogonalHaarProbability d)) s := by
    rw [← lintegral_map hf (measurable_column j)]
    simp only [f,lintegral_indicator_const hs,one_mul]
  rw [hr] at hcalc
  simpa only [f,lintegral_indicator_const hs,one_mul,Measure.smul_apply,smul_eq_mul] using hcalc

theorem ambientSurface_mass : ambientSurface d Set.univ =
    ENNReal.ofReal ((d : ℝ)*(volume : Measure (SphereSpace d)).real (ball 0 1)) := by
  have hm : ambientSurface d Set.univ =
      (d : ℝ≥0∞)*(volume : Measure (SphereSpace d)) (ball 0 1) := by
    rw [ambientSurface,Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    simp [Measure.toSphere_apply_univ]
  have hfin : (volume : Measure (SphereSpace d)) (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [hm,ENNReal.ofReal_mul (Nat.cast_nonneg d),ENNReal.ofReal_natCast,
    measureReal_def,ENNReal.ofReal_toReal hfin]

theorem ambientSurface_eq_haar (j : Fin d) :
    ambientSurface d =
      ENNReal.ofReal ((d : ℝ)*(volume : Measure (SphereSpace d)).real (ball 0 1)) •
        Measure.map (fun Q : OrthogonalGroup d => column Q j) (orthogonalHaarProbability d) := by
  have h := invariant_unit_finite_eq_haar (ambientSurface d) ambientSurface_unit ambientSurface_rotation j
  rw [ambientSurface_mass] at h
  exact h

theorem surface_integral_eq_haar {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (g : SphereSpace d → V) (hg : Measurable g) (j : Fin d) :
    (∫ u : UnitSphere d, g u.val ∂(volume : Measure (SphereSpace d)).toSphere) =
      ((d : ℝ)*(volume : Measure (SphereSpace d)).real (ball 0 1)) •
        (∫ Q : OrthogonalGroup d, g (column Q j) ∂orthogonalHaarProbability d) := by
  calc
    _ = ∫ x, g x ∂ambientSurface d :=
      (integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable).symm
    _ = _ := by
      rw [ambientSurface_eq_haar j,integral_smul_measure,
        ENNReal.toReal_ofReal (by positivity),
        integral_map (measurable_column j).aemeasurable hg.aestronglyMeasurable]

end
end Task006.SphereSmoothing
