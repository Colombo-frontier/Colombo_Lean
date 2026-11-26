import Nonsmooth.FixedProjection
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Function Filter
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Almost-everywhere pointwise limits of measure-preserving maps still preserve a probability
law when the limit is measurable. Bounded continuous tests avoid assumptions on inverse maps. -/
theorem measurePreserving_of_ae_pointwise_limit
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {Q : Measure E} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : ℕ → Ω → E) (f : Ω → E) (hF : ∀ n, MeasurePreserving (F n) P Q)
    (hf : Measurable f) (hlim : ∀ᵐ x ∂P, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    MeasurePreserving f P Q := by
  refine ⟨hf, ?_⟩
  letI : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_map hf.aemeasurable g.continuous.measurable.aestronglyMeasurable]
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖g‖)
    (fun n => (g.continuous.measurable.comp (hF n).measurable).aestronglyMeasurable)
    (integrable_const ‖g‖)
    (fun n => Filter.Eventually.of_forall (fun x => g.norm_coe_le_norm (F n x)))
    (hlim.mono (fun x hx => g.continuous.continuousAt.tendsto.comp hx))
  have he (n : ℕ) : (∫ x, g (F n x) ∂P) = ∫ y, g y ∂Q := by
    rw [← integral_map (hF n).measurable.aemeasurable g.continuous.measurable.aestronglyMeasurable,
      (hF n).map_eq]
  simp only [Function.comp_def, he] at ht
  have hc : Tendsto (fun _ : ℕ => ∫ y, g y ∂Q) atTop (𝓝 (∫ y, g y ∂Q)) := tendsto_const_nhds
  exact (tendsto_nhds_unique hc ht).symm

/-- Countably many preserving maps can be patched along measurable invariant branches. -/
theorem measurePreserving_countable_patching
    {E ι : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {P : Measure E} [IsProbabilityMeasure P]
    (F : ι → E → E) (hF : ∀ i, MeasurePreserving (F i) P P)
    (choice : E → ι) (hc : Measurable choice)
    (hpre : ∀ i, F i ⁻¹' {x | choice x = i} = {x | choice x = i}) :
    MeasurePreserving (fun x => F (choice x) x) P P := by
  let f : E → E := fun x => F (choice x) x
  have hfamily : Measurable (fun p : E × ι => F p.2 p.1) :=
    measurable_from_prod_countable_left (fun i => (hF i).measurable)
  have hf : Measurable f :=
    hfamily.comp (measurable_id.prodMk hc)
  refine ⟨hf, ?_⟩
  letI : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_map hf.aemeasurable g.continuous.measurable.aestronglyMeasurable]
  let cells : ι → Set E := fun i => {x | choice x = i}
  have hcells (i : ι) : MeasurableSet (cells i) := hc (measurableSet_singleton i)
  have hdis : Pairwise (Disjoint on cells) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (hxi.symm.trans hxj)
  have hcover : (⋃ i, cells i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨choice x, rfl⟩
  have hgi : Integrable (fun x => g (f x)) P :=
    (integrable_const ‖g‖).mono' (g.continuous.measurable.comp hf).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => g.norm_coe_le_norm (f x)))
  have hgp : Integrable (fun x => g x) P := g.integrable P
  conv_lhs => rw [← setIntegral_univ, ← hcover]
  conv_rhs => rw [← setIntegral_univ, ← hcover]
  rw [integral_iUnion hcells hdis hgi.integrableOn, integral_iUnion hcells hdis hgp.integrableOn]
  apply tsum_congr
  intro i
  have hp := (hF i).restrict_preimage (hcells i)
  rw [hpre i] at hp
  calc
    _ = ∫ x in cells i, g (F i x) ∂P := by
      apply setIntegral_congr_fun (hcells i)
      intro x hx
      change g (F (choice x) x) = g (F i x)
      rw [hx]
    _ = _ := by
      rw [← integral_map (hF i).measurable.aemeasurable g.continuous.measurable.aestronglyMeasurable,
        hp.map_eq]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem projection_event_map (K : Submodule ℝ E) (F : E → E)
    (hfix : ∀ x, K.orthogonalProjection (F x) = K.orthogonalProjection x)
    {s : Set E} (hs : MeasurableSet[projectionInformation K] s) : F ⁻¹' s = s := by
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  ext x
  change (K.orthogonalProjection (F x) : E) ∈ t ↔ (K.orthogonalProjection x : E) ∈ t
  rw [hfix]

/-- A countable preserving family may be selected using the observed projection, if each map
fixes that projection. The selected nonlinear transformation preserves the actual spherical law. -/
theorem spherical_history_selected_map
    {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Submodule ℝ E) (F : ι → E → E)
    (hF : ∀ i, MeasurePreserving (F i) (sphericalLaw E) (sphericalLaw E))
    (hfix : ∀ i x, K.orthogonalProjection (F i x) = K.orthogonalProjection x)
    (choice : E → ι) (hc : @Measurable E ι (projectionInformation K) inferInstance choice) :
    MeasurePreserving (fun x => F (choice x) x) (sphericalLaw E) (sphericalLaw E) := by
  apply measurePreserving_countable_patching F hF choice (hc.mono (projectionInformation_le K) le_rfl)
  intro i
  exact projection_event_map K (F i) (hfix i) (hc (measurableSet_singleton i))

/-- The parameter range need not be countable: a jointly continuous family of preserving maps
can be selected by any measurable function of a fixed observed projection. -/
theorem spherical_history_continuous_family
    {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    (K : Submodule ℝ E) (F : A → E → E)
    (hF : ∀ a, MeasurePreserving (F a) (sphericalLaw E) (sphericalLaw E))
    (hjoint : Continuous (Function.uncurry F))
    (hfix : ∀ a x, K.orthogonalProjection (F a x) = K.orthogonalProjection x)
    (choice : E → A) (hc : @Measurable E A (projectionInformation K) inferInstance choice) :
    MeasurePreserving (fun x => F (choice x) x) (sphericalLaw E) (sphericalLaw E) := by
  have hs : @StronglyMeasurable E A _ (projectionInformation K) choice := hc.stronglyMeasurable
  let approx := hs.approx
  have hpres (n : ℕ) : MeasurePreserving (fun x => F (approx n x) x)
      (sphericalLaw E) (sphericalLaw E) := by
    letI : MeasurableSpace E := projectionInformation (mE := mE) K
    let I := Set.range (approx n : E → A)
    letI : Countable I := (approx n).finite_range.countable.to_subtype
    let index : E → I := fun x => ⟨approx n x, Set.mem_range_self x⟩
    have hi : Measurable index :=
      (approx n).measurable.subtype_mk
    exact spherical_history_selected_map (mE := mE) K (fun i : I => F i.val) (fun i => hF i.val)
      (fun i => hfix i.val) index hi
  have hf : Measurable (fun x => F (choice x) x) :=
    hjoint.measurable.comp ((hc.mono (projectionInformation_le K) le_rfl).prodMk measurable_id)
  apply measurePreserving_of_ae_pointwise_limit (fun n x => F (approx n x) x)
    (fun x => F (choice x) x) hpres hf
  apply Filter.Eventually.of_forall
  intro x
  exact hjoint.continuousAt.tendsto.comp ((hs.tendsto_approx x).prodMk_nhds tendsto_const_nhds)

end
end Nonsmooth
