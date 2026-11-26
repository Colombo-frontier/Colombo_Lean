import Bilevel.EquivariantDisintegration

/-! A genuine regular conditional law with simultaneous pointwise stabilizer invariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Bilevel.ConditionalSymmetry

theorem pushforward_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f) (u : X → X) (v : Y → Y)
    (hu : MeasurePreserving u μ μ) (hv : Measurable v) (he : ∀ x, f (u x) = v (f x)) :
    MeasurePreserving v (μ.map f) (μ.map f) := by
  refine ⟨hv, ?_⟩
  have hc : v ∘ f = f ∘ u := by funext x; exact (he x).symm
  rw [Measure.map_map hv hf, hc, ← Measure.map_map hf hu.measurable, hu.map_eq]

variable {G X Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSpace X] [MeasurableSpace Y] [MulAction G X] [MulAction G Y]
  [MeasurableSMul₂ G X] [MeasurableSMul₂ G Y] [StandardBorelSpace X] [Nonempty X]
  (ν : Measure G) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (observation : X → Y)

def posterior : Kernel Y X := EquivariantKernel.average ν (condDistrib id observation μ)

instance posterior_markov : IsMarkovKernel (posterior ν μ observation) := inferInstanceAs
  (IsMarkovKernel (EquivariantKernel.average ν (condDistrib id observation μ)))

theorem posterior_isotropy (g : G) (y : Y) (hy : g • y = y) :
    MeasurePreserving (fun x : X => g • x) (posterior ν μ observation y) (posterior ν μ observation y) :=
  EquivariantKernel.isotropy_preserving ν _ g y hy

omit [MeasurableMul₂ G] [Measure.IsMulLeftInvariant ν] in
theorem posterior_joint_law (ho : Measurable observation)
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (he : ∀ (g : G) (x : X), observation (g • x) = g • observation x) :
    (μ.map observation) ⊗ₘ posterior ν μ observation = μ.map (fun x => (observation x,x)) := by
  letI : IsProbabilityMeasure (μ.map observation) := isProbabilityMeasure_map ho.aemeasurable
  have hbase : (μ.map observation) ⊗ₘ condDistrib id observation μ =
      μ.map (fun x => (observation x,x)) := compProd_map_condDistrib measurable_id.aemeasurable
  have hobs : ∀ g : G, MeasurePreserving (fun y : Y => g • y)
      (μ.map observation) (μ.map observation) := by
    intro g
    exact pushforward_preserving μ observation ho _ _ (hp g)
      (measurable_const.smul measurable_id) (he g)
  have hjoint : ∀ g : G, MeasurePreserving (fun p : Y × X => (g • p.1,g • p.2))
      ((μ.map observation) ⊗ₘ condDistrib id observation μ)
      ((μ.map observation) ⊗ₘ condDistrib id observation μ) := by
    intro g
    rw [hbase]
    apply pushforward_preserving μ (fun x => (observation x,x)) (ho.prodMk measurable_id)
      _ _ (hp g) ((measurable_const.smul measurable_fst).prodMk (measurable_const.smul measurable_snd))
    intro x
    simp only [he]
  exact (EquivariantDisintegration.joint_law_preserved ν (μ.map observation)
    (condDistrib id observation μ) hobs hjoint).trans hbase

omit [MeasurableMul₂ G] [Measure.IsMulLeftInvariant ν] in
theorem posterior_ae_eq_condDistrib (ho : Measurable observation)
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (he : ∀ (g : G) (x : X), observation (g • x) = g • observation x) :
    ∀ᵐ y ∂μ.map observation, posterior ν μ observation y = condDistrib id observation μ y :=
  condDistrib_ae_eq_of_measure_eq_compProd ho measurable_id _
    (posterior_joint_law ν μ observation ho hp he).symm

omit [MeasurableMul₂ G] [Measure.IsMulLeftInvariant ν] in
theorem posterior_observation_ae (ho : Measurable observation)
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (he : ∀ (g : G) (x : X), observation (g • x) = g • observation x)
    (hgraph : MeasurableSet {p : Y × X | observation p.2 = p.1}) :
    ∀ᵐ y ∂μ.map observation, ∀ᵐ x ∂posterior ν μ observation y, observation x = y := by
  letI : IsProbabilityMeasure (μ.map observation) := isProbabilityMeasure_map ho.aemeasurable
  have hj : ∀ᵐ p ∂μ.map (fun x => (observation x,x)), observation p.2 = p.1 := by
    have hm : Measurable (fun x : X => (observation x,x)) := ho.prodMk measurable_id
    exact (ae_map_iff hm.aemeasurable hgraph).2 (Filter.Eventually.of_forall (fun _ => rfl))
  rw [← posterior_joint_law ν μ observation ho hp he] at hj
  exact Measure.ae_ae_of_ae_compProd hj

omit [MeasurableMul₂ G] [Measure.IsMulLeftInvariant ν] in
theorem posterior_preserves_ae (ho : Measurable observation)
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (he : ∀ (g : G) (x : X), observation (g • x) = g • observation x)
    (s : Set X) (hs : MeasurableSet s) (hμs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ y ∂μ.map observation, ∀ᵐ x ∂posterior ν μ observation y, x ∈ s := by
  letI : IsProbabilityMeasure (μ.map observation) := isProbabilityMeasure_map ho.aemeasurable
  have hj : ∀ᵐ p ∂μ.map (fun x => (observation x,x)), p.2 ∈ s := by
    have hm : Measurable (fun x : X => (observation x,x)) := ho.prodMk measurable_id
    exact (ae_map_iff hm.aemeasurable (measurable_snd hs)).2 hμs
  rw [← posterior_joint_law ν μ observation ho hp he] at hj
  exact Measure.ae_ae_of_ae_compProd hj

end Bilevel.ConditionalSymmetry
