import Bilevel.ConditionalSymmetry

/-! Symmetry and support of actual regular conditional distributions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.ConditionalSupport

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] (μ : Measure X) [IsProbabilityMeasure μ]
  (o : X → Y) (ho : Measurable o)

theorem joint_law : (μ.map o) ⊗ₘ condDistrib id o μ = μ.map (fun x => (o x,x)) :=
  compProd_map_condDistrib measurable_id.aemeasurable

include ho

theorem fiber (hgraph : MeasurableSet {p : Y × X | o p.2 = p.1}) :
    ∀ᵐ y ∂μ.map o, ∀ᵐ x ∂condDistrib id o μ y, o x = y := by
  letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map ho.aemeasurable
  have hm : Measurable (fun x : X => (o x,x)) := ho.prodMk measurable_id
  have hj : ∀ᵐ p ∂μ.map (fun x => (o x,x)), o p.2 = p.1 :=
    (ae_map_iff hm.aemeasurable hgraph).2 (Filter.Eventually.of_forall (fun _ => rfl))
  rw [← joint_law μ o] at hj
  exact Measure.ae_ae_of_ae_compProd hj

theorem support (s : Set X) (hs : MeasurableSet s) (hμs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ y ∂μ.map o, ∀ᵐ x ∂condDistrib id o μ y, x ∈ s := by
  letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map ho.aemeasurable
  have hm : Measurable (fun x : X => (o x,x)) := ho.prodMk measurable_id
  have hj : ∀ᵐ p ∂μ.map (fun x => (o x,x)), p.2 ∈ s :=
    (ae_map_iff hm.aemeasurable (measurable_snd hs)).2 hμs
  rw [← joint_law μ o] at hj
  exact Measure.ae_ae_of_ae_compProd hj

theorem event_disintegration (s : Set (Y × X)) (hs : MeasurableSet s) :
    μ {x | (o x,x) ∈ s} = ∫⁻ y, condDistrib id o μ y {x | (y,x) ∈ s} ∂μ.map o := by
  letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map ho.aemeasurable
  have hm : Measurable (fun x : X => (o x,x)) := ho.prodMk measurable_id
  calc
    _ = (μ.map (fun x => (o x,x))) s := (Measure.map_apply hm hs).symm
    _ = _ := by rw [← joint_law μ o, Measure.compProd_apply hs]; rfl

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MulAction G X] [MeasurableSMul₂ G X]
  (ν : Measure G) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν]

include ν

theorem invariant_observation
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (he : ∀ (g : G) (x : X), o (g • x) = o x) :
    ∀ᵐ y ∂μ.map o, ∀ g : G,
      MeasurePreserving (fun x : X => g • x) (condDistrib id o μ y) (condDistrib id o μ y) := by
  letI : MulAction G Y := {
    smul := fun _ y => y
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  letI : MeasurableSMul₂ G Y := ⟨measurable_snd⟩
  have he' : ∀ (g : G) (x : X), o (g • x) = g • o x := he
  filter_upwards [ConditionalSymmetry.posterior_ae_eq_condDistrib ν μ o ho hp he'] with y hy
  intro g
  rw [← hy]
  exact ConditionalSymmetry.posterior_isotropy ν μ o g y rfl

theorem equivariant_observation [MulAction G Y] [MeasurableSMul₂ G Y]
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (he : ∀ (g : G) (x : X), o (g • x) = g • o x) :
    ∀ᵐ y ∂μ.map o, ∀ g : G, g • y = y →
      MeasurePreserving (fun x : X => g • x) (condDistrib id o μ y) (condDistrib id o μ y) := by
  filter_upwards [ConditionalSymmetry.posterior_ae_eq_condDistrib ν μ o ho hp he] with y hy
  intro g hg
  rw [← hy]
  exact ConditionalSymmetry.posterior_isotropy ν μ o g y hg

end Bilevel.ConditionalSupport
