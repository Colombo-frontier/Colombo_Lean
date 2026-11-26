import FreshGradientMinimax.SeedMachines
import FreshGradientMinimax.CostedComposition

/-! Independent countable seeds, sampled before the original oracle is
used. Mixture laws commute with sequential composition, including the
output-dependent transitions and accumulation of query counts. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {I J X Y Z : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
variable [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def labelKernel (L : I → Kernel X Y) : Kernel (X × I) Y where
  toFun s := L s.2 s.1
  measurable' := measurable_from_prod_countable (fun i => (L i).measurable)

instance labelKernel_markov (L : I → Kernel X Y) [∀ i, IsMarkovKernel (L i)] :
    IsMarkovKernel (labelKernel L) := ⟨fun s => inferInstanceAs (IsProbabilityMeasure (L s.2 s.1))⟩

def inputSeedKernel (μ : Measure I) : Kernel X (X × I) := Kernel.id ×ₖ Kernel.const X μ

instance inputSeedKernel_markov (μ : Measure I) [IsProbabilityMeasure μ] :
    IsMarkovKernel (inputSeedKernel (X := X) μ) := by unfold inputSeedKernel; infer_instance

omit [Countable I] [MeasurableSingletonClass I] in
theorem inputSeedKernel_apply (μ : Measure I) [SFinite μ] (x : X) :
    inputSeedKernel μ x = μ.map (fun i => (x, i)) := by
  rw [inputSeedKernel, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod]

def mixtureKernel (μ : Measure I) (L : I → Kernel X Y) : Kernel X Y := labelKernel L ∘ₖ inputSeedKernel μ

instance mixtureKernel_markov (μ : Measure I) [IsProbabilityMeasure μ]
    (L : I → Kernel X Y) [∀ i, IsMarkovKernel (L i)] : IsMarkovKernel (mixtureKernel μ L) := by
  unfold mixtureKernel; infer_instance

theorem mixtureKernel_apply (μ : Measure I) [SFinite μ] (L : I → Kernel X Y)
    (x : X) {A : Set Y} (hA : MeasurableSet A) :
    mixtureKernel μ L x A = ∫⁻ i, L i x A ∂μ := by
  rw [mixtureKernel, Kernel.comp_apply' _ _ _ hA, inputSeedKernel_apply,
    lintegral_map (g := fun i : I => (x, i)) ((labelKernel L).measurable_coe hA)
      (measurable_const.prodMk measurable_id)]
  rfl

theorem mixtureKernel_lintegral (μ : Measure I) [SFinite μ] (L : I → Kernel X Y)
    [∀ i, IsMarkovKernel (L i)] (x : X) (g : Y → ENNReal) (hg : Measurable g) :
    (∫⁻ y, g y ∂mixtureKernel μ L x) = ∫⁻ i, ∫⁻ y, g y ∂L i x ∂μ := by
  rw [mixtureKernel, Kernel.lintegral_comp _ _ _ hg, inputSeedKernel_apply,
    lintegral_map (g := fun i : I => (x, i)) (hg.lintegral_kernel (κ := labelKernel L))
      (measurable_const.prodMk measurable_id)]
  rfl

theorem mixtureKernel_map (μ : Measure I) [SFinite μ] (L : I → Kernel X Y)
    (f : Y → Z) (hf : Measurable f) :
    (mixtureKernel μ L).map f = mixtureKernel μ (fun i => (L i).map f) := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  rw [Kernel.map_apply _ hf, Measure.map_apply hf hA, mixtureKernel_apply μ L x (hf hA),
    mixtureKernel_apply μ _ x hA]
  apply lintegral_congr
  intro i
  rw [Kernel.map_apply _ hf, Measure.map_apply hf hA]

theorem mixtureKernel_comp_right (μ : Measure I) [SFinite μ] (L : I → Kernel X Y)
    [∀ i, IsMarkovKernel (L i)] (R : Kernel Y Z) :
    R ∘ₖ mixtureKernel μ L = mixtureKernel μ (fun i => R ∘ₖ L i) := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  rw [Kernel.comp_apply' _ _ _ hA, mixtureKernel_lintegral _ _ _ _ (R.measurable_coe hA),
    mixtureKernel_apply μ _ x hA]
  simp only [Kernel.comp_apply' _ _ _ hA]

theorem mixtureKernel_comp_left (μ : Measure I) [SFinite μ] (L : Kernel X Y) [IsMarkovKernel L]
    (R : I → Kernel Y Z) :
    mixtureKernel μ R ∘ₖ L = mixtureKernel μ (fun i => R i ∘ₖ L) := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  rw [Kernel.comp_apply' _ _ _ hA, mixtureKernel_apply μ _ x hA]
  simp_rw [mixtureKernel_apply μ R _ hA, Kernel.comp_apply' _ _ _ hA]
  apply lintegral_lintegral_swap
  exact (measurable_from_prod_countable (fun i => (R i).measurable_coe hA)).aemeasurable

theorem mixtureKernel_product (μ : Measure I) [SFinite μ] (ν : Measure J) [SFinite ν]
    (L : I → J → Kernel X Y) :
    mixtureKernel μ (fun i => mixtureKernel ν (L i)) = mixtureKernel (μ.prod ν) (fun s => L s.1 s.2) := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  rw [mixtureKernel_apply μ _ x hA, mixtureKernel_apply (μ.prod ν) _ x hA,
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp_rw [mixtureKernel_apply ν _ x hA]

theorem mixtureKernel_comp (μ : Measure I) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (L : I → Kernel X Y) [∀ i, IsMarkovKernel (L i)]
    (R : J → Kernel Y Z) :
    mixtureKernel ν R ∘ₖ mixtureKernel μ L = mixtureKernel (μ.prod ν) (fun s => R s.2 ∘ₖ L s.1) := by
  rw [mixtureKernel_comp_right]
  simp_rw [mixtureKernel_comp_left]
  exact mixtureKernel_product μ ν _

theorem costedCarryKernel_mixture (μ : Measure I) [IsProbabilityMeasure μ]
    (L : I → Kernel X (Y × ℕ)) [∀ i, IsMarkovKernel (L i)] :
    costedCarryKernel (mixtureKernel μ L) = mixtureKernel μ (fun i => costedCarryKernel (L i)) := by
  apply Kernel.ext
  rintro ⟨x, c⟩
  apply Measure.ext
  intro A hA
  have hf : Measurable (fun z : Y × ℕ => (z.1, c + z.2)) := measurable_fst.prodMk (measurable_const.add measurable_snd)
  rw [costedCarryKernel, costedUpdateKernel_apply _ _ measurable_snd _ measurable_snd, Kernel.comap_apply,
    Measure.map_apply hf hA, mixtureKernel_apply μ L x (hf hA), mixtureKernel_apply μ _ (x, c) hA]
  apply lintegral_congr
  intro i
  rw [costedCarryKernel, costedUpdateKernel_apply _ _ measurable_snd _ measurable_snd,
    Kernel.comap_apply, Measure.map_apply hf hA]

theorem costedCompose_mixture (μ : Measure I) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (L : I → Kernel X (Y × ℕ)) [∀ i, IsMarkovKernel (L i)]
    (R : J → Kernel Y (Z × ℕ)) [∀ j, IsMarkovKernel (R j)] :
    costedCompose (mixtureKernel μ L) (mixtureKernel ν R) =
      mixtureKernel (μ.prod ν) (fun s => costedCompose (L s.1) (R s.2)) := by
  rw [costedCompose, costedCarryKernel_mixture, mixtureKernel_comp]
  rfl

theorem costedCompose_tagged (L : Kernel X Y) [IsMarkovKernel L] (R : Kernel Y Z) [IsMarkovKernel R]
    (t n : ℕ) : costedCompose (taggedKernel L t) (taggedKernel R n) = taggedKernel (R ∘ₖ L) (t + n) := by
  have h : (costedCarryKernel (taggedKernel R n)).comap (fun y => (y, t)) (measurable_id.prodMk measurable_const) =
      taggedKernel R (t + n) := by
    apply Kernel.ext
    intro y
    rw [Kernel.comap_apply, costedCarryKernel, costedUpdateKernel_apply _ _ measurable_snd _ measurable_snd,
      Kernel.comap_apply, taggedKernel,
      Kernel.map_apply (f := fun z : Z => (z, n)) _ (measurable_id.prodMk measurable_const),
      Measure.map_map (f := fun z : Z => (z, n)) (g := fun z : Z × ℕ => (z.1, t + z.2))
        (measurable_fst.prodMk (measurable_const.add measurable_snd)) (measurable_id.prodMk measurable_const), taggedKernel,
      Kernel.map_apply (f := fun z : Z => (z, t + n)) _ (measurable_id.prodMk measurable_const)]
    rfl
  change costedCarryKernel (taggedKernel R n) ∘ₖ L.map (fun y => (y, t)) = _
  rw [Kernel.comp_map (f := fun y : Y => (y, t)) _ _ (measurable_id.prodMk measurable_const), h]
  simp only [taggedKernel, Kernel.map_comp]

end FreshGradientMinimax
