import Nonsmooth.FiniteFirstIntegral

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal Function
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {n : ℕ}

def supportSingleObservation {k : ℕ} [Nonempty (Fin k)] (u : E) (a : Fin k → E) : Fin k × ℝ :=
  (supportWinner a u, finiteSupport a u)

theorem supportSingleObservation_measurable {k : ℕ} [Nonempty (Fin k)] (u : E) :
    Measurable (supportSingleObservation (k := k) u) := by
  have hp : Measurable (fun a : Fin k → E => (a, u)) := measurable_id.prodMk measurable_const
  exact ((supportWinner_measurable (E := E) (k := k)).comp hp).prodMk
    ((finiteSupport_joint_continuous (E := E) (ι := Fin k)).measurable.comp hp)

theorem supportSelectionValueLaw_eq
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin (n + 1)) :
    supportSelectionValueLaw μ u w =
      ((((Measure.pi μ).map (supportSingleObservation u)).restrict (Prod.fst ⁻¹' {w})).map Prod.snd) := by
  ext D hD
  rw [supportSelectionValueLaw_apply μ u w hD,
    Measure.map_apply measurable_snd hD,
    Measure.restrict_apply (measurable_snd hD),
    Measure.map_apply (supportSingleObservation_measurable u)
      ((measurable_snd hD).inter (measurable_fst (measurableSet_singleton w)))]
  congr 1
  ext a
  exact and_comm

instance supportSelectionValueLaw_finite
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin (n + 1)) : IsFiniteMeasure (supportSelectionValueLaw μ u w) := by
  rw [supportSelectionValueLaw_eq μ u w]
  infer_instance

theorem supportSelectionKernel_disintegration_observation_set
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    {S : Set (Fin (n + 1) × ℝ)} (hS : MeasurableSet S)
    {B : Set (Fin (n + 1) → E)} (hB : MeasurableSet B) :
    Measure.pi μ ((supportSingleObservation u ⁻¹' S) ∩ B) =
      ∫⁻ h in S, supportSelectionKernel μ u h B ∂((Measure.pi μ).map (supportSingleObservation u)) := by
  let H (w : Fin (n + 1)) : Set (Fin (n + 1) → E) :=
    {a | supportWinner a u = w ∧ finiteSupport a u ∈ Prod.mk w ⁻¹' S} ∩ B
  have hO := supportSingleObservation_measurable (E := E) (k := n + 1) u
  have hH (w : Fin (n + 1)) : MeasurableSet (H w) :=
    ((hO.fst (measurableSet_singleton w)).inter
      (hO.snd (measurable_prodMk_left hS))).inter hB
  have hd : Pairwise (Disjoint on H) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro a hi hj
    exact hij (hi.1.1.symm.trans hj.1.1)
  have hu : (supportSingleObservation u ⁻¹' S) ∩ B = ⋃ w, H w := by
    ext a
    constructor
    · intro ha
      exact mem_iUnion.mpr ⟨supportWinner a u, ⟨rfl, ha.1⟩, ha.2⟩
    · intro ha
      obtain ⟨w, hwa⟩ := mem_iUnion.mp ha
      have hw := hwa.1.1
      have hy := hwa.1.2
      refine ⟨?_, hwa.2⟩
      change (supportWinner a u, finiteSupport a u) ∈ S
      rw [hw]
      exact hy
  rw [hu, measure_iUnion hd hH,
    finite_first_setLIntegral _ hS _ (Kernel.measurable_coe _ hB)]
  apply tsum_congr
  intro w
  rw [← supportSelectionValueLaw_eq μ u w]
  exact supportSelectionKernel_disintegration_set μ u w (measurable_prodMk_left hS) hB

/-- Exact disintegration of the joint observation/row law, with no positivity assumption on fibers. -/
theorem supportSelectionKernel_disintegrates
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    (Measure.pi μ).map (fun a => (supportSingleObservation u a, a)) =
      ((Measure.pi μ).map (supportSingleObservation u)) ⊗ₘ supportSelectionKernel μ u := by
  have hO := supportSingleObservation_measurable (E := E) (k := n + 1) u
  have hpair : Measurable (fun a : Fin (n + 1) → E => (supportSingleObservation u a, a)) :=
    hO.prodMk measurable_id
  apply ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod
  · rintro _ ⟨S, hS, B, hB, rfl⟩
    change MeasurableSet S at hS
    change MeasurableSet B at hB
    rw [Measure.map_apply hpair (hS.prod hB),
      Measure.compProd_apply_prod hS hB]
    exact supportSelectionKernel_disintegration_observation_set μ u hS hB
  · rw [Measure.map_apply hpair MeasurableSet.univ,
      preimage_univ, Measure.compProd_apply_univ,
      Measure.map_apply hO MeasurableSet.univ, preimage_univ]

/-- The constructed product kernel is a version of the actual regular conditional distribution. -/
theorem supportSelectionKernel_ae_eq_condDistrib
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u),
      supportSelectionKernel μ u h = condDistrib id (supportSingleObservation u) (Measure.pi μ) h :=
  (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (supportSingleObservation_measurable u) measurable_id
    (supportSelectionKernel_disintegrates μ u)).symm

theorem supportSingleObservation_posterior_independent
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u),
      iIndepFun (fun i (a : Fin (n + 1) → E) => a i)
        (condDistrib id (supportSingleObservation u) (Measure.pi μ) h) := by
  filter_upwards [supportSelectionKernel_ae_eq_condDistrib μ u] with h hh
  rw [← hh]
  exact supportSelectionKernel_independent μ u h.1 h.2

end
end Nonsmooth
