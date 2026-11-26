import Mathlib

/-!
Measure-preserving past-dependent orbit symmetries. The finite-selector
pasting theorem below is a constructive first step toward arbitrary measurable
stabilizer selections; no posterior identity is assumed.
-/

open MeasureTheory Set

namespace Task006.AdaptiveSphereOrbit

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] {μ : Measure Ω}

/-- A finite measurable choice among measure-preserving transformations still
preserves the measure when the choice is invariant under every transformation.
This is the past-dependent symmetry/pasting step, not a posterior assumption. -/
theorem finite_invariant_selector_measurePreserving
    (selector : Ω → ι) (hselector : Measurable selector)
    (T : ι → Ω → Ω) (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hinv : ∀ i ω, selector (T i ω) = selector ω)
    (htwist : Measurable (fun ω => T (selector ω) ω)) :
    MeasurePreserving (fun ω => T (selector ω) ω) μ μ := by
  classical
  let fiber : ι → Set Ω := fun i => selector ⁻¹' {i}
  have hfiber (i : ι) : MeasurableSet (fiber i) :=
    hselector (measurableSet_singleton i)
  have hdisjoint (A : ι → Set Ω) (hA : ∀ i, A i ⊆ fiber i) :
      PairwiseDisjoint (↑(Finset.univ : Finset ι)) A := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro ω hωi hωj
    have hei : selector ω = i := by
      simpa only [fiber, mem_preimage, mem_singleton_iff] using (hA i hωi)
    have hej : selector ω = j := by
      simpa only [fiber, mem_preimage, mem_singleton_iff] using (hA j hωj)
    exact hij (hei.symm.trans hej)
  refine ⟨htwist, ?_⟩
  ext s hs
  have hpre : (fun ω => T (selector ω) ω) ⁻¹' s =
      ⋃ i ∈ (Finset.univ : Finset ι), fiber i ∩ (T i ⁻¹' s) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, Finset.mem_univ, exists_prop, true_and, mem_inter_iff]
    constructor
    · intro h
      exact ⟨selector ω, by simp [fiber], h⟩
    · rintro ⟨i, hi, hTi⟩
      have hsi : selector ω = i := by simpa [fiber] using hi
      simpa only [hsi] using hTi
  have hcomp (i : ι) : fiber i ∩ (T i ⁻¹' s) = T i ⁻¹' (fiber i ∩ s) := by
    ext ω
    simp only [fiber, mem_inter_iff, mem_preimage, mem_singleton_iff, hinv]
  have hunion : (⋃ i ∈ (Finset.univ : Finset ι), fiber i ∩ s) = s := by
    ext ω
    simp only [mem_iUnion, Finset.mem_univ, exists_prop, true_and, mem_inter_iff]
    constructor
    · rintro ⟨i, hi, hsi⟩
      exact hsi
    · intro h
      exact ⟨selector ω, by simp [fiber], h⟩
  rw [Measure.map_apply htwist hs, hpre,
    measure_biUnion_finset
      (hdisjoint (fun i => fiber i ∩ (T i ⁻¹' s)) (fun _ => inter_subset_left))
      (fun i _ => (hfiber i).inter ((hT i).measurable hs))]
  calc
    (∑ i ∈ (Finset.univ : Finset ι), μ (fiber i ∩ (T i ⁻¹' s))) =
        ∑ i ∈ (Finset.univ : Finset ι), μ (fiber i ∩ s) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcomp]
      exact (hT i).measure_preimage ((hfiber i).inter hs).nullMeasurableSet
    _ = μ (⋃ i ∈ (Finset.univ : Finset ι), fiber i ∩ s) :=
      (measure_biUnion_finset
        (hdisjoint (fun i => fiber i ∩ s) (fun _ => inter_subset_left))
        (fun i _ => (hfiber i).inter hs)).symm
    _ = μ s := by rw [hunion]

section PointwiseLimits

variable [TopologicalSpace Ω] [BorelSpace Ω] [HasOuterApproxClosed Ω]
  [IsFiniteMeasure μ]

/-- A pointwise topological limit of measure-preserving maps preserves a finite
Borel measure, provided the limiting map is measurable. -/
theorem measurePreserving_of_pointwise_limit
    (T : ℕ → Ω → Ω) (hT : ∀ n, MeasurePreserving (T n) μ μ)
    (limit : Ω → Ω) (hlimit : Measurable limit)
    (hconv : ∀ ω, Filter.Tendsto (fun n => T n ω) Filter.atTop (nhds (limit ω))) :
    MeasurePreserving limit μ μ := by
  refine ⟨hlimit, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hlimit.aemeasurable f.continuous.aestronglyMeasurable]
  have hdom := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp (hT n).measurable).aestronglyMeasurable)
    (integrable_const ‖f‖)
    (fun n => Filter.Eventually.of_forall (fun ω => f.norm_coe_le_norm (T n ω)))
    (Filter.Eventually.of_forall (fun ω =>
      (f.continuous.tendsto (limit ω)).comp (hconv ω)))
  have hchange (n : ℕ) : (∫ ω, f (T n ω) ∂μ) = ∫ ω, f ω ∂μ := by
    calc
      _ = ∫ ω, f ω ∂Measure.map (T n) μ :=
        (integral_map (hT n).measurable.aemeasurable
          f.continuous.aestronglyMeasurable).symm
      _ = _ := by rw [(hT n).map_eq]
  have heq : (fun n => ∫ ω, f (T n ω) ∂μ) = (fun _ : ℕ => ∫ ω, f ω ∂μ) := by
    funext n
    exact hchange n
  simp only [Function.comp_apply] at hdom
  rw [heq] at hdom
  exact (tendsto_nhds_unique tendsto_const_nhds hdom).symm

variable {G : Type*} [MeasurableSpace G] [TopologicalSpace G]
  [TopologicalSpace.PseudoMetrizableSpace G] [T1Space G] [SecondCountableTopology G] [BorelSpace G]

/-- Arbitrary measurable orbit-invariant choices of a probability-space
symmetry preserve the measure. Finite invariant partition pasting and dominated
convergence prove this; the conclusion is not an assumed posterior property. -/
theorem invariant_selector_measurePreserving
    (selector : Ω → G) (hselector : Measurable selector)
    (T : G → Ω → Ω) (hT : ∀ g, MeasurePreserving (T g) μ μ)
    (hjoint : Measurable (fun p : G × Ω => T p.1 p.2))
    (hcont : ∀ ω, Continuous (fun g => T g ω))
    (hinv : ∀ g ω, selector (T g ω) = selector ω) :
    MeasurePreserving (fun ω => T (selector ω) ω) μ μ := by
  classical
  have hid : StronglyMeasurable (id : G → G) := measurable_id.stronglyMeasurable
  let approx : ℕ → SimpleFunc G G := hid.approx
  let twists : ℕ → Ω → Ω := fun n ω => T (approx n (selector ω)) ω
  have htwists (n : ℕ) : MeasurePreserving (twists n) μ μ := by
    let Choice : Type _ := ↥(approx n).range
    let choice : Ω → Choice := fun ω =>
      ⟨approx n (selector ω), (approx n).mem_range_self (selector ω)⟩
    have hchoice : Measurable choice := by
      exact Measurable.subtype_mk ((approx n).measurable.comp hselector)
    have hmeas : Measurable (fun ω => T (approx n (selector ω)) ω) :=
      hjoint.comp (((approx n).measurable.comp hselector).prodMk measurable_id)
    apply finite_invariant_selector_measurePreserving choice hchoice
      (fun g : Choice => T g.val) (fun g => hT g.val) _ hmeas
    intro g ω
    apply Subtype.ext
    change approx n (selector (T g.val ω)) = approx n (selector ω)
    rw [hinv]
  apply measurePreserving_of_pointwise_limit twists htwists
    (fun ω => T (selector ω) ω) (hjoint.comp (hselector.prodMk measurable_id))
  intro ω
  exact (hcont ω).tendsto (selector ω) |>.comp (hid.tendsto_approx (selector ω))

/-- A measurable control depending only on an invariant observable is an
admissible measure-preserving past-dependent symmetry. -/
theorem observable_dependent_symmetry_measurePreserving
    {H : Type*} [MeasurableSpace H]
    (obs : Ω → H) (hobs : Measurable obs)
    (control : H → G) (hcontrol : Measurable control)
    (T : G → Ω → Ω) (hT : ∀ g, MeasurePreserving (T g) μ μ)
    (hjoint : Measurable (fun p : G × Ω => T p.1 p.2))
    (hcont : ∀ ω, Continuous (fun g => T g ω))
    (hfix : ∀ g ω, obs (T g ω) = obs ω) :
    MeasurePreserving (fun ω => T (control (obs ω)) ω) μ μ := by
  apply invariant_selector_measurePreserving (control ∘ obs)
    (hcontrol.comp hobs) T hT hjoint hcont
  intro g ω
  simp only [Function.comp_apply, hfix]

end PointwiseLimits

#print axioms finite_invariant_selector_measurePreserving
#print axioms measurePreserving_of_pointwise_limit
#print axioms invariant_selector_measurePreserving
#print axioms observable_dependent_symmetry_measurePreserving

end
end Task006.AdaptiveSphereOrbit
