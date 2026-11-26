import Nonsmooth.ConditionalSupportUpdate
import Nonsmooth.ConditionalReencoding

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem supportPosteriorKernel_initial {k : ℕ} [Nonempty (Fin k)]
    (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (h : SupportHistory E k 0) :
    supportPosteriorKernel Q p ω 0 h = Q := by
  have hF : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω 0) := measurable_const
  have hset : {a : Fin k → E | supportAugmentedTranscript p a ω 0 = h} = Set.univ := by
    ext a
    exact ⟨fun _ => mem_univ a, fun _ => Subsingleton.elim _ _⟩
  have ha : Q.map (fun a => supportAugmentedTranscript p a ω 0) {h} ≠ 0 := by
    rw [Measure.map_apply hF (measurableSet_singleton h)]
    change Q {a | supportAugmentedTranscript p a ω 0 = h} ≠ 0
    rw [hset, measure_univ]
    exact one_ne_zero
  rw [supportPosteriorKernel_at_atom Q p hp ω 0 h ha, hset, cond_univ]

/-- After any finite measurable adaptive transcript, independent rows remain conditionally independent. -/
theorem supportPosteriorKernel_independent_succ_rows {r : ℕ}
    (μ : Fin (r + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    ∀ᵐ h ∂(Measure.pi μ).map (fun a => supportAugmentedTranscript p a ω n),
      iIndepFun (fun i (a : Fin (r + 1) → E) => a i)
        (supportPosteriorKernel (Measure.pi μ) p ω n h) := by
  induction n with
  | zero =>
    apply Eventually.of_forall
    intro h
    rw [supportPosteriorKernel_initial _ p hp ω h]
    exact finiteProductKernel_independent (fun i => Kernel.const Unit (μ i)) ()
  | succ n ih =>
    let H := SupportHistory E (r + 1) n
    let Q := Measure.pi μ
    let prev : (Fin (r + 1) → E) → H := fun a => supportAugmentedTranscript p a ω n
    let u : H → E := fun h => p.query n ω (p.stateOnHistory ω n (supportEraseHistory h))
    have hprev : Measurable prev :=
      (supportAugmentedTranscript_measurable p hp n).comp (measurable_id.prodMk measurable_const)
    have hu : Measurable u := (hp.query n).comp (measurable_const.prodMk
      ((stateOnHistory_measurable hp n).comp
        (measurable_const.prodMk (supportEraseHistory_measurable n))))
    let X : (Fin (r + 1) → E) → H × (Fin (r + 1) × ℝ) :=
      fun a => (prev a, supportSingleObservation (u (prev a)) a)
    let Z : (Fin (r + 1) → E) → SupportHistory E (r + 1) (n + 1) :=
      fun a => supportAugmentedTranscript p a ω (n + 1)
    have hZ : Measurable Z :=
      (supportAugmentedTranscript_measurable p hp (n + 1)).comp (measurable_id.prodMk measurable_const)
    let f : H × (Fin (r + 1) × ℝ) → SupportHistory E (r + 1) (n + 1) :=
      fun z => Fin.snoc z.1 (u z.1, z.2)
    let g : SupportHistory E (r + 1) (n + 1) → H × (Fin (r + 1) × ℝ) :=
      fun h => (Fin.init h, (h (Fin.last n)).2)
    have hf : Measurable f := by
      apply measurable_pi_lambda
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [f, Fin.snoc_last, Function.comp_def] using
          (hu.comp measurable_fst).prodMk measurable_snd
      · simpa only [f, Fin.snoc_castSucc, Function.comp_def] using
          (measurable_pi_apply j).comp measurable_fst
    have hinit : Measurable (fun h : SupportHistory E (r + 1) (n + 1) => Fin.init h) := by
      apply measurable_pi_lambda
      intro i
      exact measurable_pi_apply i.castSucc
    have hg : Measurable g := hinit.prodMk (measurable_pi_apply (Fin.last n)).snd
    have hZX (a : Fin (r + 1) → E) : Z a = f (X a) := rfl
    have hXZ (a : Fin (r + 1) → E) : g (Z a) = X a := by
      simp only [g, Z, supportAugmentedTranscript, Fin.init_snoc, Fin.snoc_last]
      rfl
    have hX : Measurable X := by
      have he : X = g ∘ Z := funext (fun a => (hXZ a).symm)
      rw [he]
      exact hg.comp hZ
    have hnew : ∀ᵐ x ∂Q.map X,
        iIndepFun (fun i (a : Fin (r + 1) → E) => a i) (condDistrib id X Q x) :=
      support_conditional_independence_update Q prev hprev u hu ih
    exact condDistrib_property_reencoding Q X hX id measurable_id Z hZ f hf g hg hZX hXZ
      (fun ν => iIndepFun (fun i (a : Fin (r + 1) → E) => a i) ν) hnew

theorem supportPosteriorKernel_independent {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    ∀ᵐ h ∂(Measure.pi μ).map (fun a => supportAugmentedTranscript p a ω n),
      iIndepFun (fun i (a : Fin k → E) => a i) (supportPosteriorKernel (Measure.pi μ) p ω n h) := by
  cases k with
  | zero => exact (Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0))))
  | succ r => exact supportPosteriorKernel_independent_succ_rows μ p hp ω n

theorem supportPosteriorKernel_product_marginals {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    ∀ᵐ h ∂(Measure.pi μ).map (fun a => supportAugmentedTranscript p a ω n),
      supportPosteriorKernel (Measure.pi μ) p ω n h =
        Measure.pi (fun i => (supportPosteriorKernel (Measure.pi μ) p ω n h).map (fun a => a i)) := by
  filter_upwards [supportPosteriorKernel_independent μ p hp ω n] with h hh
  have he := (independent_iff_productMarginalKernel (supportPosteriorKernel (Measure.pi μ) p ω n) h).mp hh
  rwa [productMarginalKernel_apply] at he

end
end Nonsmooth
