import UpperGhostKernel

/-! Finite analysis-only common-first-proposal process. Its failure flag records
every rejected first proposal, even after the first divergence. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

namespace Task006.Full

abbrev GhostState (E : Type*) := (E × E) × Bool

def ghostFailed {E : Type*} : Set (GhostState E) := {j | j.2 = true}

theorem measurableSet_ghostFailed {E : Type*} [MeasurableSpace E] :
    MeasurableSet (@ghostFailed E) :=
  (measurableSet_singleton true).preimage measurable_snd

abbrev ghostGoodOnState {E B : Type*} (G : E → Set B) (j : GhostState E) : Set B := G j.1.2

theorem ghostGoodOnState_measurable {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    {G : E → Set B} (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) :
    MeasurableSet {p : GhostState E × B | p.2 ∈ ghostGoodOnState G p.1} :=
  hG.preimage (((measurable_snd.comp measurable_fst).comp measurable_fst).prodMk measurable_snd)

noncomputable def ghostUpdate {E B : Type*} (G : E → Set B) (step : E × B → E)
    (z : GhostState E × (B × B)) : GhostState E := by
  classical
  exact ((step (z.1.1.1, z.2.1),
    step (z.1.1.2, acceptedProposal (G z.1.1.2) z.2)),
      if z.2.1 ∈ G z.1.1.2 then z.1.2 else true)

theorem ghostUpdate_measurable {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (G : E → Set B) (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (step : E × B → E) (hstep : Measurable step) : Measurable (ghostUpdate G step) := by
  classical
  have hact : Measurable (fun z : GhostState E × (B × B) => z.1.1.1) := by fun_prop
  have hghost : Measurable (fun z : GhostState E × (B × B) => z.1.1.2) := by fun_prop
  have hfirst : Measurable (fun z : GhostState E × (B × B) => z.2.1) := by fun_prop
  have hprop := hG.preimage (hghost.prodMk hfirst)
  have haccepted : Measurable (fun z : GhostState E × (B × B) =>
      acceptedProposal (G z.1.1.2) z.2) :=
    (adaptiveAcceptedProposal_measurable G hG).comp (hghost.prodMk measurable_snd)
  exact ((hstep.comp (hact.prodMk hfirst)).prodMk
    (hstep.comp (hghost.prodMk haccepted))).prodMk
      (Measurable.ite hprop (measurable_snd.comp measurable_fst) measurable_const)

noncomputable def ghostTransition {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) :
    Kernel (GhostState E) (GhostState E) := by
  let good := goodProposalKernel μ (ghostGoodOnState G) (ghostGoodOnState_measurable hG)
  letI : IsMarkovKernel good := goodProposalKernel_markov μ _ _ (fun j => hpos j.1.2)
  exact (Kernel.id ×ₖ (Kernel.const (GhostState E) μ ×ₖ good)).map (ghostUpdate G step)

theorem ghostTransition_markov {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) :
    IsMarkovKernel (ghostTransition μ G hG hpos step hstep) := by
  letI := goodProposalKernel_markov μ (ghostGoodOnState G) (ghostGoodOnState_measurable hG)
    (fun j => hpos j.1.2)
  unfold ghostTransition
  exact Kernel.IsMarkovKernel.map _ (ghostUpdate_measurable G hG step hstep)

theorem ghostTransition_apply {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (j : GhostState E) :
    ghostTransition μ G hG hpos step hstep j =
      (μ.prod (goodRestrictedLaw μ (G j.1.2))).map (fun p => ghostUpdate G step (j, p)) := by
  let good := goodProposalKernel μ (ghostGoodOnState G) (ghostGoodOnState_measurable hG)
  letI : IsMarkovKernel good := goodProposalKernel_markov μ _ _ (fun j => hpos j.1.2)
  letI := goodRestrictedLaw_probability μ (G j.1.2) (hpos j.1.2)
  change ((Kernel.id ×ₖ (Kernel.const (GhostState E) μ ×ₖ good)).map (ghostUpdate G step)) j = _
  rw [Kernel.map_apply _ (ghostUpdate_measurable G hG step hstep), Kernel.prod_apply,
    Kernel.id_apply, Kernel.prod_apply, Kernel.const_apply, goodProposalKernel_apply,
    Measure.dirac_prod, Measure.map_map (ghostUpdate_measurable G hG step hstep) measurable_prodMk_left]
  rfl

theorem ghostTransition_failure {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (j : GhostState E) :
    ghostTransition μ G hG hpos step hstep j ghostFailed =
      if j.2 = true then 1 else μ (G j.1.2)ᶜ := by
  classical
  letI := goodRestrictedLaw_probability μ (G j.1.2) (hpos j.1.2)
  have hm : Measurable (fun p : B × B => ghostUpdate G step (j, p)) :=
    (ghostUpdate_measurable G hG step hstep).comp measurable_prodMk_left
  rw [ghostTransition_apply, Measure.map_apply hm measurableSet_ghostFailed]
  by_cases hj : j.2 = true
  · rw [if_pos hj]
    have heq : (fun p => ghostUpdate G step (j, p)) ⁻¹' ghostFailed = univ := by
      ext p
      simp [ghostFailed, ghostUpdate, hj]
    rw [heq, measure_univ]
  · rw [if_neg hj]
    have heq : (fun p => ghostUpdate G step (j, p)) ⁻¹' ghostFailed = (G j.1.2)ᶜ ×ˢ univ := by
      ext p
      simp [ghostFailed, ghostUpdate, hj]
    rw [heq, Measure.prod_prod, measure_univ, mul_one]

theorem ghostUpdate_agreement {E B : Type*} (G : E → Set B) (step : E × B → E)
    (j : GhostState E) (p : B × B) (hj : j.2 = false → j.1.1 = j.1.2) :
    (ghostUpdate G step (j, p)).2 = false →
      (ghostUpdate G step (j, p)).1.1 = (ghostUpdate G step (j, p)).1.2 := by
  classical
  by_cases hp : p.1 ∈ G j.1.2
  · simp only [ghostUpdate, if_pos hp, Prod.fst, Prod.snd, acceptedProposal_agrees _ _ hp]
    intro hf
    rw [hj hf]
  · simp only [ghostUpdate, if_neg hp, Prod.snd, Bool.true_eq_false, false_implies]

#print axioms ghostTransition
#print axioms ghostTransition_failure
#print axioms ghostUpdate_agreement

end Task006.Full
