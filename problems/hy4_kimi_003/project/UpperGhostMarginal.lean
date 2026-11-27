import UpperGhostFinite

/-! Exact actual and ghost one-step marginals of the finite coupling. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace Task006.Full

theorem ghostTransition_actual_map {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (j : GhostState E) :
    (ghostTransition μ G hG hpos step hstep j).map (fun j' => j'.1.1) =
      μ.map (fun b => step (j.1.1, b)) := by
  letI := goodRestrictedLaw_probability μ (G j.1.2) (hpos j.1.2)
  have hu : Measurable (fun p : B × B => ghostUpdate G step (j, p)) :=
    (ghostUpdate_measurable G hG step hstep).comp measurable_prodMk_left
  have hs : Measurable (fun b => step (j.1.1, b)) := hstep.comp measurable_prodMk_left
  have ha : Measurable (fun j' : GhostState E => j'.1.1) := measurable_fst.comp measurable_fst
  rw [ghostTransition_apply, Measure.map_map ha hu]
  have hcomp : (fun p : B × B => (ghostUpdate G step (j, p)).1.1) =
      (fun b => step (j.1.1, b)) ∘ Prod.fst := rfl
  change (μ.prod (goodRestrictedLaw μ (G j.1.2))).map (fun p => (ghostUpdate G step (j, p)).1.1) = _
  rw [hcomp, ← Measure.map_map hs measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

theorem ghostTransition_ghost_map {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (j : GhostState E) :
    (ghostTransition μ G hG hpos step hstep j).map (fun j' => j'.1.2) =
      (goodRestrictedLaw μ (G j.1.2)).map (fun b => step (j.1.2, b)) := by
  letI := goodRestrictedLaw_probability μ (G j.1.2) (hpos j.1.2)
  have hu : Measurable (fun p : B × B => ghostUpdate G step (j, p)) :=
    (ghostUpdate_measurable G hG step hstep).comp measurable_prodMk_left
  have hGx : MeasurableSet (G j.1.2) := hG.preimage measurable_prodMk_left
  have hacc : Measurable (acceptedProposal (G j.1.2)) := acceptedProposal_measurable hGx
  have hs : Measurable (fun b => step (j.1.2, b)) := hstep.comp measurable_prodMk_left
  have ha : Measurable (fun j' : GhostState E => j'.1.2) := measurable_snd.comp measurable_fst
  rw [ghostTransition_apply, Measure.map_map ha hu]
  have hcomp : (fun p : B × B => (ghostUpdate G step (j, p)).1.2) =
      (fun b => step (j.1.2, b)) ∘ acceptedProposal (G j.1.2) := rfl
  change (μ.prod (goodRestrictedLaw μ (G j.1.2))).map (fun p => (ghostUpdate G step (j, p)).1.2) = _
  rw [hcomp, ← Measure.map_map hs hacc, acceptedProposal_map μ hGx (hpos j.1.2)]

noncomputable def iidStepKernel {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) (step : E × B → E) : Kernel E E :=
  (Kernel.id ×ₖ Kernel.const E μ).map step

theorem iidStepKernel_apply {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (step : E × B → E) (hstep : Measurable step) (x : E) :
    iidStepKernel μ step x = μ.map (fun b => step (x, b)) := by
  rw [iidStepKernel, Kernel.map_apply _ hstep, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hstep measurable_prodMk_left]
  rfl

theorem iidStepKernel_comp_eq_map_prod {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (step : E × B → E) (hstep : Measurable step)
    (ν : Measure E) [SFinite ν] :
    iidStepKernel μ step ∘ₘ ν = (ν.prod μ).map step := by
  rw [iidStepKernel, ← Measure.map_comp ν _ hstep, ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

noncomputable def iidStateLaw {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) (step : E × B → E) (x0 : E) : ℕ → Measure E
  | 0 => Measure.dirac x0
  | n + 1 => iidStepKernel μ step ∘ₘ iidStateLaw μ step x0 n

theorem ghostProcess_actual_marginal {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E) (n : ℕ) :
    (ghostProcessLaw μ G hG hpos step hstep x0 n).map (fun j => j.1.1) = iidStateLaw μ step x0 n := by
  have hact : Measurable (fun j : GhostState E => j.1.1) := measurable_fst.comp measurable_fst
  have hcomm : (ghostTransition μ G hG hpos step hstep).map (fun j => j.1.1) =
      iidStepKernel μ step ∘ₖ Kernel.deterministic (fun j : GhostState E => j.1.1) hact := by
    rw [Kernel.comp_deterministic_eq_comap]
    apply Kernel.ext
    intro j
    rw [Kernel.map_apply _ hact, Kernel.comap_apply, iidStepKernel_apply μ step hstep]
    exact ghostTransition_actual_map μ G hG hpos step hstep j
  induction n with
  | zero =>
    rw [ghostProcessLaw, iidStateLaw, Measure.map_dirac' hact]
  | succ n ih =>
    rw [ghostProcessLaw, Measure.map_comp _ _ hact, hcomm, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map hact, ih, iidStateLaw]

#print axioms ghostTransition_ghost_map
#print axioms ghostProcess_actual_marginal
end Task006.Full
