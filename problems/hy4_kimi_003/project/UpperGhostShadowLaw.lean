import UpperGhostMarginal
import UpperGhostFeasible

/-! Exact adaptive normalized-good Markov law of the ghost marginal. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Metric
namespace Task006.Full

noncomputable def goodStepKernel {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) (step : E × B → E) : Kernel E E :=
  (Kernel.id ×ₖ goodProposalKernel μ G hG).map step

theorem goodStepKernel_markov {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) (hpos : ∀ x, μ (G x) ≠ 0)
    (step : E × B → E) (hstep : Measurable step) : IsMarkovKernel (goodStepKernel μ G hG step) := by
  letI := goodProposalKernel_markov μ G hG hpos
  exact Kernel.IsMarkovKernel.map _ hstep

theorem goodStepKernel_apply {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) (hpos : ∀ x, μ (G x) ≠ 0)
    (step : E × B → E) (hstep : Measurable step) (x : E) :
    goodStepKernel μ G hG step x = (goodRestrictedLaw μ (G x)).map (fun b => step (x, b)) := by
  letI := goodProposalKernel_markov μ G hG hpos
  letI := goodRestrictedLaw_probability μ (G x) (hpos x)
  rw [goodStepKernel, Kernel.map_apply _ hstep, Kernel.prod_apply, Kernel.id_apply, goodProposalKernel_apply,
    Measure.dirac_prod, Measure.map_map hstep measurable_prodMk_left]
  rfl

noncomputable def goodStateLaw {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) (step : E × B → E) (x0 : E) : ℕ → Measure E
  | 0 => Measure.dirac x0
  | n + 1 => goodStepKernel μ G hG step ∘ₘ goodStateLaw μ G hG step x0 n

theorem goodStateLaw_probability {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) (hpos : ∀ x, μ (G x) ≠ 0)
    (step : E × B → E) (hstep : Measurable step) (x0 : E) (n : ℕ) :
    IsProbabilityMeasure (goodStateLaw μ G hG step x0 n) := by
  letI := goodStepKernel_markov μ G hG hpos step hstep
  induction n with
  | zero => rw [goodStateLaw]; infer_instance
  | succ n ih => rw [goodStateLaw]; infer_instance

theorem ghostProcess_ghost_marginal {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E) (n : ℕ) :
    (ghostProcessLaw μ G hG hpos step hstep x0 n).map (fun j => j.1.2) =
      goodStateLaw μ G hG step x0 n := by
  have hghost : Measurable (fun j : GhostState E => j.1.2) := measurable_snd.comp measurable_fst
  have hcomm : (ghostTransition μ G hG hpos step hstep).map (fun j => j.1.2) =
      goodStepKernel μ G hG step ∘ₖ Kernel.deterministic (fun j : GhostState E => j.1.2) hghost := by
    rw [Kernel.comp_deterministic_eq_comap]
    apply Kernel.ext
    intro j
    rw [Kernel.map_apply _ hghost, Kernel.comap_apply, goodStepKernel_apply μ G hG hpos step hstep]
    exact ghostTransition_ghost_map μ G hG hpos step hstep j
  induction n with
  | zero => rw [ghostProcessLaw, goodStateLaw, Measure.map_dirac' hghost]
  | succ n ih =>
    rw [ghostProcessLaw, Measure.map_comp _ _ hghost, hcomm, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map hghost, ih, goodStateLaw]

theorem goodStateLaw_upperStep_feasible {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : UpperProgramParameters) (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (ν : Measure (UpperSampleBlock d Ω)) [IsProbabilityMeasure ν]
    (G : UpperGhostState d → Set (UpperSampleBlock d Ω))
    (hG : MeasurableSet {p : UpperGhostState d × UpperSampleBlock d Ω | p.2 ∈ G p.1})
    (hpos : ∀ x, ν (G x) ≠ 0) (n : ℕ) :
    ∀ᵐ x ∂goodStateLaw ν G hG (upperGhostStep P F) (0, 0) n,
      ‖x.1‖ ≤ P.R - (P.ρ + P.δ) ∧ ‖x.2‖ ≤ n * (P.R - (P.ρ + P.δ)) := by
  rw [← ghostProcess_ghost_marginal ν G hG hpos _ (upperGhostStep_measurable P hF)]
  have hm : Measurable (fun j : GhostState (UpperGhostState d) => j.1.2) := measurable_snd.comp measurable_fst
  have hs1 : MeasurableSet {x : UpperGhostState d | ‖x.1‖ ≤ P.R - (P.ρ + P.δ)} :=
    measurableSet_le measurable_fst.norm measurable_const
  have hs2 : MeasurableSet {x : UpperGhostState d | ‖x.2‖ ≤ n * (P.R - (P.ρ + P.δ))} :=
    measurableSet_le measurable_snd.norm measurable_const
  have hs : MeasurableSet {x : UpperGhostState d | ‖x.1‖ ≤ P.R - (P.ρ + P.δ) ∧
      ‖x.2‖ ≤ n * (P.R - (P.ρ + P.δ))} := hs1.inter hs2
  apply (ae_map_iff hm.aemeasurable hs).mpr
  exact (ghostProcess_upperStep_feasible P F hF ν G hG hpos n).mono (fun j hj => ⟨hj.2.1, hj.2.2.2⟩)

#print axioms ghostProcess_ghost_marginal
end Task006.Full
