import Mathlib.MeasureTheory.Measure.Prod

/-! # Finite adaptive completion from exact local joint identities

The tape consists of independent fresh draws and one final completion draw.
An exact one-step joint identity propagates to the actual full final history
and static hidden operator, for every finite number of adaptive requests.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

@[reducible] def RevealTape (W Z : Type u) : ℕ → Type u
  | 0 => Z
  | N + 1 => W × RevealTape W Z N

variable {S Q W Z : Type u} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace W] [MeasurableSpace Z]

instance revealTapeMeasurableSpace : (N : ℕ) → MeasurableSpace (RevealTape W Z N)
  | 0 => inferInstanceAs (MeasurableSpace Z)
  | N + 1 => letI : MeasurableSpace (RevealTape W Z N) := revealTapeMeasurableSpace N
             inferInstanceAs (MeasurableSpace (W × RevealTape W Z N))

def revealTapeLaw (τ : Measure W) (ν : Measure Z) : (N : ℕ) → Measure (RevealTape W Z N)
  | 0 => ν
  | N + 1 => τ.prod (revealTapeLaw τ ν N)

instance revealTapeLaw_probability (τ : Measure W) (ν : Measure Z)
    [IsProbabilityMeasure τ] [IsProbabilityMeasure ν] (N : ℕ) :
    IsProbabilityMeasure (revealTapeLaw τ ν N) := by
  induction N with
  | zero => exact ‹IsProbabilityMeasure ν›
  | succ N ih =>
      letI := ih
      exact inferInstanceAs (IsProbabilityMeasure (τ.prod (revealTapeLaw τ ν N)))

def simulateCompletion (next : S → W → S) (complete : S → Z → Q) :
    (N : ℕ) → S → RevealTape W Z N → S × Q
  | 0, s, z => (s, complete s z)
  | N + 1, s, p => simulateCompletion next complete N (next s p.1) p.2

def staticEvolve (step : S → Q → S) : ℕ → S → Q → S
  | 0, s, _ => s
  | N + 1, s, q => staticEvolve step N (step s q) q

theorem simulateCompletion_joint_measurable
    {next : S → W → S} {complete : S → Z → Q}
    (hn : Measurable (fun p : S × W ↦ next p.1 p.2))
    (hc : Measurable (fun p : S × Z ↦ complete p.1 p.2)) (N : ℕ) :
    Measurable (fun p : S × RevealTape W Z N ↦ simulateCompletion next complete N p.1 p.2) := by
  induction N with
  | zero => exact measurable_fst.prodMk hc
  | succ N ih =>
      exact ih.comp ((hn.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))

theorem staticEvolve_joint_measurable {step : S → Q → S}
    (hs : Measurable (fun p : S × Q ↦ step p.1 p.2)) (N : ℕ) :
    Measurable (fun p : S × Q ↦ staticEvolve step N p.1 p.2) := by
  induction N with
  | zero => exact measurable_fst
  | succ N ih => exact ih.comp (hs.prodMk measurable_snd)

variable (τ : Measure W) (ν : Measure Z) [IsProbabilityMeasure τ] [IsProbabilityMeasure ν]
  (next : S → W → S) (complete : S → Z → Q) (step : S → Q → S)
  (hn : Measurable (fun p : S × W ↦ next p.1 p.2))
  (hc : Measurable (fun p : S × Z ↦ complete p.1 p.2))
  (hs : Measurable (fun p : S × Q ↦ step p.1 p.2))
  (hlocal : ∀ s, (τ.prod ν).map (simulateCompletion next complete 1 s) =
    ν.map (fun z ↦ (step s (complete s z), complete s z)))

include hn hc hs hlocal

theorem adaptive_completion_lintegral (N : ℕ) (s : S) (F : S × Q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (simulateCompletion next complete N s p) ∂revealTapeLaw τ ν N) =
      ∫⁻ z, F (staticEvolve step N s (complete s z), complete s z) ∂ν := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
      let FN : S × Q → ℝ≥0∞ := fun p ↦ F (staticEvolve step N p.1 p.2, p.2)
      have hFN : Measurable FN := hF.comp ((staticEvolve_joint_measurable hs N).prodMk measurable_snd)
      have hsim1 : Measurable (simulateCompletion next complete 1 s) :=
        (simulateCompletion_joint_measurable hn hc 1).comp (measurable_const.prodMk measurable_id)
      have hcomp : Measurable (complete s) := hc.comp (measurable_const.prodMk measurable_id)
      have hgraph : Measurable (fun z ↦ (step s (complete s z),complete s z)) :=
        (hs.comp (measurable_const.prodMk hcomp)).prodMk hcomp
      have hOne := congrArg (fun ν : Measure (S × Q) ↦ ∫⁻ p, FN p ∂ν) (hlocal s)
      rw [lintegral_map (μ := τ.prod ν) hFN hsim1,
        lintegral_map (μ := ν) hFN hgraph] at hOne
      have hm1 : Measurable (fun p : W × Z ↦ FN (next s p.1, complete (next s p.1) p.2)) := by
        simpa only [simulateCompletion,Function.comp_def] using hFN.comp hsim1
      change (∫⁻ p : W × Z, FN (next s p.1, complete (next s p.1) p.2) ∂τ.prod ν) =
        ∫⁻ z, FN (step s (complete s z),complete s z) ∂ν at hOne
      rw [lintegral_prod _ hm1.aemeasurable] at hOne
      have hsim : Measurable (fun p : W × RevealTape W Z N ↦
          simulateCompletion next complete N (next s p.1) p.2) :=
        (simulateCompletion_joint_measurable hn hc N).comp
          ((hn.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
      calc
        _ = ∫⁻ w, ∫⁻ p, F (simulateCompletion next complete N (next s w) p)
            ∂revealTapeLaw τ ν N ∂τ := lintegral_prod _ (hF.comp hsim).aemeasurable
        _ = ∫⁻ w, ∫⁻ z, F (staticEvolve step N (next s w) (complete (next s w) z),
            complete (next s w) z) ∂ν ∂τ :=
          lintegral_congr_ae (Filter.Eventually.of_forall (fun w ↦ ih (next s w)))
        _ = _ := by simpa only [FN,simulateCompletion,staticEvolve] using hOne

/-- Equality includes the complete public state, hence every recorded
query/reply and arbitrary returned point, together with the final operator. -/
theorem adaptive_completion_joint_law (N : ℕ) (s : S) :
    (revealTapeLaw τ ν N).map (simulateCompletion next complete N s) =
      ν.map (fun z ↦ (staticEvolve step N s (complete s z),complete s z)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hsim : Measurable (simulateCompletion next complete N s) := (simulateCompletion_joint_measurable hn hc N).comp
    (measurable_const.prodMk measurable_id)
  have hcomp : Measurable (complete s) := hc.comp (measurable_const.prodMk measurable_id)
  have hgraph : Measurable (fun z ↦ (staticEvolve step N s (complete s z),complete s z)) :=
    ((staticEvolve_joint_measurable hs N).comp (measurable_const.prodMk hcomp)).prodMk hcomp
  rw [lintegral_map' hF.aemeasurable hsim.aemeasurable,
    lintegral_map' hF.aemeasurable hgraph.aemeasurable]
  exact adaptive_completion_lintegral τ ν next complete step hn hc hs hlocal N s F hF

theorem adaptive_completion_operator_law (N : ℕ) (s : S) :
    (revealTapeLaw τ ν N).map (fun p ↦ (simulateCompletion next complete N s p).2) =
      ν.map (complete s) := by
  have hsim : Measurable (simulateCompletion next complete N s) :=
    (simulateCompletion_joint_measurable hn hc N).comp (measurable_const.prodMk measurable_id)
  have hcomp : Measurable (complete s) := hc.comp (measurable_const.prodMk measurable_id)
  have hgraph : Measurable (fun z ↦ (staticEvolve step N s (complete s z),complete s z)) :=
    ((staticEvolve_joint_measurable hs N).comp (measurable_const.prodMk hcomp)).prodMk hcomp
  have hh := congrArg (fun μ : Measure (S × Q) ↦ μ.map Prod.snd)
    (adaptive_completion_joint_law τ ν next complete step hn hc hs hlocal N s)
  rw [Measure.map_map measurable_snd hsim,Measure.map_map measurable_snd hgraph] at hh
  simpa only [Function.comp_def] using hh

end NCConcave16991.MixedHaar
