import HeavyTail.AdaptiveKernelExecution
import HeavyTail.GaussianAdaptiveSampler
import Mathlib.MeasureTheory.Measure.Real

/-! A pre-generated independent noise stream realizes the actual causal kernel
history law. Agreement of response samplers on a noise event implies transcript
agreement by induction, including arbitrary seed randomization. -/

open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel
noncomputable section
universe u

variable {Seed Noise Reply : Type u} {Query Output : Type*}
  [MeasurableSpace Seed] [MeasurableSpace Noise] [MeasurableSpace Reply]
  [MeasurableSpace Query] [MeasurableSpace Output] {T : ℕ}

def noiseHistoryLaw (P : Measure Seed) (ν : Measure Noise) : (n : ℕ) → Measure (History Seed Noise n)
  | 0 => P
  | n + 1 => (noiseHistoryLaw P ν n).prod ν

instance noiseHistoryLaw_probability (P : Measure Seed) (ν : Measure Noise)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (noiseHistoryLaw P ν n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure P)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsProbabilityMeasure ((noiseHistoryLaw P ν n).prod ν))

def Policy.sampleHistory (A : Policy Seed Query Reply Output T) (F : Query × Noise → Reply) :
    (n : ℕ) → History Seed Noise n → History Seed Reply n
  | 0 => id
  | n + 1 => fun ω =>
    (A.sampleHistory F n ω.1, F (A.query n (A.sampleHistory F n ω.1), ω.2))

theorem Policy.sampleHistory_measurable (A : Policy Seed Query Reply Output T)
    {F : Query × Noise → Reply} (hF : Measurable F) (n : ℕ) :
    Measurable (A.sampleHistory F n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
    exact (ih.comp measurable_fst).prodMk (hF.comp
      (((A.query_measurable n).comp (ih.comp measurable_fst)).prodMk measurable_snd))

theorem Policy.sampleHistory_law (A : Policy Seed Query Reply Output T)
    (P : Measure Seed) (ν : Measure Noise) [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {F : Query × Noise → Reply} (hF : Measurable F) (n : ℕ) :
    (noiseHistoryLaw P ν n).map (A.sampleHistory F n) =
      A.historyLaw P (kernelOfSampler ν F hF) n := by
  induction n with
  | zero => exact Measure.map_id
  | succ n ih =>
    rw [Policy.historyLaw_succ]
    unfold Policy.replyKernel
    rw [kernelOfSampler_comap, compProd_kernelOfSampler, ← ih]
    have hp : ((noiseHistoryLaw P ν n).map (A.sampleHistory F n)).prod ν =
        ((noiseHistoryLaw P ν n).prod ν).map
          (fun ω => (A.sampleHistory F n ω.1, ω.2)) := by
      simpa only [Measure.map_id, Prod.map_apply, id_eq] using
        Measure.map_prod_map (noiseHistoryLaw P ν n) ν
          (A.sampleHistory_measurable hF n) measurable_id
    rw [hp, Measure.map_map]
    · rfl
    · exact measurable_fst.prodMk
        (hF.comp (((A.query_measurable n).comp measurable_fst).prodMk measurable_snd))
    · exact ((A.sampleHistory_measurable hF n).comp measurable_fst).prodMk measurable_snd

def goodNoiseHistory (B : Set Noise) : (n : ℕ) → Set (History Seed Noise n)
  | 0 => Set.univ
  | n + 1 => goodNoiseHistory B n ×ˢ B

theorem goodNoiseHistory_measurable {B : Set Noise} (hB : MeasurableSet B) (n : ℕ) :
    MeasurableSet (goodNoiseHistory (Seed := Seed) B n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih => exact ih.prod hB

theorem goodNoiseHistory_probability (P : Measure Seed) (ν : Measure Noise)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (B : Set Noise) (n : ℕ) :
    (noiseHistoryLaw P ν n).real (goodNoiseHistory B n) = (ν.real B) ^ n := by
  induction n with
  | zero => simp only [noiseHistoryLaw, goodNoiseHistory, measureReal_univ_eq_one, pow_zero]
  | succ n ih =>
    change ((noiseHistoryLaw P ν n).prod ν).real (goodNoiseHistory B n ×ˢ B) = _
    rw [measureReal_prod_prod, ih, pow_succ]

theorem Policy.sampleHistory_noninterference (A : Policy Seed Query Reply Output T)
    {F G : Query × Noise → Reply} {B : Set Noise}
    (hFG : ∀ x z, z ∈ B → F (x, z) = G (x, z)) (n : ℕ)
    (ω : History Seed Noise n) (hω : ω ∈ goodNoiseHistory B n) :
    A.sampleHistory F n ω = A.sampleHistory G n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih ω.1 hω.1
    change (A.sampleHistory F n ω.1, F (A.query n (A.sampleHistory F n ω.1), ω.2)) = _
    rw [he, hFG _ _ hω.2]
    rfl

end
end HeavyTail.AdaptiveKernel
