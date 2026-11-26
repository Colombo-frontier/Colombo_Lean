import Bilevel.ChiSourceUniformHorizon
import Bilevel.ChiSourceActivation

/-! The same finite Haar prior, private seed, and independent Bernoulli
stream support both observer and activation events at every capped horizon.
No independence between the algorithm's transcript and its frames is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian

variable {Private S Q O Y : Type*} [MeasurableSpace Private] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
variable (counts : ℕ → ℕ) (J D m : ℕ)
  (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
  (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
  (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
    evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ l,Measurable (queries l))
  (output : FrameIndex counts J → Y → Space D) (ho : ∀ i,Measurable (output i))
  (initial : Private → S)

def seedGood (N : ℕ) (cap : ℝ) (p : Sample (Orientations counts J D) Private Bool) : Prop :=
  sourceGood counts J D m hD A evaluate he queries hq output ho
    (fun c : Private × (ℕ → Bool) => initial c.1) Prod.snd N cap (p.2,p.1)

theorem seedGood_measurable (hi : Measurable initial) (N : ℕ) (cap : ℝ) :
    MeasurableSet {p | seedGood counts J D m hD A evaluate he queries hq output ho initial N cap p} :=
  sourceGood_swapped_measurable counts J D m hD A evaluate he queries hq output ho
    (fun c : Private × (ℕ → Bool) => initial c.1) Prod.snd (hi.comp measurable_fst) measurable_snd N cap

theorem seedGood_failure_eighth (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (hi : Measurable initial) (p : ℝ) (hp1 : p≤1) (N n r : ℕ) (hn : n≤N) (b cap : ℝ)
    (hb : 0<b) (hb2 : b≤2)
    (hdim : (2*(N*batchSize counts J m)+1)+(N*batchSize counts J m)+(r+1)≤D)
    (hcap : ((N*batchSize counts J m:ℕ):ℝ)*(((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b)≤1/2)
    (henergy : 2*((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b≤cap)
    (hbudget : ((2*(N*batchSize counts J m)+1:ℕ):ℝ≥0∞)*
      GenieProtocol.failurePerQuery (totalColumns counts J) r b≤1/8) :
    ((law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real
      {z | ¬seedGood counts J D m hD A evaluate he queries hq output ho initial n cap z}≤1/8 := by
  let σ := ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))
  have hs := sourceGood_swap_measure counts J D m hD A evaluate he queries hq output ho
    (fun c : Private × (ℕ → Bool) => initial c.1) Prod.snd σ
    (hi.comp measurable_fst) measurable_snd n cap
  have hb' := sourceGood_failure_uniform counts J D m hD A evaluate he queries hq output ho
    (fun c : Private × (ℕ → Bool) => initial c.1) Prod.snd σ
    (hi.comp measurable_fst) measurable_snd N n r hn b cap hb hb2 hdim hcap henergy
  have he' : ((law counts J D).prod σ)
      {z | ¬seedGood counts J D m hD A evaluate he queries hq output ho initial n cap z}≤1/8 := by
    change ((law counts J D).prod σ) {z | ¬sourceGood counts J D m hD A evaluate he queries hq output ho
      (fun c : Private × (ℕ → Bool) => initial c.1) Prod.snd n cap (z.2,z.1)}≤1/8
    rw [hs]
    exact hb'.trans hbudget
  have ht := ENNReal.toReal_mono (by norm_num : (1/8:ℝ≥0∞)≠⊤) he'
  simpa only [measureReal_def,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using ht

def seedActivation (N T : ℕ) (z : Sample (Orientations counts J D) Private Bool) : Prop :=
  T≤(run counts J A evaluate (columns hD z.1) (initial z.2.1) z.2.2 N).2.1

include he in
theorem seedActivation_measurable (hi : Measurable initial) (N T : ℕ) :
    MeasurableSet {z | seedActivation counts J D hD A evaluate initial N T z} :=
  measurableSet_le measurable_const (actual_counter_measurable hD A evaluate he initial hi N)

theorem seedActivation_failure (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (N T : ℕ) (hT : 0<T) (hN : (N:ℝ)≤(T:ℝ)/(16*p)) :
    ((law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real
      {z | seedActivation counts J D hD A evaluate initial N T z}≤1/16 :=
  actual_activation_sixteenth hD A evaluate initial ρ p hp hp1 N T hT hN

end Bilevel.ChiHierarchyHaar
