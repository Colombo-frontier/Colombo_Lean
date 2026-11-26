import Bilevel.ChiSourceGoodEvent

/-! One public ambient dimension and one Haar prior work for every capped
horizon below a fixed maximum. This is required by the expected-cost
argument, rather than choosing a new hard-instance prior for each cap. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian

variable {C : Type*} {S : Type u} {Q O Y : Type*} [MeasurableSpace C] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
variable (counts : ℕ → ℕ) (J D m : ℕ)
  (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
  (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
  (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
    evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ l, Measurable (queries l))
  (output : FrameIndex counts J → Y → Space D) (ho : ∀ i,Measurable (output i))
  (initial : C → S) (draws : C → ℕ → Bool)

theorem sourceGood_failure_uniform (ρ : Measure C) [IsProbabilityMeasure ρ]
    (hi : Measurable initial) (hd : Measurable draws) (N n r : ℕ) (hn : n≤N) (b cap : ℝ)
    (hb : 0<b) (hb2 : b≤2)
    (hdim : (2*(N*batchSize counts J m)+1)+(N*batchSize counts J m)+(r+1)≤D)
    (hcap : ((N*batchSize counts J m:ℕ):ℝ)*(((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b)≤1/2)
    (henergy : 2*((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b≤cap) :
    (ρ.prod (law counts J D)) {p | ¬sourceGood counts J D m hD A evaluate he queries hq output ho initial draws n cap p} ≤
      ((2*(N*batchSize counts J m)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (totalColumns counts J) r b := by
  have hR : n*batchSize counts J m≤N*batchSize counts J m := Nat.mul_le_mul_right _ hn
  have hM : 2*(n*batchSize counts J m)+1≤2*(N*batchSize counts J m)+1 := by omega
  have hRr : ((n*batchSize counts J m:ℕ):ℝ)≤((N*batchSize counts J m:ℕ):ℝ) := Nat.cast_le.mpr hR
  have hMr : ((2*(n*batchSize counts J m)+1:ℕ):ℝ)≤((2*(N*batchSize counts J m)+1:ℕ):ℝ) := Nat.cast_le.mpr hM
  have hc : ((n*batchSize counts J m:ℕ):ℝ)*(((2*(n*batchSize counts J m)+1:ℕ):ℝ)*b)≤1/2 := by
    apply (mul_le_mul hRr (mul_le_mul_of_nonneg_right hMr hb.le)
      (by positivity) (Nat.cast_nonneg _)).trans hcap
  have he' : 2*((2*(n*batchSize counts J m)+1:ℕ):ℝ)*b≤cap := by
    apply le_trans _ henergy
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMr (by norm_num)) hb.le
  have hp := sourceGood_failure counts J D m hD A evaluate he queries hq output ho initial draws
    ρ hi hd n r b cap hb hb2 (by omega) hc he'
  exact hp.trans (mul_le_mul_right' (Nat.cast_le.mpr hM) _)

theorem sourceGood_swap_measure (ρ : Measure C) [IsProbabilityMeasure ρ]
    (hi : Measurable initial) (hd : Measurable draws) (N : ℕ) (cap : ℝ) :
    ((law counts J D).prod ρ) {p | ¬sourceGood counts J D m hD A evaluate he queries hq output ho initial draws N cap (p.2,p.1)} =
      (ρ.prod (law counts J D)) {p | ¬sourceGood counts J D m hD A evaluate he queries hq output ho initial draws N cap p} := by
  have hm := (sourceGood_measurable counts J D m hD A evaluate he queries hq output ho initial draws hi hd N cap).compl
  exact (Measure.measurePreserving_swap (μ:=law counts J D) (ν:=ρ)).measure_preimage hm.nullMeasurableSet

theorem sourceGood_swapped_measurable (hi : Measurable initial) (hd : Measurable draws) (N : ℕ) (cap : ℝ) :
    MeasurableSet {p : Orientations counts J D × C |
      sourceGood counts J D m hD A evaluate he queries hq output ho initial draws N cap (p.2,p.1)} :=
  (sourceGood_measurable counts J D m hD A evaluate he queries hq output ho initial draws hi hd N cap).preimage
    measurable_swap

end Bilevel.ChiHierarchyHaar
