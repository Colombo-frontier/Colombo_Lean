import Bilevel.ChiSelectedFramePrior
import Bilevel.ChiHierarchyExecution

/-! Activation of the actual finite-prefix source execution on the same
Haar/private-seed/iid-coin prior. The observer's stronger frame context is
not used as an adaptedness assumption for the coin process. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian

variable {Private S Q O Y : Type*} [MeasurableSpace Private] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

omit [MeasurableSpace Private] in
theorem actual_counter_le_coins {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (initial : Private → S) (N : ℕ) (p : Sample (Orientations counts J D) Private Bool) :
    ((run counts J A evaluate (columns hD p.1) (initial p.2.1) p.2.2 N).2.1:ℝ)≤
      MultiscaleActivation.count N (IndependentStream.project N p.2.2) := by
  rw [run_success_count]
  exact successes_le_count (instrument counts J A) (response counts J evaluate) (initialState counts J)
    N (columns hD p.1,(initial p.2.1,p.2.2))

theorem actual_counter_measurable {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (initial : Private → S) (hi : Measurable initial) (N : ℕ) :
    Measurable (fun p : Sample (Orientations counts J D) Private Bool =>
      (run counts J A evaluate (columns hD p.1) (initial p.2.1) p.2.2 N).2.1) := by
  have hp : Measurable (fun p : Sample (Orientations counts J D) Private Bool =>
      (columns hD p.1,(initialState (E:=Space D) counts J (initial p.2.1),p.2.2))) :=
    ((columns_measurable hD).comp measurable_fst).prodMk
      (((initialize_measurable (E:=Space D) counts J).comp (hi.comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))
  have hr := (BorelAdaptive.run_measurable (instrument counts J A) (response counts J evaluate)
    (response_measurable counts J evaluate he) N).comp hp
  exact measurable_fst.comp (measurable_snd.comp hr)

theorem actual_activation_sixteenth {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (initial : Private → S) (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (N T : ℕ) (hT : 0<T)
    (hN : (N:ℝ)≤(T:ℝ)/(16*p)) :
    ((law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real
      {z | T≤(run counts J A evaluate (columns hD z.1) (initial z.2.1) z.2.2 N).2.1}≤1/16 := by
  let μ := (law counts J D).prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))
  have hm : MeasurableSet {z : IndependentDraws.Draws Bool N | (T:ℝ)≤MultiscaleActivation.count N z} :=
    measurableSet_le measurable_const (MultiscaleActivation.count_measurable N)
  have hmap := (draws_preserving (law counts J D) ρ p hp1 N).measure_preimage hm.nullMeasurableSet
  have hsub : {z : Sample (Orientations counts J D) Private Bool |
      T≤(run counts J A evaluate (columns hD z.1) (initial z.2.1) z.2.2 N).2.1} ⊆
      {z | (T:ℝ)≤MultiscaleActivation.count N (IndependentStream.project N z.2.2)} := by
    intro z hz
    exact (Nat.cast_le.mpr hz).trans (actual_counter_le_coins hD A evaluate initial N z)
  apply (measureReal_mono hsub).trans
  change μ.real ((fun z : Sample (Orientations counts J D) Private Bool => IndependentStream.project N z.2.2) ⁻¹'
    {z | (T:ℝ)≤MultiscaleActivation.count N z})≤_
  rw [measureReal_def,hmap]
  exact MultiscaleActivation.revelation_sixteenth N T hT p hp hp1 hN

theorem macro_incomplete_of_successes_lt (counts : ℕ → ℕ) (J q : ℕ)
    (hq : q<ChiTreeProgress.capacity counts (J+1) 0) :
    retained counts J q (Sum.inl ())≤counts 0 := by
  have hcap := ChiTreeProgress.capacity_pos counts J 1
  have hq' : q<(counts 0+1)*ChiTreeProgress.capacity counts J 1 := hq
  have hdiv : q/ChiTreeProgress.capacity counts J 1<counts 0+1 :=
    (Nat.div_lt_iff_lt_mul hcap).mpr hq'
  change ChiTreeProgress.counter counts (J+1) q 0 []≤counts 0
  simp only [ChiTreeProgress.counter,List.length_nil,if_true,Nat.sub_zero,
    ChiTreeProgress.nodeBudget,ChiTreeProgress.nodePrefix]
  exact (Nat.min_le_right _ _).trans (Nat.le_of_lt_succ hdiv)

end Bilevel.ChiHierarchyHaar
