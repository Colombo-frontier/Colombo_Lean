import UpperGhostIidBridge
import UpperGhostRiskTransfer
import UpperGhostSampleLaw
import UpperMain
import UpperGhostClosedBasis

/-! Specialization of the finite ghost coupling to the actual public projected
algorithm. The state stores the iterate and the sum of past iterates. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set
open Task006.HaarRebalancing
open scoped BigOperators
set_option maxHeartbeats 1000000

namespace Task006.Full

attribute [local irreducible] SampleInstance.goodRebalancedBasis SampleInstance.rebalancedDirectionalMoment SampleInstance.sourceGoodRebalancedBasis

abbrev UpperGhostState (d : ℕ) := Space d × Space d

noncomputable def upperGhostStep {d : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (p : UpperGhostState d × UpperSampleBlock d Ω) : UpperGhostState d :=
  (ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg
    (p.1.1 - P.η • upperBlockDirection (d := d) (Ω := Ω) P F p.1.1 p.2), p.1.2 + p.1.1)

theorem upperGhostStep_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : UpperProgramParameters) {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (upperGhostStep P F) := by
  have hx : Measurable (fun p : UpperGhostState d × UpperSampleBlock d Ω => p.1.1) := by fun_prop
  have hs : Measurable (fun p : UpperGhostState d × UpperSampleBlock d Ω => p.1.2) := by fun_prop
  have hg := (upperBlockDirection_measurable (d := d) (Ω := Ω) P hF).comp (hx.prodMk measurable_snd)
  exact ((ballProj_lipschitz (E := Space d) P.inner_nonneg).continuous.measurable.comp
    (hx.sub (hg.const_smul P.η))).prodMk (hs.add hx)

theorem upperGhost_iid_current {d T : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (blocks : Fin T → UpperSampleBlock d Ω) (n : ℕ) :
    (iidState (upperGhostStep P F) (0, 0) blocks n).1 = upperBlockIterate P F blocks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iidState, upperBlockIterate]
    split_ifs with hn
    · change ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg ((iidState (upperGhostStep P F) (0, 0) blocks n).1 -
        P.η • upperBlockDirection P F (iidState (upperGhostStep P F) (0, 0) blocks n).1 (blocks ⟨n, hn⟩)) = _
      rw [ih]
    · exact ih

theorem upperGhost_iid_sum {d T : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (blocks : Fin T → UpperSampleBlock d Ω) (n : ℕ) (hn : n ≤ T) :
    (iidState (upperGhostStep P F) (0, 0) blocks n).2 = ∑ t ∈ Finset.range n, upperBlockIterate P F blocks t := by
  induction n with
  | zero => simp [iidState]
  | succ n ih =>
    have hnT : n < T := by omega
    rw [iidState, dif_pos hnT, Finset.sum_range_succ]
    change (iidState (upperGhostStep P F) (0, 0) blocks n).2 +
      (iidState (upperGhostStep P F) (0, 0) blocks n).1 = _
    rw [ih (by omega), upperGhost_iid_current]

namespace SampleInstance
variable {d : ℕ} {L : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
  (I : SampleInstance d L P.R Ω μ)

def upperGhostGood (hR : 0 ≤ P.R) (s : ℝ) (x : UpperGhostState d) : Set (UpperSampleBlock d Ω) :=
  {b | I.sourceGoodRebalancedBasis P hR P.ρ P.δ s x.1 b.1.1}

theorem upperGhostGood_measurable (hR : 0 ≤ P.R) (s : ℝ) :
    MeasurableSet {p : UpperGhostState d × UpperSampleBlock d Ω | p.2 ∈ I.upperGhostGood (d := d) (Ω := Ω) P hR s p.1} := by
  have hm : Measurable (fun p : UpperGhostState d × UpperSampleBlock d Ω => (p.1.1, p.2.1.1)) := by fun_prop
  unfold upperGhostGood
  convert! (I.measurableSet_sourceGoodRebalancedBasis P hR P.ρ P.δ s).preimage hm using 1

theorem upperGhostGood_bad_probability (hR : 0 ≤ P.R) (hL : 0 < L) (hd : 0 < d)
    {s : ℝ} (hs : 1 ≤ s) (x : UpperGhostState d) :
    (upperSampleBlockLaw d μ).real (I.upperGhostGood (d := d) (Ω := Ω) P hR s x)ᶜ ≤ (d : ℝ) * Real.exp (-s) := by
  unfold upperGhostGood
  let G : Set (OrthogonalGroup d) := {Q | I.sourceGoodRebalancedBasis P hR P.ρ P.δ s x.1 Q}
  have hG : MeasurableSet G := (I.measurableSet_sourceGoodRebalancedBasis P hR P.ρ P.δ s).preimage measurable_prodMk_left
  have heq := upperSampleBlock_basis_bad_probability μ G hG
  change (upperSampleBlockLaw d μ).real {b | b.1.1 ∉ G} ≤ _
  rw [measureReal_def, heq]
  exact I.bad_sourceGoodRebalancedBasis_probability_le P hR hd hL P.delta_pos hs x.1

theorem upperGhostGood_pos (hR : 0 ≤ P.R) (hL : 0 < L) (hd : 0 < d)
    {s : ℝ} (hs : 1 ≤ s) (hq : (d : ℝ) * Real.exp (-s) < 1) (x : UpperGhostState d) :
    upperSampleBlockLaw d μ (I.upperGhostGood (d := d) (Ω := Ω) P hR s x) ≠ 0 := by
  apply good_measure_ne_zero_of_bad_lt_one _ _
    ((I.upperGhostGood_measurable P hR s).preimage measurable_prodMk_left)
  exact (I.upperGhostGood_bad_probability P hR hL hd hs x).trans_lt hq

noncomputable def upperGhostLaw (hR : 0 ≤ P.R) (hL : 0 < L) (hd : 0 < d)
    (s : ℝ) (hs : 1 ≤ s) (hq : (d : ℝ) * Real.exp (-s) < 1) (n : ℕ) :
    Measure (GhostState (UpperGhostState d)) :=
  ghostProcessLaw (upperSampleBlockLaw d μ) (I.upperGhostGood (d := d) (Ω := Ω) P hR s)
    (I.upperGhostGood_measurable P hR s) (I.upperGhostGood_pos P hR hL hd hs hq)
    (upperGhostStep P (I.rebalancedSample hR))
    (upperGhostStep_measurable P (I.rebalancedSample_measurable hR)) (0, 0) n

theorem upperGhostLaw_failure (hR : 0 ≤ P.R) (hL : 0 < L) (hd : 0 < d)
    (s : ℝ) (hs : 1 ≤ s) (hq : (d : ℝ) * Real.exp (-s) < 1) (n : ℕ) :
    (I.upperGhostLaw P hR hL hd s hs hq n).real ghostFailed ≤ n * ((d : ℝ) * Real.exp (-s)) := by
  apply ghostProcess_failure_real_le
  · positivity
  · intro x
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
    exact I.upperGhostGood_bad_probability P hR hL hd hs x

end SampleInstance

#print axioms SampleInstance.upperGhostLaw_failure
end Task006.Full
