import SphereSmoothingSharpMoments

open MeasureTheory Set
open Task006.HaarRebalancing
open scoped BigOperators NNReal
set_option maxHeartbeats 1000000
namespace Task006.Full.SampleInstance
attribute [local irreducible] rebalancedDirectionalMoment goodRebalancedBasis
noncomputable section
variable {d : ℕ} {L : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
  (I : SampleInstance d L P.R Ω μ)

/-- The manuscript's exact non-strict good-basis boundary convention. -/
def sourceGoodRebalancedBasis (hR : 0 ≤ P.R) (ρ δ s : ℝ) (x : Space d)
    (Q : OrthogonalGroup d) : Prop :=
  ∀ i : Fin d, I.rebalancedDirectionalMoment hR ρ δ x (column Q i) ≤ rebalancingThreshold L d s

theorem measurableSet_sourceGoodRebalancedBasis (hR : 0 ≤ P.R) (ρ δ s : ℝ) :
    MeasurableSet {p : Space d × OrthogonalGroup d | I.sourceGoodRebalancedBasis P hR ρ δ s p.1 p.2} := by
  have hh : MeasurableSet (⋂ i : Fin d, {p : Space d × OrthogonalGroup d |
      I.rebalancedDirectionalMoment hR ρ δ p.1 (column p.2 i) ≤ rebalancingThreshold L d s}) := by
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun p : Space d × OrthogonalGroup d => (p.1, column p.2 i)) :=
      measurable_fst.prodMk ((measurable_column i).comp measurable_snd)
    have hphi : Measurable (fun p : Space d × OrthogonalGroup d =>
        I.rebalancedDirectionalMoment hR ρ δ p.1 (column p.2 i)) := by
      convert! (I.rebalancedDirectionalMoment_joint_measurable hR ρ δ).comp hm using 1
    exact measurableSet_le hphi measurable_const
  convert hh using 1
  ext p
  simp only [sourceGoodRebalancedBasis, mem_setOf_eq, mem_iInter]

theorem bad_sourceGoodRebalancedBasis_probability_le (hR : 0 ≤ P.R) (hd : 0 < d) (hL : 0 < L)
    {δ s ρ : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s) (x : Space d) :
    (orthogonalHaarProbability d).real {Q | ¬I.sourceGoodRebalancedBasis P hR ρ δ s x Q} ≤
      (d : ℝ)*Real.exp (-s) := by
  have hsub : {Q | ¬I.sourceGoodRebalancedBasis P hR ρ δ s x Q} ⊆
      {Q | ¬I.goodRebalancedBasis hR ρ δ s x Q} := by
    intro Q hn hp
    unfold goodRebalancedBasis at hp
    exact hn (fun i => (hp i).le)
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans
    (I.badRebalancedBasis_probability_le hR hd hL hδ hs x)

theorem upperFixedBasisDirection_source_good_moments_sharp (hR : 0 ≤ P.R) (hL : 0 < L)
    (hd : 0 < d) (hρ : 0 < P.ρ) (hb : 0 < P.b)
    {s : ℝ} (hs : 1 ≤ s) {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ))
    (Q : OrthogonalGroup d) (hQ : I.sourceGoodRebalancedBasis P hR P.ρ P.δ s x Q) :
    Integrable (upperFixedBasisDirection P (I.rebalancedSample hR) x Q) (upperRoundNoiseLaw d μ) ∧
    Integrable (fun z => ‖upperFixedBasisDirection P (I.rebalancedSample hR) x Q z‖ ^ 2)
      (upperRoundNoiseLaw d μ) ∧
    ‖(∫ z, upperFixedBasisDirection P (I.rebalancedSample hR) x Q z ∂upperRoundNoiseLaw d μ) -
      I.smoothedGradient hL.le hR P.ρ x‖ ≤
      Real.sqrt d * rebalancingThreshold L d s * P.b ^ (-1 / 2 : ℝ) +
        Real.sqrt d * (d * L * P.δ / (2 * P.ρ)) ∧
    (∫ z, ‖upperFixedBasisDirection P (I.rebalancedSample hR) x Q z‖ ^ 2 ∂upperRoundNoiseLaw d μ) ≤
      d * rebalancingThreshold L d s * P.b ^ (1 / 2 : ℝ) := by
  have hρR : P.ρ ≤ P.R := by linarith [P.inner_nonneg, P.delta_pos]
  have hxδ : ‖x‖ + P.δ ≤ P.R := by linarith
  let D := I.upperCoordinateSecant hR P.ρ P.δ x Q
  have hDi := I.upperCoordinateSecant_integrable hR (ρ := P.ρ) P.delta_pos x Q
  have hm (i : Fin d) : (∫ z, |D i z| ^ (3 / 2 : ℝ) ∂upperRoundNoiseLaw d μ) ≤
      rebalancingThreshold L d s := by
    rw [I.upperCoordinateSecant_moment_eq hR P.delta_pos x Q i]
    exact hQ i
  have hc := clippedVector_moments Q hb (rebalancingThreshold_nonneg L d s hL.le (by linarith)) D
    (I.upperCoordinateSecant_measurable hR P.ρ P.δ x Q) (fun i => (hDi i).1) (fun i => (hDi i).2) hm
  have heq := I.upperFixedBasisDirection_eq_clippedVector P hR x Q
  rw [heq]
  have hmean (i : Fin d) : (∫ z, D i z ∂upperRoundNoiseLaw d μ) =
      centralSecant (ballSmooth I.objective P.ρ) x (column Q i) P.δ :=
    I.upperCoordinateSecant_mean_eq hR hL.le P.rho_nonneg hρR P.delta_pos hxδ Q i
  have hbias := orthogonalReconstruct_error hd Q
    (fun i => ∫ z, D i z ∂upperRoundNoiseLaw d μ) (I.smoothedGradient hL.le hR P.ρ x)
    (a := d * L * P.δ / (2 * P.ρ)) (div_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hL.le) P.delta_pos.le) (by positivity)) (by
      intro i
      rw [hmean i, real_inner_comm]
      exact I.centralSecant_smoothedGradient_error_sharp hL.le hR hρ hρR P.delta_pos
        (by omega) hx ((orthonormal_column Q).norm_eq_one i).le)
  refine ⟨hc.1, hc.2.1, ?_, hc.2.2.2⟩
  calc
    _ ≤ ‖(∫ z, clippedVector Q P.b D z ∂upperRoundNoiseLaw d μ) -
          orthogonalReconstruct Q (fun i => ∫ z, D i z ∂upperRoundNoiseLaw d μ)‖ +
        ‖orthogonalReconstruct Q (fun i => ∫ z, D i z ∂upperRoundNoiseLaw d μ) -
          I.smoothedGradient hL.le hR P.ρ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hc.2.2.1 hbias



#print axioms upperFixedBasisDirection_source_good_moments_sharp
end
end Task006.Full.SampleInstance
