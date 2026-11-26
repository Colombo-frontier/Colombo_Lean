import HeavyTail.GaussianHistoryMaster
import HeavyTail.GaussianStageGoodEvent

/-! The actual optimization stage's untuned probability bound, combining
the derived mirror inequality, original-oracle concentration, accepted
mean bias, proximal transfer, and the actual feasible average. -/
noncomputable section
open MeasureTheory Set
open scoped Classical

namespace HeavyTail.PrivateInstance
open GaussianEntropy
universe u
variable {E ι : Type u} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters} {B : PublicProblem E θ}

theorem gaussianStage_scaled_error (I : PrivateInstance B)
    {c : E} {R τ a η β ε δ ρ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : a ≠ 0)
    (hη : 0 ≤ η) (hβ : 0 < β) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (hfirst : ∀ (w : SimplexPoint ι) (Y : E) (q : SimplexPoint ι),
      -ε ≤ (observedClippedLoss E c a η centers (Y, w.val) +
        gaussianOnlineDerivative E c a β centers (L.update (w, Y)).val -
        gaussianOnlineDerivative E c a β centers w.val) (q.val - (L.update (w, Y)).val))
    (q : SimplexPoint ι) (hq : ‖finiteMixtureMean centers q.val - I.minimizer‖ ≤ ρ)
    (T : ℕ) (h : AdaptiveKernel.History PUnit E T)
    (hg : h ∈ I.gaussianStageGoodEvent hR hn τ a η δ centers L q T) :
    (η * n) * I.objectiveGap ((B.cappedStagePolicy hR hn τ L T).output h) ≤
      gaussianOnlineDivergence E c a β centers q.val L.initial.val +
        n * (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
        2 * (T * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ)) +
        η * T * (acceptedMeanScale θ τ * ρ + 2 * R * acceptedBiasScale θ τ + θ.G * R / (2 * n)) := by
  have ht := I.stage_online_to_batch hR hn hτ L hcenter T h hg.1
  have hq' := I.gaussianHistory_comparator_transfer hR hn hτ centers hc hcenter hρ L hpoint q hq T h
  have hr := I.gaussianHistory_regret_bound hR hn hτ centers hc hcenter ha hη hβ hε
    L hpoint hfirst q T h
  have htη := mul_le_mul_of_nonneg_left ht hη
  have hqη := mul_le_mul_of_nonneg_left hq' hη
  have hw := hg.2.1
  have hQ := hg.2.2
  dsimp only [acceptedBiasScale]
  nlinarith only [htη, hqη, hr, hw, hQ]

theorem gaussianStage_error_probability (I : PrivateInstance B)
    {c : E} {R τ a η β ε δ ρ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 < η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (hβ : 0 < β) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (hfirst : ∀ (w : SimplexPoint ι) (Y : E) (q : SimplexPoint ι),
      -ε ≤ (observedClippedLoss E c a η centers (Y, w.val) +
        gaussianOnlineDerivative E c a β centers (L.update (w, Y)).val -
        gaussianOnlineDerivative E c a β centers w.val) (q.val - (L.update (w, Y)).val))
    (q : SimplexPoint ι) (hq : ‖finiteMixtureMean centers q.val - I.minimizer‖ ≤ ρ)
    (P : Measure PUnit) [IsProbabilityMeasure P] (hδ : 0 < δ) :
    ((B.cappedStagePolicy hR hn τ L (4 * n)).historyLaw P I.oracle (4 * n)).real
      {h | (gaussianOnlineDivergence E c a β centers q.val L.initial.val +
        n * (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
        2 * ((4 * n : ℕ) * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ)) +
        η * (4 * n : ℕ) * (acceptedMeanScale θ τ * ρ + 2 * R * acceptedBiasScale θ τ + θ.G * R / (2 * n))) /
          (η * n) < I.objectiveGap ((B.cappedStagePolicy hR hn τ L (4 * n)).output h)} ≤
        ((2 : ℝ) ^ (8 * n))⁻¹ + 2 * δ := by
  apply le_trans (measureReal_mono (s₂ := (I.gaussianStageGoodEvent hR hn τ a η δ centers L q (4 * n))ᶜ) ?_)
    (I.gaussianStageGoodEvent_compl_probability hR hn hτ centers hc hcenter ha haR hη.le htune L hpoint q P hδ)
  intro h hh hg
  have hs := I.gaussianStage_scaled_error hR hn hτ centers hc hcenter ha.ne' hη.le hβ hε hρ
    L hpoint hfirst q hq (4 * n) h hg
  have hp : 0 < η * (n : ℝ) := mul_pos hη (Nat.cast_pos.mpr hn)
  have hlt := (div_lt_iff₀ hp).mp hh
  linarith only [hs, hlt]

theorem stage_output_loss_tail_le_objective_tail {W : Type u} [MeasurableSpace W]
    (I : PrivateInstance B) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R) (T : ℕ)
    (P : Measure PUnit) [IsProbabilityMeasure P] (r : ℝ) :
    ((B.cappedStagePolicy hR hn τ L T).outputLaw P I.oracle).real
      {x | ENNReal.ofReal r < I.loss x} ≤
    ((B.cappedStagePolicy hR hn τ L T).historyLaw P I.oracle T).real
      {h | r < I.objectiveGap ((B.cappedStagePolicy hR hn τ L T).output h)} := by
  have he := (B.cappedStagePolicy hR hn τ L T).outputLaw_apply P I.oracle
    (B := {x : B.X | ENNReal.ofReal r < I.loss x})
    (measurableSet_lt (measurable_const (a := ENNReal.ofReal r)) I.loss_measurable)
  change (((B.cappedStagePolicy hR hn τ L T).outputLaw P I.oracle) _).toReal ≤ _
  rw [he]
  apply measureReal_mono
  · intro h hh
    change ENNReal.ofReal r < I.loss ((B.cappedStagePolicy hR hn τ L T).output h) at hh
    rw [I.loss_of_mem _ (B.stage_readout_domain hR hn τ L T h)] at hh
    exact lt_of_not_ge fun hr => not_lt_of_ge (ENNReal.ofReal_le_ofReal hr) hh
  · finiteness

end HeavyTail.PrivateInstance
