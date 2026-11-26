import HeavyTail.GaussianStageBound
import HeavyTail.GaussianTranslatedLearner

/-! A concrete translated Gaussian stage: the update is the measurable
first-order selector, initialization is the central Gaussian, and the
comparator is a fixed component of the public finite net. -/
noncomputable section
open MeasureTheory Set
open scoped Classical

namespace HeavyTail

def gaussianStageErrorBound (θ : OracleParameters) (R τ a η β ε δ ρ : ℝ) (n : ℕ) : ℝ :=
  (R ^ 2 / (2 * a ^ 2) + β / 2 * R ^ 2 +
    n * (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
    2 * (4 * n * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ)) +
    η * (4 * n) * (acceptedMeanScale θ τ * ρ + 2 * R * acceptedBiasScale θ τ + θ.G * R / (2 * n))) /
      (η * n)

namespace PrivateInstance
open GaussianEntropy
universe u
variable {E ι : Type u} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters} {B : PublicProblem E θ}

theorem translatedGaussianStage_error_confidence (I : PrivateInstance B)
    {c : E} {R τ a η β ε α ρ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (offsets : ι → E) (hball : ∀ i, ‖offsets i‖ ≤ R)
    (i₀ : ι) (hzero : offsets i₀ = 0)
    (hcover : ∀ u : E, ‖u‖ ≤ R → ∃ i, ‖offsets i - u‖ ≤ ρ)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 < η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (hβ : 0 < β) (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (P : Measure PUnit) [IsProbabilityMeasure P] (hα : 0 < α)
    (hnlog : Real.log (3 / α) ≤ (n : ℝ)) :
    let initial : SimplexPoint ι := ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
    let L := translatedGaussianStageLearner c a η β offsets hball initial hε
    ((B.cappedStagePolicy hR hn τ L (4 * n)).historyLaw P I.oracle (4 * n)).real
      {h | gaussianStageErrorBound θ R τ a η β ε (α / 4) ρ n <
        I.objectiveGap ((B.cappedStagePolicy hR hn τ L (4 * n)).output h)} ≤ α := by
  classical
  dsimp only
  let initial : SimplexPoint ι := ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
  let L := translatedGaussianStageLearner c a η β offsets hball initial hε
  let centers : ι → E := fun i => c + offsets i
  have hc : ∀ i, ‖centers i - c‖ ≤ R := by
    intro i
    simpa only [centers, add_sub_cancel_left] using hball i
  have hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val := by
    intro w
    exact (finiteMixtureMean_translate c offsets w.property).symm
  have hfirst : ∀ (w : SimplexPoint ι) (Y : E) (q : SimplexPoint ι),
      -ε ≤ (observedClippedLoss E c a η centers (Y, w.val) +
        gaussianOnlineDerivative E c a β centers (L.update (w, Y)).val -
        gaussianOnlineDerivative E c a β centers w.val) (q.val - (L.update (w, Y)).val) := by
    intro w Y q
    exact translatedGaussianUpdate_first_order c a η β offsets hε Y w q.property
  have hu : ‖I.minimizer - c‖ ≤ R := by simpa only [norm_sub_rev] using hcenter
  obtain ⟨i, hi⟩ := hcover (I.minimizer - c) hu
  let q : SimplexPoint ι := ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩
  have hq : ‖finiteMixtureMean centers q.val - I.minimizer‖ ≤ ρ := by
    change ‖finiteMixtureMean centers (Pi.single i 1) - I.minimizer‖ ≤ ρ
    rw [finiteMixtureMean_single_component]
    have he : centers i - I.minimizer = offsets i - (I.minimizer - c) := by dsimp [centers]; abel
    simpa only [he] using hi
  have h₀ : centers i₀ = c := by simp only [centers, hzero, add_zero]
  have hD : gaussianOnlineDivergence E c a β centers q.val L.initial.val ≤
      R ^ 2 / (2 * a ^ 2) + β / 2 * R ^ 2 :=
    gaussianOnlineDivergence_initial_bound E c a hβ.le hR.le centers i i₀ h₀ (hc i)
  have hbase := I.gaussianStage_error_probability hR hn hτ centers hc hcenter ha haR
    hη htune hβ hε.le hρ L hpoint hfirst q hq P (show 0 < α / 4 by positivity)
  have hsmall : (gaussianOnlineDivergence E c a β centers q.val L.initial.val +
      n * (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
      2 * ((4 * n : ℕ) * acceptedOnlineExponent θ τ R a η + Real.log (1 / (α / 4))) +
      η * (4 * n : ℕ) * (acceptedMeanScale θ τ * ρ + 2 * R * acceptedBiasScale θ τ + θ.G * R / (2 * n))) /
        (η * n) ≤ gaussianStageErrorBound θ R τ a η β ε (α / 4) ρ n := by
    unfold gaussianStageErrorBound
    apply div_le_div_of_nonneg_right _ (mul_nonneg hη.le (Nat.cast_nonneg n))
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hD]
  have hm := measureReal_mono (μ := (B.cappedStagePolicy hR hn τ L (4 * n)).historyLaw P I.oracle (4 * n))
    (show {h | gaussianStageErrorBound θ R τ a η β ε (α / 4) ρ n <
        I.objectiveGap ((B.cappedStagePolicy hR hn τ L (4 * n)).output h)} ⊆ _ from
      fun _ hh => lt_of_le_of_lt hsmall hh)
  have hcap := rawBudgetTail_le_confidence hα n hnlog
  exact (hm.trans hbase).trans (by linarith only [hcap])

theorem translatedGaussianStage_loss_confidence (I : PrivateInstance B)
    {c : E} {R τ a η β ε α ρ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (offsets : ι → E) (hball : ∀ i, ‖offsets i‖ ≤ R)
    (i₀ : ι) (hzero : offsets i₀ = 0)
    (hcover : ∀ u : E, ‖u‖ ≤ R → ∃ i, ‖offsets i - u‖ ≤ ρ)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 < η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (hβ : 0 < β) (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (P : Measure PUnit) [IsProbabilityMeasure P] (hα : 0 < α)
    (hnlog : Real.log (3 / α) ≤ (n : ℝ)) :
    let initial : SimplexPoint ι := ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
    let L := translatedGaussianStageLearner c a η β offsets hball initial hε
    ((B.cappedStagePolicy hR hn τ L (4 * n)).outputLaw P I.oracle).real
      {x | ENNReal.ofReal (gaussianStageErrorBound θ R τ a η β ε (α / 4) ρ n) < I.loss x} ≤ α := by
  dsimp only
  exact (I.stage_output_loss_tail_le_objective_tail hR hn τ _ (4 * n) P _).trans
    (I.translatedGaussianStage_error_confidence hR hn hτ offsets hball i₀ hzero hcover
      hcenter ha haR hη htune hβ hε hρ P hα hnlog)

end PrivateInstance
end HeavyTail
