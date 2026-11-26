import HeavyTail.PredictableGaussianRate
import HeavyTail.ChangingHistoryKernel

/-! The conditional online theorem stated directly for arbitrary changing
history kernels. The seed can contain any fixed starting history, and its
law can in particular be a Dirac measure at that history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates AdaptiveKernel
universe u
variable {Seed E ι : Type u} [MeasurableSpace Seed]
  [Fintype ι] [Nonempty ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def tunedGaussianWeights (c : E) {p M V s R α : ℝ} {n : ℕ}
    (hM : 0 < M) (hV : 0 ≤ V) (hs : 0 < s) (hR : 0 < R)
    (hα : 0 < α) (hα1 : α < 1 / 10) (hn : 0 < n)
    (centers : ι → E) (i₀ : ι) : (t : ℕ) → History Seed E t → SimplexPoint ι :=
  let ell := confidenceLog α
  let η := onlineStep p M V s R ell n
  let a := onlineSmoothing R ell
  let β := onlineQuadratic η M R n
  let hε := tunedOnlineResidual_pos (p := p) hM hV hs hR (confidenceLog_pos hα hα1) (Nat.cast_pos.mpr hn)
  onlineHistoryWeights c a η β centers hε ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩

theorem changingKernel_online_rate {n : ℕ}
    (κ : (t : ℕ) → Kernel (History Seed E t) E) [∀ t, IsMarkovKernel (κ t)]
    (P : Measure Seed) [IsProbabilityMeasure P]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R α : ℝ}
    (hbm : ∀ t, Measurable (b t)) (hbb : ∀ t h, ‖b t h‖ ≤ M)
    (h2 : ∀ t h, Integrable (fun r => ‖r - b t h‖ ^ 2) (κ t h))
    (hzero : ∀ t h, (∫ r, r - b t h ∂κ t h) = 0)
    (hsecond : ∀ t h, (∫ r, ‖r - b t h‖ ^ 2 ∂κ t h) ≤ V)
    (hweak : ∀ t h v, ‖v‖ = 1 → (∫ r, |⟪v, r - b t h⟫_ℝ| ^ p ∂κ t h) ≤ s ^ p)
    (hp : 1 < p) (hp2 : p ≤ 2) (hM : 0 < M) (hV : 0 ≤ V) (hs : 0 < s)
    (c : E) (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1 / 10) (hn : 0 < n)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R) (i₀ : ι) (h₀ : centers i₀ = c)
    (u : E) (hnear : ∃ i, ‖centers i - u‖ ≤ R / (8 * n)) :
    (changingHistoryLaw P κ n).real {h |
      (96 + 16 * mixedConstant p) * R * ((M + Real.sqrt V) / Real.sqrt n +
        M * confidenceLog α / n + s * (confidenceLog α / n) ^ (1 - 1 / p)) <
      historySum (predictableGaussianRegret centers
        (tunedGaussianWeights c (p := p) hM hV hs hR hα hα1 hn centers i₀) b u) n h / n} ≤ α := by
  let H : PredictableNoiseContract (fullHistoryPolicy n) (changingResponseKernel κ) b p s V M :=
    ⟨hbm, hbb, h2, hzero, hsecond, hweak⟩
  have h := predictableGaussian_online_rate (fullHistoryPolicy n) (changingResponseKernel κ)
    P b H hp hp2 hM hV hs c hR hα hα1 hn centers hc i₀ h₀ u hnear
  simpa only [fullHistoryPolicy_historyLaw, tunedGaussianWeights] using h

end HeavyTail.GaussianEntropy
