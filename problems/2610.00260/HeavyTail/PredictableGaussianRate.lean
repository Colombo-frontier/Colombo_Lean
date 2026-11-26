import HeavyTail.PredictableGaussianOnline
import HeavyTail.GenericOnlineMasterTuning
import HeavyTail.GaussianStageTuning

/-! The fully tuned conditional online rate for the concrete measurable
Gaussian learner, with arbitrary history-dependent means and noise laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates AdaptiveKernel
universe u v w
variable {Seed E ι : Type u} {Query : Type v} {Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Query] [MeasurableSpace Output]
  [Fintype ι] [Nonempty ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem predictableGaussian_online_rate {n : ℕ} (A : Policy Seed Query E Output n)
    (K : Kernel Query E) [IsMarkovKernel K] (P : Measure Seed) [IsProbabilityMeasure P]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R α : ℝ}
    (H : PredictableNoiseContract A K b p s V M) (hp : 1 < p) (hp2 : p ≤ 2)
    (hM : 0 < M) (hV : 0 ≤ V) (hs : 0 < s) (c : E) (hR : 0 < R)
    (hα : 0 < α) (hα1 : α < 1 / 10) (hn : 0 < n)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R) (i₀ : ι) (h₀ : centers i₀ = c)
    (u : E) (hnear : ∃ i, ‖centers i - u‖ ≤ R / (8 * n)) :
    let ell := confidenceLog α
    let η := onlineStep p M V s R ell n
    let a := onlineSmoothing R ell
    let β := onlineQuadratic η M R n
    let hε := tunedOnlineResidual_pos (p := p) hM hV hs hR (confidenceLog_pos hα hα1) (Nat.cast_pos.mpr hn)
    let initial : SimplexPoint ι := ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
    let weights := onlineHistoryWeights c a η β centers hε initial
    (A.historyLaw P K n).real {h |
      (96 + 16 * mixedConstant p) * R * ((M + Real.sqrt V) / Real.sqrt n +
        M * ell / n + s * (ell / n) ^ (1 - 1 / p)) <
      historySum (predictableGaussianRegret centers weights b u) n h / n} ≤ α := by
  classical
  let ell := confidenceLog α
  let η := onlineStep p M V s R ell n
  let a := onlineSmoothing R ell
  let β := onlineQuadratic η M R n
  let ε := onlineResidual η M R n
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hell : 1 ≤ ell := confidenceLog_ge_one hα hα1
  have hη : 0 < η := onlineStep_pos hM hV hs hR (confidenceLog_pos hα hα1) hnR
  have ha := onlineSmoothing_bounds hR hell
  have hβ := onlineQuadratic_pos hη hM hR hnR
  have hε : 0 < ε := tunedOnlineResidual_pos hM hV hs hR (confidenceLog_pos hα hα1) hnR
  let initial : SimplexPoint ι := ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
  let weights := onlineHistoryWeights (Seed := Seed) c a η β centers hε initial
  obtain ⟨i, hi⟩ := hnear
  let q : SimplexPoint ι := ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩
  let D₀ := gaussianOnlineDivergence E c a β centers q.val initial.val
  let ν := mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))
  let N := D₀ + n * (η ^ 2 * M ^ 2 / (2 * β) + ε) + 2 * (n * ν + Real.log (1 / (α / 2)))
  let rate := (96 + 16 * mixedConstant p) * R * ((M + Real.sqrt V) / Real.sqrt n +
    M * ell / n + s * (ell / n) ^ (1 - 1 / p))
  have hD : D₀ ≤ R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 := by
    have hd := gaussianOnlineDivergence_initial_bound E c a hβ.le hR.le centers i i₀ h₀ (hc i)
    simpa only [div_mul_eq_mul_div] using hd
  have hlog : Real.log (1 / (α / 2)) ≤ 2 * ell := by
    apply le_trans (Real.log_le_log (by positivity)
      (one_div_le_one_div_of_le (show 0 < α / 4 by positivity) (by linarith)))
    exact stage_log_confidence_comparison hα hα1
  have hsmall : N / (η * n) + M * R / (8 * n) ≤ rate :=
    (generic_online_small_master_bound (mixedConstant_pos p).le hM hV hs hR hell hnR hD hlog).trans
      (online_master_bound (mixedConstant_pos p).le hp hM hV hs hR hell (by exact_mod_cast (Nat.succ_le_of_lt hn)))
  have hqdist : ‖finiteMixtureMean centers q.val - u‖ ≤ R / (8 * n) := by
    simpa only [q, finiteMixtureMean_single_component] using hi
  have hcomp (h : History Seed E n) :
      historySum (predictableGaussianRegret centers weights b u) n h / n ≤
        historySum (predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val)) n h / n +
          M * R / (8 * n) := by
    have hstep (t : ℕ) (z : History Seed E t × E) :
        predictableGaussianRegret centers weights b u t z ≤
          predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val) t z +
            M * (R / (8 * n)) := by
      have hcs := (real_inner_le_norm (b t z.1) (finiteMixtureMean centers q.val - u)).trans
        (mul_le_mul (H.mean_bound t z.1) hqdist (norm_nonneg _) hM.le)
      simp only [predictableGaussianRegret, inner_sub_right] at hcs ⊢
      linarith only [hcs]
    have ht := historySum_mono hstep n h
    rw [historySum_add, historySum_const] at ht
    have hd := div_le_div_of_nonneg_right ht hnR.le
    have he : (n : ℝ) * (M * (R / (8 * n))) / n = M * R / (8 * n) := by
      field_simp [hnR.ne']
      <;> ring
    simpa only [add_div, he] using hd
  have hprob := predictableGaussian_regret_tail A K P b H hp hp2 hs c hM.le hη ha.1 ha.2.1
    (onlineStep_admissible hM hR) hβ hε (show 0 < α / 2 by positivity) centers hc initial q n
  have hsub : {h | rate < historySum (predictableGaussianRegret centers weights b u) n h / n} ⊆
      {h | N / η < historySum (predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val)) n h} := by
    intro h hh
    change rate < historySum (predictableGaussianRegret centers weights b u) n h / n at hh
    have hc := hcomp h
    have hlt : N / (η * n) <
        historySum (predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val)) n h / n := by
      linarith only [hsmall, hc, hh]
    rw [div_mul_eq_div_div] at hlt
    exact (div_lt_div_iff_of_pos_right hnR).mp hlt
  have hm := measureReal_mono (μ := A.historyLaw P K n) hsub
  dsimp only
  exact (hm.trans hprob).trans (by linarith)

end HeavyTail.GaussianEntropy
