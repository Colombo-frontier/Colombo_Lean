import HeavyTail.PredictableGaussianFactors

/-! Pathwise regret and actual-history concentration for the generic online
problem, allowing arbitrary predictable means and conditional noise laws. -/
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

def predictableGaussianRegret (centers : ι → E)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (b : (t : ℕ) → History Seed E t → E) (u : E)
    (t : ℕ) (h : History Seed E t × E) : ℝ :=
  ⟪b t h.1, finiteMixtureMean centers (weights t h.1).val - u⟫_ℝ

theorem gaussianHistory_pathwise_master (c : E) {a η β M ε : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β) (hM : 0 ≤ M) (hε : 0 < ε)
    (centers : ι → E) (initial : SimplexPoint ι)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (b : (t : ℕ) → History Seed E t → E)
    (hinit : ∀ h, weights 0 h = initial)
    (hrec : ∀ t h, weights (t + 1) h = gaussianOnlineUpdate E c a η β centers hε (weights t h.1, h.2))
    (hb : ∀ t h, ‖b t h‖ ≤ M) (q : SimplexPoint ι) (T : ℕ) (h : History Seed E T) :
    gaussianOnlineDivergence E c a β centers q.val (weights T h).val +
      η * historySum (predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val)) T h ≤
    gaussianOnlineDivergence E c a β centers q.val initial.val +
      T * (η ^ 2 * M ^ 2 / (2 * β) + ε) +
      historySum (fun t h => Real.log (predictableGaussianW c a η centers weights b t h)) T h +
      historySum (fun t h => Real.log (predictableGaussianComparator c a η centers weights b q t h)) T h := by
  induction T with
  | zero => simp only [historySum, hinit, Nat.cast_zero, zero_mul, mul_zero, add_zero, le_refl]
  | succ T ih =>
      have hs := gaussianOnlineUpdate_step E c ha hη hβ hM centers hε (weights T h.1)
        q.property h.2 (b T h.1) (hb T h.1)
      have hp := ih h.1
      rw [hrec T h]
      simp only [historySum, predictableGaussianRegret, predictableGaussianW,
        predictableGaussianComparator, Real.log_exp, Nat.cast_add, Nat.cast_one]
      simp only [predictableGaussianRegret, predictableGaussianW,
        predictableGaussianComparator, Real.log_exp] at hp
      nlinarith only [hs, hp]

theorem gaussianHistory_canonical_master (c : E) {a η β M ε : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β) (hM : 0 ≤ M) (hε : 0 < ε)
    (centers : ι → E) (initial : SimplexPoint ι)
    (b : (t : ℕ) → History Seed E t → E) (hb : ∀ t h, ‖b t h‖ ≤ M)
    (q : SimplexPoint ι) (T : ℕ) (h : History Seed E T) :
    let weights := onlineHistoryWeights c a η β centers hε initial
    η * historySum (predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val)) T h ≤
    gaussianOnlineDivergence E c a β centers q.val initial.val +
      T * (η ^ 2 * M ^ 2 / (2 * β) + ε) +
      historySum (fun t h => Real.log (predictableGaussianW c a η centers weights b t h)) T h +
      historySum (fun t h => Real.log (predictableGaussianComparator c a η centers weights b q t h)) T h := by
  let weights := onlineHistoryWeights (Seed := Seed) c a η β centers hε initial
  have hm := gaussianHistory_pathwise_master c ha hη hβ hM hε centers initial weights b
    (fun _ => rfl) (fun _ _ => rfl) hb q T h
  have hD := gaussianOnlineDivergence_nonneg E c a hβ.le centers q.property (weights T h).property
  dsimp only
  linarith only [hm, hD]

theorem predictableGaussianW_tail {T : ℕ} (A : Policy Seed Query E Output T)
    (K : Kernel Query E) [IsMarkovKernel K] (P : Measure Seed) [IsProbabilityMeasure P]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R η a δ : ℝ}
    (H : PredictableNoiseContract A K b p s V M) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (c : E) (hM : 0 ≤ M) (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R)
    (htune : η * M * R ≤ 1 / 16) (hδ : 0 < δ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (hw : ∀ t, Measurable (weights t)) (n : ℕ) :
    (A.historyLaw P K n).real {h |
      n * (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) + Real.log (1 / δ) <
      historySum (fun t h => Real.log (predictableGaussianW c a η centers weights b t h)) n h} ≤ δ := by
  apply history_log_sum_tail A P K
    (B := Real.exp (1 + 2 * η * M * R + η ^ 2 * a ^ 2 * M ^ 2 / 2))
    (Real.exp_pos _).le hδ (predictableGaussianW_measurable c a η centers weights b hw H.mean_measurable)
  · intro t h
    exact onlineMixtureW_pos E c a η centers (weights t h.1).property _ _ _
  · intro t h
    exact onlineMixtureW_ball_bound E c (b t h.1) ha.ne' hη hM (H.mean_bound t h.1)
      centers hc (weights t h.1).property h.2
  · exact predictableGaussianW_moment A K b H hp hp2 hs c hη ha haR htune centers hc weights

theorem predictableGaussianComparator_tail {T : ℕ} (A : Policy Seed Query E Output T)
    (K : Kernel Query E) [IsMarkovKernel K] (P : Measure Seed) [IsProbabilityMeasure P]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R η a δ : ℝ}
    (H : PredictableNoiseContract A K b p s V M) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (c : E) (hM : 0 ≤ M) (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R)
    (htune : η * M * R ≤ 1 / 16) (hδ : 0 < δ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (hw : ∀ t, Measurable (weights t)) (q : SimplexPoint ι) (n : ℕ) :
    (A.historyLaw P K n).real {h |
      n * (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) + Real.log (1 / δ) <
      historySum (fun t h => Real.log (predictableGaussianComparator c a η centers weights b q t h)) n h} ≤ δ := by
  apply history_log_sum_tail A P K (B := Real.exp (1 + 2 * η * M * R))
    (Real.exp_pos _).le hδ (predictableGaussianComparator_measurable c ha.ne' η centers weights b q hw H.mean_measurable)
  · intro t h
    exact Real.exp_pos _
  · intro t h
    exact onlineMixture_comparator_factor_bound E c (b t h.1) ha.ne' hη hM (H.mean_bound t h.1)
      centers hc q.property (weights t h.1).property h.2
  · exact predictableGaussianComparator_moment A K b H hp hp2 hs c hη ha haR htune centers hc weights q

theorem predictableGaussian_regret_tail {T : ℕ} (A : Policy Seed Query E Output T)
    (K : Kernel Query E) [IsMarkovKernel K] (P : Measure Seed) [IsProbabilityMeasure P]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R η a β ε δ : ℝ}
    (H : PredictableNoiseContract A K b p s V M) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (c : E) (hM : 0 ≤ M) (hη : 0 < η) (ha : 0 < a) (haR : a ≤ R)
    (htune : η * M * R ≤ 1 / 16) (hβ : 0 < β) (hε : 0 < ε) (hδ : 0 < δ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (initial q : SimplexPoint ι) (n : ℕ) :
    let weights := onlineHistoryWeights c a η β centers hε initial
    (A.historyLaw P K n).real {h |
      (gaussianOnlineDivergence E c a β centers q.val initial.val +
        n * (η ^ 2 * M ^ 2 / (2 * β) + ε) +
        2 * (n * (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) + Real.log (1 / δ))) / η <
      historySum (predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val)) n h} ≤ 2 * δ := by
  let weights := onlineHistoryWeights (Seed := Seed) c a η β centers hε initial
  let ν := mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))
  let tailW : Set (History Seed E n) := {h | n * ν + Real.log (1 / δ) <
    historySum (fun t h => Real.log (predictableGaussianW c a η centers weights b t h)) n h}
  let tailQ : Set (History Seed E n) := {h | n * ν + Real.log (1 / δ) <
    historySum (fun t h => Real.log (predictableGaussianComparator c a η centers weights b q t h)) n h}
  have hw : ∀ t, Measurable (weights t) := onlineHistoryWeights_measurable c a η β centers hε initial
  have hW : (A.historyLaw P K n).real tailW ≤ δ := predictableGaussianW_tail A K P b H
    hp hp2 hs c hM hη.le ha haR htune hδ centers hc weights hw n
  have hQ : (A.historyLaw P K n).real tailQ ≤ δ := predictableGaussianComparator_tail A K P b H
    hp hp2 hs c hM hη.le ha haR htune hδ centers hc weights hw q n
  have hsub : {h | (gaussianOnlineDivergence E c a β centers q.val initial.val +
        n * (η ^ 2 * M ^ 2 / (2 * β) + ε) + 2 * (n * ν + Real.log (1 / δ))) / η <
      historySum (predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val)) n h} ⊆
      tailW ∪ tailQ := by
    intro h hh
    by_cases hw' : h ∈ tailW
    · exact Or.inl hw'
    · right
      by_contra hq'
      have hm := gaussianHistory_canonical_master c ha.ne' hη.le hβ hM hε centers initial b H.mean_bound q n h
      have hwle : historySum (fun t h => Real.log (predictableGaussianW c a η centers weights b t h)) n h ≤
          n * ν + Real.log (1 / δ) := le_of_not_gt hw'
      have hqle : historySum (fun t h => Real.log (predictableGaussianComparator c a η centers weights b q t h)) n h ≤
          n * ν + Real.log (1 / δ) := le_of_not_gt hq'
      have hlt := (div_lt_iff₀ hη).mp hh
      change η * historySum (predictableGaussianRegret centers weights b (finiteMixtureMean centers q.val)) n h ≤ _ at hm
      nlinarith only [hm, hwle, hqle, hlt]
  have hprob := (measureReal_mono (μ := A.historyLaw P K n) hsub).trans
    (measureReal_union_le (μ := A.historyLaw P K n) tailW tailQ)
  dsimp only
  exact hprob.trans (by linarith only [hW, hQ])

end HeavyTail.GaussianEntropy
