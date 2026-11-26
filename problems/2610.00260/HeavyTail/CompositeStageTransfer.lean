import HeavyTail.CompositeStageAverage
import HeavyTail.AcceptedOracleRegularity

/-! The concrete composite stage's online-to-batch transfer, including the
accepted-mean bias. It is proved on each successful raw history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical InnerProductSpace
namespace HeavyTail.PrivateInstance
universe u
variable {E W : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace W]
  {θ : OracleParameters} {B : PublicProblem E θ}

def objectiveGap (I : PrivateInstance B) (x : E) : ℝ := I.f x + B.h x - I.optimalValue

theorem objectiveGap_convex (I : PrivateInstance B) : ConvexOn ℝ B.S I.objectiveGap := by
  have h := ((I.f_convex.subset B.domain_subset B.h_convex.1).add B.h_convex).add_const (-I.optimalValue)
  simpa only [Pi.add_apply, sub_eq_add_neg, objectiveGap] using h

def stageAcceptedMeanIncrement (I : PrivateInstance B) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R)
    (t : ℕ) (h : AdaptiveKernel.History PUnit E t × E) : ℝ :=
  let M := B.stageRule hR hn τ L
  let s := M.state (PublicProblem.stageInitial L) n t h.1
  let z := L.point s.2.1
  if (s, h.2) ∈ M.activeAcceptance n then
    ⟪I.acceptedMean hR hn τ z, z - I.minimizer⟫_ℝ else 0

theorem acceptedMean_objective_transfer (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    I.objectiveGap (selectedProximalPoint B.prox θ.G_pos hR hn z) ≤
      ⟪I.acceptedMean hR hn τ z, z - I.minimizer⟫_ℝ +
        2 * R * (rejectionConstant θ.p * θ.s * (θ.L / τ) ^ (θ.p - 1)) + θ.G * R / (2 * n) := by
  have ht := (I.correctedMean_bound_transfer hR hn z hz).2
  have hb := (I.acceptedRawLaw_bounds hR hn hτ z hz).2.2.1
  have hB : 0 ≤ rejectionConstant θ.p * θ.s * (θ.L / τ) ^ (θ.p - 1) := by
    have hL := θ.s_pos.trans_le θ.s_le_L
    have hτpos : 0 < τ := by linarith [θ.G_pos]
    have hC := (rejectionConstant_pos θ.p).le
    exact mul_nonneg (mul_nonneg hC θ.s_pos.le)
      (Real.rpow_nonneg (div_nonneg hL.le hτpos.le) _)
  have hi := real_inner_le_norm (I.correctedMean hR hn z - I.acceptedMean hR hn τ z) (z - I.minimizer)
  have hp := mul_le_mul hb hz (norm_nonneg (z - I.minimizer)) hB
  rw [norm_sub_rev (I.correctedMean hR hn z) (I.acceptedMean hR hn τ z)] at hi
  rw [inner_sub_left] at hi
  change I.f _ + B.h _ - I.optimalValue ≤ _ at ht ⊢
  nlinarith only [ht, hi, hp]

theorem stage_increment_transfer (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R)
    (t : ℕ) (h : AdaptiveKernel.History PUnit E t × E) :
    B.stageObjectiveIncrement hR hn τ L I.objectiveGap t h ≤
      I.stageAcceptedMeanIncrement hR hn τ L t h +
        (2 * R * (rejectionConstant θ.p * θ.s * (θ.L / τ) ^ (θ.p - 1)) + θ.G * R / (2 * n)) := by
  dsimp only [PublicProblem.stageObjectiveIncrement, stageAcceptedMeanIncrement]
  split_ifs
  · simpa only [add_assoc] using I.acceptedMean_objective_transfer hR hn hτ _
      (I.stageLearner_point_distance L hc
        ((B.stageRule hR hn τ L).state (PublicProblem.stageInitial L) n t h.1).2.1)
  · have hL := θ.s_pos.trans_le θ.s_le_L
    have hτpos : 0 < τ := by linarith [θ.G_pos]
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hC := (rejectionConstant_pos θ.p).le
    have hs := θ.s_pos
    have hG := θ.G_pos
    positivity

/-- The actual output's objective error is bounded by the accepted-mean
regret sum. Rejected/inactive raw rounds contribute zero to that sum. -/
theorem stage_online_to_batch (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (T : ℕ)
    (history : AdaptiveKernel.History PUnit E T)
    (hsuccess : n ≤ ((B.stageRule hR hn τ L).state (PublicProblem.stageInitial L) n T history).1) :
    (n : ℝ) * I.objectiveGap ((B.cappedStagePolicy hR hn τ L T).output history) ≤
      AdaptiveKernel.historySum (I.stageAcceptedMeanIncrement hR hn τ L) T history +
        (T : ℝ) * (2 * R * (rejectionConstant θ.p * θ.s * (θ.L / τ) ^ (θ.p - 1)) +
          θ.G * R / (2 * n)) := by
  have hj := B.stage_average_jensen hR hn τ L I.objectiveGap_convex T history
  have hcounters := B.stage_state_counts hR hn τ L T history
  have hcap := (B.stageRule hR hn τ L).state_count_le (PublicProblem.stageInitial L) n T history
  have hcount : (((B.stageRule hR hn τ L).state (PublicProblem.stageInitial L) n T history).2).2.2 = n := by omega
  dsimp only at hj
  rw [hcount] at hj
  rw [B.stage_output_eq_average hR hn τ L T history hsuccess]
  apply hj.trans
  have hs := AdaptiveKernel.historySum_mono (I.stage_increment_transfer hR hn hτ L hc) T history
  rw [AdaptiveKernel.historySum_add, AdaptiveKernel.historySum_const] at hs
  exact hs

end HeavyTail.PrivateInstance
