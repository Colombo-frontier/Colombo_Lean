import HeavyTail.GaussianHistoryFactors
import HeavyTail.CompositeStageTransfer

/-! The pathwise master inequality for the actual capped raw history.
The local first-order property is the proved implementation contract of a
Gaussian update; neither stability nor a regret bound is an assumption. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical

namespace HeavyTail
universe u
variable {E ι : Type u} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters}

namespace GaussianEntropy

theorem gaussian_first_order_master_step {c : E} {a η β M ε : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β) (hM : 0 ≤ M)
    (centers : ι → E) (w y q : SimplexPoint ι) (Y b : E) (hb : ‖b‖ ≤ M)
    (hfirst : -ε ≤ (observedClippedLoss E c a η centers (Y, w.val) +
      gaussianOnlineDerivative E c a β centers y.val -
      gaussianOnlineDerivative E c a β centers w.val) (q.val - y.val)) :
    gaussianOnlineDivergence E c a β centers q.val y.val +
      η * ⟪b, finiteMixtureMean centers w.val - finiteMixtureMean centers q.val⟫_ℝ ≤
    gaussianOnlineDivergence E c a β centers q.val w.val + η ^ 2 * M ^ 2 / (2 * β) +
      Real.log (onlineMixtureW E c a η centers w.val Y b (finiteMixtureMean centers w.val)) +
      (∫ u, onlineMixtureError E η Y b (finiteMixtureMean centers w.val) u
        ∂physicalGaussianMixtureLaw E c a centers q.val) + ε := by
  have ht := approximate_mirror_update (H := gaussianOnlineGenerator E c a β centers)
    (observedClippedLoss E c a η centers (Y, w.val)) hfirst
  have hs := gaussian_online_stability_bound E c ha hη hβ hM centers y.property w.property Y b hb
  have he := onlineMixtureError_integral E c ha η centers q.property w.val Y b
  have hi : ⟪b, finiteMixtureMean centers w.val - finiteMixtureMean centers q.val⟫_ℝ =
      -⟪b, finiteMixtureMean centers q.val - finiteMixtureMean centers w.val⟫_ℝ := by
    simp only [inner_sub_right]
    ring
  rw [hi]
  dsimp only [gaussianOnlineDivergence, gaussianOnlineGenerator, gaussianOnlineDerivative] at ht hs ⊢
  linarith only [ht, hs, he]

end GaussianEntropy

namespace PublicProblem
open GaussianEntropy

theorem stageLearnerState_gaussian_succ (B : PublicProblem E θ)
    {c : E} {R : ℝ} {n : ℕ} (hR : 0 < R) (hn : 0 < n) (τ : ℝ)
    (centers : ι → E) (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (t : ℕ) (h : AdaptiveKernel.History PUnit E t × E) :
    B.stageLearnerState hR hn τ L (t + 1) h =
      let s := B.stageLearnerState hR hn τ L t h.1
      if (s, h.2) ∈ PrivateInstance.gaussianRawAcceptance B hR hn τ centers then
        (s.1 + 1, L.update (s.2, B.correctedReply hR hn (finiteMixtureMean centers s.2.val) h.2))
      else s := by
  simp only [stageLearnerState, CappedRaw.Rule.state, CappedRaw.Rule.step,
    CappedRaw.Rule.activeAcceptance, PrivateInstance.gaussianRawAcceptance, mem_setOf_eq,
    stageRule, hpoint]
  split_ifs <;> rfl

end PublicProblem

namespace PrivateInstance
open GaussianEntropy
variable {B : PublicProblem E θ}

def gaussianHistoryMeanIncrement (I : PrivateInstance B) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (centers : ι → E)
    (L : StageLearner (SimplexPoint ι) E c R) (q : SimplexPoint ι) (t : ℕ)
    (h : AdaptiveKernel.History PUnit E t × E) : ℝ :=
  let s := B.stageLearnerState hR hn τ L t h.1
  let z := finiteMixtureMean centers s.2.val
  if (s, h.2) ∈ gaussianRawAcceptance B hR hn τ centers then
    ⟪I.acceptedMean hR hn τ z, z - finiteMixtureMean centers q.val⟫_ℝ else 0

theorem gaussianHistory_step (I : PrivateInstance B) {c : E} {R τ a η β ε : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (hfirst : ∀ (w : SimplexPoint ι) (Y : E) (q : SimplexPoint ι),
      -ε ≤ (observedClippedLoss E c a η centers (Y, w.val) +
        gaussianOnlineDerivative E c a β centers (L.update (w, Y)).val -
        gaussianOnlineDerivative E c a β centers w.val) (q.val - (L.update (w, Y)).val))
    (q : SimplexPoint ι) (t : ℕ) (h : AdaptiveKernel.History PUnit E t × E) :
    let s := B.stageLearnerState hR hn τ L t h.1
    let s' := B.stageLearnerState hR hn τ L (t + 1) h
    let κ := η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε
    gaussianOnlineDivergence E c a β centers q.val s'.2.val +
      η * I.gaussianHistoryMeanIncrement hR hn τ centers L q t h + s.1 * κ ≤
    gaussianOnlineDivergence E c a β centers q.val s.2.val + s'.1 * κ +
      Real.log (I.gaussianHistoryW hR hn τ a η centers L t h) +
      Real.log (I.gaussianHistoryComparatorFactor hR hn τ a η centers L q t h) := by
  dsimp only
  rw [B.stageLearnerState_gaussian_succ hR hn τ centers L hpoint]
  let s := B.stageLearnerState hR hn τ L t h.1
  by_cases hactive : (s, h.2) ∈ gaussianRawAcceptance B hR hn τ centers
  · have hs := gaussian_first_order_master_step ha hη hβ (acceptedMeanScale_pos θ hτ).le
      centers s.2 (L.update (s.2, B.correctedReply hR hn (finiteMixtureMean centers s.2.val) h.2)) q
      (B.correctedReply hR hn (finiteMixtureMean centers s.2.val) h.2)
      (I.acceptedMean hR hn τ (finiteMixtureMean centers s.2.val))
      (I.acceptedMean_bound hR hn hτ _ (I.acceptedMixtureMean_distance centers hc hcenter s.2))
      (hfirst s.2 _ q)
    simp only [s] at hactive hs
    simp only [gaussianHistoryMeanIncrement, gaussianHistoryW, gaussianHistoryComparatorFactor,
      gaussianRawW, gaussianRawComparatorFactor, acceptedGaussianW, acceptedGaussianComparatorFactor,
      if_pos hactive, Real.log_exp, Nat.cast_add, Nat.cast_one]
    linarith only [hs]
  · simp only [s] at hactive
    simp only [gaussianHistoryMeanIncrement, gaussianHistoryW, gaussianHistoryComparatorFactor,
      gaussianRawW, gaussianRawComparatorFactor, if_neg hactive, Real.log_one, mul_zero,
      add_zero, le_refl]

/-- The pathwise master inequality on the actual raw history, retaining the
terminal divergence and charging only actual accepted updates. -/
theorem gaussianHistory_master (I : PrivateInstance B) {c : E} {R τ a η β ε : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (hfirst : ∀ (w : SimplexPoint ι) (Y : E) (q : SimplexPoint ι),
      -ε ≤ (observedClippedLoss E c a η centers (Y, w.val) +
        gaussianOnlineDerivative E c a β centers (L.update (w, Y)).val -
        gaussianOnlineDerivative E c a β centers w.val) (q.val - (L.update (w, Y)).val))
    (q : SimplexPoint ι) (T : ℕ) (h : AdaptiveKernel.History PUnit E T) :
    gaussianOnlineDivergence E c a β centers q.val
        (B.stageLearnerState hR hn τ L T h).2.val +
      η * AdaptiveKernel.historySum (I.gaussianHistoryMeanIncrement hR hn τ centers L q) T h ≤
    gaussianOnlineDivergence E c a β centers q.val L.initial.val +
      (B.stageLearnerState hR hn τ L T h).1 *
        (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
      AdaptiveKernel.historySum (fun t h => Real.log (I.gaussianHistoryW hR hn τ a η centers L t h)) T h +
      AdaptiveKernel.historySum
        (fun t h => Real.log (I.gaussianHistoryComparatorFactor hR hn τ a η centers L q t h)) T h := by
  induction T with
  | zero => simp [PublicProblem.stageLearnerState, CappedRaw.Rule.state,
      PublicProblem.stageInitial, AdaptiveKernel.historySum]
  | succ T ih =>
      have hs := I.gaussianHistory_step hR hn hτ centers hc hcenter ha hη hβ L hpoint hfirst q T h
      have hp := ih h.1
      simp only [AdaptiveKernel.historySum]
      dsimp only at hs
      linarith only [hp, hs]

theorem gaussianHistory_regret_bound (I : PrivateInstance B) {c : E} {R τ a η β ε : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β) (hε : 0 ≤ ε)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (hfirst : ∀ (w : SimplexPoint ι) (Y : E) (q : SimplexPoint ι),
      -ε ≤ (observedClippedLoss E c a η centers (Y, w.val) +
        gaussianOnlineDerivative E c a β centers (L.update (w, Y)).val -
        gaussianOnlineDerivative E c a β centers w.val) (q.val - (L.update (w, Y)).val))
    (q : SimplexPoint ι) (T : ℕ) (h : AdaptiveKernel.History PUnit E T) :
    η * AdaptiveKernel.historySum (I.gaussianHistoryMeanIncrement hR hn τ centers L q) T h ≤
    gaussianOnlineDivergence E c a β centers q.val L.initial.val +
      n * (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
      AdaptiveKernel.historySum (fun t h => Real.log (I.gaussianHistoryW hR hn τ a η centers L t h)) T h +
      AdaptiveKernel.historySum
        (fun t h => Real.log (I.gaussianHistoryComparatorFactor hR hn τ a η centers L q t h)) T h := by
  have hm := I.gaussianHistory_master hR hn hτ centers hc hcenter ha hη hβ L hpoint hfirst q T h
  have hD := gaussianOnlineDivergence_nonneg E c a hβ.le centers q.property
    (B.stageLearnerState hR hn τ L T h).2.property
  have hcount : (B.stageLearnerState hR hn τ L T h).1 ≤ n :=
    (B.stageRule hR hn τ L).state_count_le (PublicProblem.stageInitial L) n T h
  have hκ : 0 ≤ η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε := by positivity
  have hc := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount :
      ((B.stageLearnerState hR hn τ L T h).1 : ℝ) ≤ n) hκ
  linarith only [hm, hD, hc]

theorem gaussianHistory_comparator_transfer (I : PrivateInstance B) {c : E} {R τ ρ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (hρ : 0 ≤ ρ)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (q : SimplexPoint ι) (hq : ‖finiteMixtureMean centers q.val - I.minimizer‖ ≤ ρ)
    (T : ℕ) (h : AdaptiveKernel.History PUnit E T) :
    AdaptiveKernel.historySum (I.stageAcceptedMeanIncrement hR hn τ L) T h ≤
      AdaptiveKernel.historySum (I.gaussianHistoryMeanIncrement hR hn τ centers L q) T h +
        T * acceptedMeanScale θ τ * ρ := by
  have hstep (t : ℕ) (h : AdaptiveKernel.History PUnit E t × E) :
      I.stageAcceptedMeanIncrement hR hn τ L t h ≤
        I.gaussianHistoryMeanIncrement hR hn τ centers L q t h + acceptedMeanScale θ τ * ρ := by
    let s := B.stageLearnerState hR hn τ L t h.1
    let z := finiteMixtureMean centers s.2.val
    have hb := I.acceptedMean_bound hR hn hτ z (I.acceptedMixtureMean_distance centers hc hcenter s.2)
    have hi := (real_inner_le_norm (I.acceptedMean hR hn τ z)
      (finiteMixtureMean centers q.val - I.minimizer)).trans
      (mul_le_mul hb hq (norm_nonneg _) (acceptedMeanScale_pos θ hτ).le)
    have he : ⟪I.acceptedMean hR hn τ z, z - I.minimizer⟫_ℝ ≤
        ⟪I.acceptedMean hR hn τ z, z - finiteMixtureMean centers q.val⟫_ℝ + acceptedMeanScale θ τ * ρ := by
      simp only [inner_sub_right] at hi ⊢
      dsimp only [acceptedMeanScale, acceptedBiasScale]
      linarith only [hi]
    have hacc : (B.stageRule hR hn τ L).acceptance =
        {p | (L.point p.1.1, p.2) ∈ B.stageAcceptance hR hn τ} := rfl
    simp only [stageAcceptedMeanIncrement, gaussianHistoryMeanIncrement,
      PublicProblem.stageLearnerState, CappedRaw.Rule.activeAcceptance, gaussianRawAcceptance,
      hacc, mem_setOf_eq, hpoint]
    split_ifs
    · exact he
    · exact le_add_of_nonneg_right (mul_nonneg (acceptedMeanScale_pos θ hτ).le hρ)
  have hs := AdaptiveKernel.historySum_mono hstep T h
  rw [AdaptiveKernel.historySum_add, AdaptiveKernel.historySum_const] at hs
  simpa only [mul_assoc] using hs

end PrivateInstance
end HeavyTail
