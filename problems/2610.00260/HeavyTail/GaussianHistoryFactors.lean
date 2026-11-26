import HeavyTail.GaussianRawFactors
import HeavyTail.GaussianStageLearner

/-! The Gaussian factors evaluated on the actual capped raw histories.
Concentration is obtained from the original oracle kernel, not an assumed
conditional moment or terminal regret bound. -/

noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators InnerProductSpace Classical

namespace HeavyTail
universe u
variable {E W ι : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters}

namespace PublicProblem
variable [MeasurableSpace W]

def stageLearnerState (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R)
    (t : ℕ) (history : AdaptiveKernel.History PUnit E t) : ℕ × W :=
  let s := (B.stageRule hR hn τ L).state (stageInitial L) n t history
  (s.1, s.2.1)

theorem stageLearnerState_measurable (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R) (t : ℕ) :
    Measurable (B.stageLearnerState hR hn τ L t) := by
  have hs := (B.stageRule hR hn τ L).state_measurable
    (show Measurable (stageInitial L) from measurable_const) n t
  exact hs.fst.prodMk hs.snd.fst

end PublicProblem

namespace PrivateInstance
open GaussianEntropy
variable [Fintype ι] {B : PublicProblem E θ}

def gaussianHistoryW (I : PrivateInstance B) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ a η : ℝ) (centers : ι → E)
    (L : StageLearner (SimplexPoint ι) E c R) (t : ℕ)
    (h : AdaptiveKernel.History PUnit E t × E) : ℝ :=
  I.gaussianRawW hR hn τ c a η centers (B.stageLearnerState hR hn τ L t h.1, h.2)

def gaussianHistoryComparatorFactor (I : PrivateInstance B) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ a η : ℝ) (centers : ι → E)
    (L : StageLearner (SimplexPoint ι) E c R) (q : SimplexPoint ι) (t : ℕ)
    (h : AdaptiveKernel.History PUnit E t × E) : ℝ :=
  I.gaussianRawComparatorFactor hR hn τ c a η centers q
    (B.stageLearnerState hR hn τ L t h.1, h.2)

theorem gaussianHistoryW_measurable (I : PrivateInstance B) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ a η : ℝ) (centers : ι → E)
    (L : StageLearner (SimplexPoint ι) E c R) (t : ℕ) :
    Measurable (I.gaussianHistoryW hR hn τ a η centers L t) :=
  (I.gaussianRawW_measurable hR hn τ c a η centers).comp
    (((B.stageLearnerState_measurable hR hn τ L t).comp measurable_fst).prodMk measurable_snd)

theorem gaussianHistoryComparatorFactor_measurable (I : PrivateInstance B) {c : E} {R a : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (ha : a ≠ 0) (η : ℝ) (centers : ι → E)
    (L : StageLearner (SimplexPoint ι) E c R) (q : SimplexPoint ι) (t : ℕ) :
    Measurable (I.gaussianHistoryComparatorFactor hR hn τ a η centers L q t) :=
  (I.gaussianRawComparatorFactor_measurable hR hn τ c ha η centers q).comp
    (((B.stageLearnerState_measurable hR hn τ L t).comp measurable_fst).prodMk measurable_snd)

theorem gaussianHistoryW_moment (I : PrivateInstance B) {c : E} {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (T t : ℕ) (h : AdaptiveKernel.History PUnit E t) :
    (∫ g, I.gaussianHistoryW hR hn τ a η centers L t (h, g)
      ∂I.oracle ((B.cappedStagePolicy hR hn τ L T).query t h)) ≤
      Real.exp (acceptedOnlineExponent θ τ R a η) := by
  let s := B.stageLearnerState hR hn τ L t h
  change (∫ g, I.gaussianRawW hR hn τ c a η centers (s, g)
    ∂I.stageRawKernel hR hn (L.point s.2)) ≤ _
  rw [hpoint s.2]
  exact I.gaussianRawW_moment hR hn hτ c centers hc hcenter ha haR hη htune s.1 s.2

theorem gaussianHistoryComparatorFactor_moment (I : PrivateInstance B)
    {c : E} {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val) (q : SimplexPoint ι)
    (T t : ℕ) (h : AdaptiveKernel.History PUnit E t) :
    (∫ g, I.gaussianHistoryComparatorFactor hR hn τ a η centers L q t (h, g)
      ∂I.oracle ((B.cappedStagePolicy hR hn τ L T).query t h)) ≤
      Real.exp (acceptedOnlineExponent θ τ R a η) := by
  let s := B.stageLearnerState hR hn τ L t h
  change (∫ g, I.gaussianRawComparatorFactor hR hn τ c a η centers q (s, g)
    ∂I.stageRawKernel hR hn (L.point s.2)) ≤ _
  rw [hpoint s.2]
  exact I.gaussianRawComparatorFactor_moment hR hn hτ c centers hc hcenter ha haR hη htune q s.1 s.2

theorem gaussianHistoryW_tail (I : PrivateInstance B) {c : E} {R τ a η δ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val)
    (P : Measure PUnit) [IsProbabilityMeasure P] (hδ : 0 < δ) (T : ℕ) :
    ((B.cappedStagePolicy hR hn τ L T).historyLaw P I.oracle T).real
      {h | (T : ℝ) * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ) <
        AdaptiveKernel.historySum (fun t h => Real.log (I.gaussianHistoryW hR hn τ a η centers L t h)) T h} ≤ δ := by
  apply AdaptiveKernel.history_log_sum_tail (B.cappedStagePolicy hR hn τ L T) P I.oracle
    (B := acceptedGaussianFactorCap θ τ R a η)
    ((zero_le_one).trans (acceptedGaussianFactorCap_ge_one θ hτ hR.le hη)) hδ
    (I.gaussianHistoryW_measurable hR hn τ a η centers L)
  · intro t h
    exact I.gaussianRawW_pos hR hn τ c a η centers _
  · intro t h
    exact I.gaussianRawW_bound hR hn hτ c centers hc hcenter ha.ne' hη _
  · exact I.gaussianHistoryW_moment hR hn hτ centers hc hcenter ha haR hη htune L hpoint T

theorem gaussianHistoryComparatorFactor_tail (I : PrivateInstance B)
    {c : E} {R τ a η δ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val) (q : SimplexPoint ι)
    (P : Measure PUnit) [IsProbabilityMeasure P] (hδ : 0 < δ) (T : ℕ) :
    ((B.cappedStagePolicy hR hn τ L T).historyLaw P I.oracle T).real
      {h | (T : ℝ) * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ) <
        AdaptiveKernel.historySum
          (fun t h => Real.log (I.gaussianHistoryComparatorFactor hR hn τ a η centers L q t h)) T h} ≤ δ := by
  apply AdaptiveKernel.history_log_sum_tail (B.cappedStagePolicy hR hn τ L T) P I.oracle
    (B := acceptedGaussianFactorCap θ τ R a η)
    ((zero_le_one).trans (acceptedGaussianFactorCap_ge_one θ hτ hR.le hη)) hδ
    (I.gaussianHistoryComparatorFactor_measurable hR hn τ ha.ne' η centers L q)
  · intro t h
    exact I.gaussianRawComparatorFactor_pos hR hn τ c a η centers q _
  · intro t h
    exact I.gaussianRawComparatorFactor_bound hR hn hτ c centers hc hcenter ha.ne' hη q _
  · exact I.gaussianHistoryComparatorFactor_moment hR hn hτ centers hc hcenter ha haR hη htune L hpoint q T

end PrivateInstance
end HeavyTail
