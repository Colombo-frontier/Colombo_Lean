import HeavyTail.GaussianHistoryFactors
import HeavyTail.RawBudgetCalibration

/-! A joint good event for the actual capped stage: enough accepted replies
and both derived Gaussian log-factor bounds. -/
noncomputable section
open MeasureTheory Set
open scoped Classical

namespace HeavyTail.PrivateInstance
open GaussianEntropy
universe u
variable {E ι : Type u} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters} {B : PublicProblem E θ}

def gaussianStageGoodEvent (I : PrivateInstance B) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ a η δ : ℝ) (centers : ι → E)
    (L : StageLearner (SimplexPoint ι) E c R) (q : SimplexPoint ι) (T : ℕ) :
    Set (AdaptiveKernel.History PUnit E T) :=
  {h | n ≤ (B.stageLearnerState hR hn τ L T h).1 ∧
    AdaptiveKernel.historySum (fun t h => Real.log (I.gaussianHistoryW hR hn τ a η centers L t h)) T h ≤
      (T : ℝ) * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ) ∧
    AdaptiveKernel.historySum
      (fun t h => Real.log (I.gaussianHistoryComparatorFactor hR hn τ a η centers L q t h)) T h ≤
      (T : ℝ) * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ)}

theorem gaussianStageGoodEvent_compl_probability (I : PrivateInstance B)
    {c : E} {R τ a η δ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val) (q : SimplexPoint ι)
    (P : Measure PUnit) [IsProbabilityMeasure P] (hδ : 0 < δ) :
    ((B.cappedStagePolicy hR hn τ L (4 * n)).historyLaw P I.oracle (4 * n)).real
      (I.gaussianStageGoodEvent hR hn τ a η δ centers L q (4 * n))ᶜ ≤
        ((2 : ℝ) ^ (8 * n))⁻¹ + 2 * δ := by
  let μ := (B.cappedStagePolicy hR hn τ L (4 * n)).historyLaw P I.oracle (4 * n)
  let failure : Set (AdaptiveKernel.History PUnit E (4 * n)) :=
    {h | (B.stageLearnerState hR hn τ L (4 * n) h).1 < n}
  let tailW : Set (AdaptiveKernel.History PUnit E (4 * n)) :=
    {h | ((4 * n : ℕ) : ℝ) * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ) <
      AdaptiveKernel.historySum (fun t h => Real.log (I.gaussianHistoryW hR hn τ a η centers L t h)) (4 * n) h}
  let tailQ : Set (AdaptiveKernel.History PUnit E (4 * n)) :=
    {h | ((4 * n : ℕ) : ℝ) * acceptedOnlineExponent θ τ R a η + Real.log (1 / δ) <
      AdaptiveKernel.historySum
        (fun t h => Real.log (I.gaussianHistoryComparatorFactor hR hn τ a η centers L q t h)) (4 * n) h}
  have hsub : (I.gaussianStageGoodEvent hR hn τ a η δ centers L q (4 * n))ᶜ ⊆
      failure ∪ (tailW ∪ tailQ) := by
    intro h hh
    by_cases hs : n ≤ (B.stageLearnerState hR hn τ L (4 * n) h).1
    · right
      by_cases hw : h ∈ tailW
      · exact Or.inl hw
      · right
        by_contra hq
        apply hh
        exact ⟨hs, le_of_not_gt hw, le_of_not_gt hq⟩
    · exact Or.inl (Nat.lt_of_not_ge hs)
  have hf : μ.real failure ≤ ((2 : ℝ) ^ (8 * n))⁻¹ :=
    I.cappedStage_failure_probability hR hn hτ L hcenter (4 * n) P
  have hw : μ.real tailW ≤ δ :=
    I.gaussianHistoryW_tail hR hn hτ centers hc hcenter ha haR hη htune L hpoint P hδ (4 * n)
  have hq : μ.real tailQ ≤ δ :=
    I.gaussianHistoryComparatorFactor_tail hR hn hτ centers hc hcenter ha haR hη htune L hpoint q P hδ (4 * n)
  have hu := measureReal_union_le (μ := μ) failure (tailW ∪ tailQ)
  have hv := measureReal_union_le (μ := μ) tailW tailQ
  have hm := measureReal_mono (μ := μ) hsub
  change μ.real _ ≤ _
  linarith only [hf, hw, hq, hu, hv, hm]

theorem gaussianStageGoodEvent_confidence (I : PrivateInstance B)
    {c : E} {R τ a η α : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (L : StageLearner (SimplexPoint ι) E c R)
    (hpoint : ∀ w, L.point w = finiteMixtureMean centers w.val) (q : SimplexPoint ι)
    (P : Measure PUnit) [IsProbabilityMeasure P] (hα : 0 < α)
    (hnlog : Real.log (3 / α) ≤ (n : ℝ)) :
    ((B.cappedStagePolicy hR hn τ L (4 * n)).historyLaw P I.oracle (4 * n)).real
      (I.gaussianStageGoodEvent hR hn τ a η (α / 4) centers L q (4 * n))ᶜ ≤ α := by
  have hg := I.gaussianStageGoodEvent_compl_probability hR hn hτ centers hc hcenter ha haR
    hη htune L hpoint q P (show 0 < α / 4 by positivity)
  have hc := rawBudgetTail_le_confidence hα n hnlog
  linarith only [hg, hc]

end HeavyTail.PrivateInstance
