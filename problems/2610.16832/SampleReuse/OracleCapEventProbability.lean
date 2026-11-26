import SampleReuse.OracleCapProbability
import SampleReuse.CurvatureFirstJointAccuracy

open MeasureTheory
open scoped Classical

namespace SampleReuse
noncomputable section

/-- Event-level cap composition permits sectionwise analysis of stopped
surrogate costs while measuring only the actual observable execution. -/
theorem capped_success_probability_of_events {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (good exhausted : Ω → Prop) (output cappedOutput : Ω → X) (success : X → Prop)
    (actualG actualH : Ω → ℕ) (Cg CH : ℕ)
    (hmeas : MeasurableSet {w | good w ∧ ¬exhausted w ∧ actualG w ≤ Cg ∧ actualH w ≤ CH})
    {δbad δexhaust δG δH : ℝ}
    (hbad : μ.real {w | ¬good w} ≤ δbad)
    (hexhaust : μ.real {w | good w ∧ exhausted w} ≤ δexhaust)
    (hG : μ.real {w | good w ∧ Cg < actualG w} ≤ δG)
    (hH : μ.real {w | good w ∧ CH < actualH w} ≤ δH)
    (hsuccess : ∀ w, good w → ¬exhausted w → success (output w))
    (hagree : ∀ w, actualG w ≤ Cg → actualH w ≤ CH → cappedOutput w = output w) :
    1-(δbad+δexhaust+δG+δH) ≤ μ.real {w | success (cappedOutput w)} := by
  let E := {w | good w ∧ ¬exhausted w ∧ actualG w ≤ Cg ∧ actualH w ≤ CH}
  have hsub : Eᶜ ⊆ (({w | ¬good w} ∪ {w | good w ∧ exhausted w}) ∪
      {w | good w ∧ Cg < actualG w}) ∪ {w | good w ∧ CH < actualH w} := by
    intro w hw
    by_cases hg : good w
    · by_cases he : exhausted w
      · exact Or.inl (Or.inl (Or.inr ⟨hg,he⟩))
      · by_cases hcg : actualG w ≤ Cg
        · have hch : CH < actualH w := by
            by_contra hn
            exact hw ⟨hg,he,hcg,le_of_not_gt hn⟩
          exact Or.inr ⟨hg,hch⟩
        · exact Or.inl (Or.inr ⟨hg,Nat.lt_of_not_ge hcg⟩)
    · exact Or.inl (Or.inl (Or.inl hg))
  have hμ := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  have hu₁ := measureReal_union_le (μ := μ)
    ({w | ¬good w} ∪ {w | good w ∧ exhausted w}) {w | good w ∧ Cg < actualG w}
  have hu₂ := measureReal_union_le (μ := μ) {w | ¬good w} {w | good w ∧ exhausted w}
  have hE : 1-(δbad+δexhaust+δG+δH) ≤ μ.real E := by
    rw [measureReal_compl hmeas,measureReal_univ_eq_one] at hμ
    linarith
  apply hE.trans (measureReal_mono ?_)
  intro w hw
  change success (cappedOutput w)
  rw [hagree w hw.2.2.1 hw.2.2.2]
  exact hsuccess w hw.1 hw.2.1

/-- A fixed external tape can use any integrable stopped cost dominating
the actual count on good executions; no joint measurability of that cost is
required to obtain the section probability bound. -/
theorem good_queryCount_exceed_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (good : Ω → Prop)
    (actual shadow : Ω → ℕ) (hdom : ∀ w, good w → actual w ≤ shadow w)
    (hi : Integrable (fun w => (shadow w : ℝ)) μ) (cap : ℕ) {B : ℝ}
    (hB : (∫ w, (shadow w : ℝ) ∂μ) ≤ B) :
    μ.real {w | good w ∧ cap < actual w} ≤ B/((cap : ℝ)+1) := by
  apply (measureReal_mono (μ := μ) (show {w | good w ∧ cap < actual w} ⊆ {w | cap < shadow w} from
    fun w hw => hw.2.trans_le (hdom w hw.1))).trans
  exact queryCount_exceed_probability shadow hi cap hB

end
end SampleReuse
