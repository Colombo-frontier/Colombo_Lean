import SampleReuse.OracleDerivativeCapsFinish
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
open scoped Classical

namespace SampleReuse
noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A natural-valued query count exceeds its cap only by reaching cap plus one. -/
theorem queryCount_exceed_probability (cost : Ω → ℕ)
    (hi : Integrable (fun w => (cost w : ℝ)) μ) (cap : ℕ) {B : ℝ}
    (hB : (∫ w, (cost w : ℝ) ∂μ) ≤ B) :
    μ.real {w | cap < cost w} ≤ B / ((cap : ℝ)+1) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun w => Nat.cast_nonneg (cost w))) hi ((cap : ℝ)+1)
  have he : {w | (cap : ℝ)+1 ≤ (cost w : ℝ)} = {w | cap < cost w} := by
    ext w
    change (cap : ℝ)+1 ≤ (cost w : ℝ) ↔ cap < cost w
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    omega
  rw [he] at hm
  apply (le_div_iff₀ (by positivity : 0 < (cap : ℝ)+1)).mpr
  simpa only [mul_comm] using hm.trans hB

/-- Surrogate query counts need dominate the actual counts only on the good
execution event. Thus stopping the analysis at the first inaccurate estimate
does not require an expected-cost claim for the untruncated execution. -/
theorem capped_success_failure_probability
    (good exhausted : Ω → Prop) (output cappedOutput : Ω → X) (success : X → Prop)
    (actualG actualH shadowG shadowH : Ω → ℕ) (Cg CH : ℕ)
    (hiG : Integrable (fun w => (shadowG w : ℝ)) μ)
    (hiH : Integrable (fun w => (shadowH w : ℝ)) μ)
    {BG BH δbad δexhaust : ℝ}
    (hBG : (∫ w, (shadowG w : ℝ) ∂μ) ≤ BG)
    (hBH : (∫ w, (shadowH w : ℝ) ∂μ) ≤ BH)
    (hbad : μ.real {w | ¬ good w} ≤ δbad)
    (hexhaust : μ.real {w | good w ∧ exhausted w} ≤ δexhaust)
    (hsuccess : ∀ w, good w → ¬ exhausted w → success (output w))
    (hG : ∀ w, good w → ¬ exhausted w → actualG w ≤ shadowG w)
    (hH : ∀ w, good w → ¬ exhausted w → actualH w ≤ shadowH w)
    (hagree : ∀ w, actualG w ≤ Cg → actualH w ≤ CH → cappedOutput w = output w) :
    μ.real {w | ¬ success (cappedOutput w)} ≤
      δbad+δexhaust+BG/((Cg : ℝ)+1)+BH/((CH : ℝ)+1) := by
  have hsub : {w | ¬ success (cappedOutput w)} ⊆
      (({w | ¬ good w} ∪ {w | good w ∧ exhausted w}) ∪
        {w | Cg < shadowG w}) ∪ {w | CH < shadowH w} := by
    intro w hw
    by_cases hg : good w
    · by_cases he : exhausted w
      · exact Or.inl (Or.inl (Or.inr ⟨hg,he⟩))
      · by_cases hcg : shadowG w ≤ Cg
        · by_cases hch : shadowH w ≤ CH
          · exact False.elim (hw (by rw [hagree w ((hG w hg he).trans hcg)
                ((hH w hg he).trans hch)]; exact hsuccess w hg he))
          · exact Or.inr (Nat.lt_of_not_ge hch)
        · exact Or.inl (Or.inr (Nat.lt_of_not_ge hcg))
    · exact Or.inl (Or.inl (Or.inl hg))
  have hm := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  have hu₁ := measureReal_union_le (μ := μ)
    ({w | ¬ good w} ∪ {w | good w ∧ exhausted w}) {w | Cg < shadowG w}
  have hu₂ := measureReal_union_le (μ := μ) {w | ¬ good w} {w | good w ∧ exhausted w}
  have hg := queryCount_exceed_probability shadowG hiG Cg hBG
  have hh := queryCount_exceed_probability shadowH hiH CH hBH
  linarith

theorem capped_success_probability
    (good exhausted : Ω → Prop) (output cappedOutput : Ω → X) (success : X → Prop)
    (actualG actualH shadowG shadowH : Ω → ℕ) (Cg CH : ℕ)
    (hiG : Integrable (fun w => (shadowG w : ℝ)) μ)
    (hiH : Integrable (fun w => (shadowH w : ℝ)) μ)
    {BG BH δbad δexhaust : ℝ}
    (hBG : (∫ w, (shadowG w : ℝ) ∂μ) ≤ BG)
    (hBH : (∫ w, (shadowH w : ℝ) ∂μ) ≤ BH)
    (hbad : μ.real {w | ¬ good w} ≤ δbad)
    (hexhaust : μ.real {w | good w ∧ exhausted w} ≤ δexhaust)
    (hsuccess : ∀ w, good w → ¬ exhausted w → success (output w))
    (hG : ∀ w, good w → ¬ exhausted w → actualG w ≤ shadowG w)
    (hH : ∀ w, good w → ¬ exhausted w → actualH w ≤ shadowH w)
    (hagree : ∀ w, actualG w ≤ Cg → actualH w ≤ CH → cappedOutput w = output w)
    (hmeas : MeasurableSet {w | success (cappedOutput w)}) :
    1-(δbad+δexhaust+BG/((Cg : ℝ)+1)+BH/((CH : ℝ)+1)) ≤
      μ.real {w | success (cappedOutput w)} := by
  have hf := capped_success_failure_probability good exhausted output cappedOutput success
    actualG actualH shadowG shadowH Cg CH hiG hiH hBG hBH hbad hexhaust hsuccess hG hH hagree
  have he : {w | ¬ success (cappedOutput w)} = {w | success (cappedOutput w)}ᶜ := rfl
  rw [he,measureReal_compl hmeas,measureReal_univ_eq_one] at hf
  linarith

/-- The rounded twelvefold expected budget leaves at most one twelfth of
failure probability for each derivative channel. -/
theorem queryBudget_twelvefold (B : ℝ) :
    B / ((⌈12*B⌉₊ : ℝ)+1) ≤ 1/12 := by
  have hc : 12*B ≤ (⌈12*B⌉₊ : ℝ) := Nat.le_ceil _
  apply (div_le_iff₀ (by positivity : 0 < (⌈12*B⌉₊ : ℝ)+1)).mpr
  nlinarith

end
end SampleReuse
