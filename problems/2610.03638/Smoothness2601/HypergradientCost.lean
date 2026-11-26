import Smoothness2601.HypergradientSource

/-! Source fixed sample budget for one fully executed outer direction. -/
noncomputable section
namespace Smoothness2601.HypergradientCost
open AdjointGeometry HypergradientGeometry HypergradientKernels

def finalConstant (b : Budgets) : ℝ := 2048*b.σ ^ 2+2/Real.log 2
def constant (b : Budgets) : ℝ :=
  InnerSource.costConstant b (32*innerSensitivity b)+
    AdjointSource.costConstant b (32*b.L₁)+finalConstant b

theorem finalConstant_pos (b : Budgets) : 0 < finalConstant b := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold finalConstant
  positivity

theorem constant_pos (b : Budgets) (hgap : b.μ < b.L₁) : 0 < constant b := by
  have hi := InnerSource.costConstant_pos b hgap (32*innerSensitivity b)
  have ha := AdjointSource.costConstant_pos b hgap.le (32*b.L₁)
  have ho := finalConstant_pos b
  unfold constant
  linarith

theorem final_budget (b : Budgets) (k : ℕ) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (AdjointSolve.stepSamples k h (outputBatch b ((2*k+1:ℕ)/h) ε):ℝ) ≤
      finalConstant b*((1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2)+(2*k+2:ℕ)*Real.log (2/ε)) := by
  let W : ℝ := (2*k+1:ℕ)/h
  have hn0 : 0 ≤ 1024*b.σ ^ 2*(1+W ^ 2)/ε ^ 2 := by positivity
  have hN : (outputBatch b W ε:ℝ) ≤ 1+1024*b.σ ^ 2*(1+W ^ 2)/ε ^ 2 := by
    unfold outputBatch
    rw [Nat.cast_max,Nat.cast_one]
    exact max_le (by linarith) (by linarith [Nat.ceil_lt_add_one hn0])
  have hs := AdjointSolve.step_samples_bound k hh (outputBatch b W ε) (outputBatch_pos b W ε)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 2)
    ((le_div_iff₀ hε).mpr (by nlinarith : (2:ℝ)*ε ≤ 2))
  have hlog0 : 0 ≤ Real.log (2/ε) := hl2.le.trans hlog
  have hI : 0 ≤ (2*k+2:ℕ)*Real.log (2/ε) := by positivity
  have hE : 0 ≤ (1+W ^ 2)*(1/ε ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ (2/Real.log 2)*((2*k+2:ℕ):ℝ))
  have he : (2/Real.log 2)*((2*k+2:ℕ):ℝ)*Real.log 2 = 2*((2*k+2:ℕ):ℝ) := by field_simp
  rw [he] at hmul
  have hover : 2+((2*k+2:ℕ):ℝ) ≤ (2/Real.log 2)*((2*k+2:ℕ)*Real.log (2/ε)) := by
    push_cast at hmul ⊢
    nlinarith
  have hcross₁ := mul_nonneg (by positivity : 0 ≤ 2048*b.σ ^ 2) hI
  have hcross₂ := mul_nonneg (by positivity : 0 ≤ 2/Real.log 2) hE
  change (AdjointSolve.stepSamples k h (outputBatch b W ε):ℝ) ≤ _
  change (AdjointSolve.stepSamples k h (outputBatch b W ε):ℝ) ≤ 2*(outputBatch b W ε:ℝ)+(2*k+2:ℕ) at hs
  have hmain : (AdjointSolve.stepSamples k h (outputBatch b W ε):ℝ) ≤
      2048*b.σ ^ 2*((1+W ^ 2)*(1/ε ^ 2))+(2/Real.log 2)*((2*k+2:ℕ)*Real.log (2/ε)) := by
    calc
      _ ≤ 2*(1+1024*b.σ ^ 2*(1+W ^ 2)/ε ^ 2)+(2*k+2:ℕ) :=
        hs.trans (add_le_add_right (mul_le_mul_of_nonneg_left hN (by norm_num)) _)
      _ = 2048*b.σ ^ 2*((1+W ^ 2)*(1/ε ^ 2))+(2+(2*k+2:ℕ)) := by ring
      _ ≤ _ := add_le_add_left hover _
  change _ ≤ finalConstant b*((1+W ^ 2)*(1/ε ^ 2)+(2*k+2:ℕ)*Real.log (2/ε))
  unfold finalConstant
  nlinarith

theorem per_outer_budget (b : Budgets) (hgap : b.μ < b.L₁) (k : ℕ) {h D ε : ℝ}
    (hh : 0 < h) (hD : 0 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεC : ε ≤ 32*innerSensitivity b) (hεL : ε ≤ 32*b.L₁) :
    (HypergradientSolve.samples b k h D (HypergradientSource.innerAccuracy b ε)
      (HypergradientSource.adjointAccuracy b ε) ε : ℝ) ≤
    constant b*((1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2)+(2*k+2:ℕ)*Real.log (2/ε)+Real.log (2+D/ε)) := by
  have hC : 0 < 32*innerSensitivity b := mul_pos (by norm_num) (innerSensitivity_pos b)
  have hL : 0 < 32*b.L₁ := mul_pos (by norm_num) b.L₁_pos
  have hi := InnerSource.sample_budget (b := b) hgap hD hC hε hε1 hεC
  have ha := AdjointSource.sample_budget b hgap.le k hh hL hε hε1 hεL
  have ho := final_budget b k hh hε hε1
  have hci := (InnerSource.costConstant_pos b hgap (32*innerSensitivity b)).le
  have hca := (AdjointSource.costConstant_pos b hgap.le (32*b.L₁)).le
  have hco := (finalConstant_pos b).le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  have hI : 0 ≤ (2*k+2:ℕ)*Real.log (2/ε) := mul_nonneg (by positivity) hlog
  have hDlog : 0 ≤ Real.log (2+D/ε) := Real.log_nonneg (by
    have : 0 ≤ D/ε := by positivity
    linarith)
  have hW : 1/ε ^ 2 ≤ (1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2) := by
    have := mul_nonneg (sq_nonneg ((2*k+1:ℕ)/h)) (by positivity : 0 ≤ 1/ε ^ 2)
    nlinarith
  have hi' := hi.trans (mul_le_mul_of_nonneg_left (show 1/ε ^ 2+Real.log (2+D/ε) ≤
    (1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2)+(2*k+2:ℕ)*Real.log (2/ε)+Real.log (2+D/ε) by linarith) hci)
  have ha' := ha.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hDlog) hca)
  have ho' := ho.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hDlog) hco)
  calc
    _ = (InnerPopulation.samples b D (ε/(32*innerSensitivity b)):ℝ)+
      (AdjointSolve.samples b k h (ε/(32*b.L₁)):ℝ)+
      (AdjointSolve.stepSamples k h (outputBatch b ((2*k+1:ℕ)/h) ε):ℝ) := by
        simp only [HypergradientSolve.samples,HypergradientSource.innerAccuracy,
          HypergradientSource.adjointAccuracy,Nat.cast_add]
    _ ≤ _ := (add_le_add (add_le_add hi' ha') ho').trans_eq (by unfold constant; ring)

end Smoothness2601.HypergradientCost
