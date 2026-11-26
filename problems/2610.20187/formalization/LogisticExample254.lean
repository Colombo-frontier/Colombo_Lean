import BackgroundExamples254

noncomputable section
open Set
namespace Paper254

def logisticLoss (x : ℝ) := Real.log (1+Real.exp (-x))
def logisticFirst (x : ℝ) := -Real.exp (-x)/(1+Real.exp (-x))
def logisticSecond (x : ℝ) := Real.exp (-x)/(1+Real.exp (-x))^2

theorem logistic_first (x : ℝ) : HasDerivAt logisticLoss (logisticFirst x) x := by
  have hd := ((hasDerivAt_id x).neg.exp).const_add 1
  convert hd.log (show 1+Real.exp (-x) ≠ 0 by positivity) using 1 <;>
    simp [logisticLoss,logisticFirst]

theorem logistic_second (x : ℝ) : HasDerivAt logisticFirst (logisticSecond x) x := by
  have he := (hasDerivAt_id x).neg.exp
  convert he.neg.div (he.const_add 1) (show 1+Real.exp (-x) ≠ 0 by positivity) using 1
  dsimp [logisticSecond]
  ring

theorem logistic_expConcave (B : ℝ) :
    ConcaveOn ℝ (Icc (-B) B) (fun x => Real.exp (-Real.exp (-B)*logisticLoss x)) := by
  apply scalar_expConcave_of_second (convex_Icc _ _) logisticLoss logisticFirst logisticSecond
    (Real.exp (-B)) (Real.exp_pos _).le logistic_first logistic_second
  intro x hx
  have hm : Real.exp (-B)*Real.exp (-x) ≤ 1 := by
    rw [← Real.exp_add,Real.exp_le_one_iff]
    linarith [hx.1]
  have hb := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-x)).le
  dsimp [logisticFirst,logisticSecond]
  rw [div_pow]
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith only [hb]

theorem logistic_gradient_bound (x : ℝ) : |logisticFirst x| ≤ 1 := by
  have he := Real.exp_pos (-x)
  rw [logisticFirst,abs_div,abs_neg,abs_of_pos he,abs_of_pos (by positivity : 0 < 1+Real.exp (-x))]
  exact (div_le_one (by positivity)).mpr (by linarith)

end Paper254
#print axioms Paper254.logistic_expConcave
