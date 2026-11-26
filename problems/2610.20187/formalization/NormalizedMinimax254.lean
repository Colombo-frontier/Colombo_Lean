import UpperMain254
import LowerMain254
import HardCurvature254

noncomputable section
namespace Paper254

theorem curved_log_comparison (d T : ℕ) (hT : 0 < T) (P : ℝ) (hP : 0 ≤ P) :
    curvedRate d T P ≤ logFactor T^2 * unloggedRate d T P := by
  have hL := logFactor_ge_one T hT
  have hh := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (4/3 : ℝ) ≤ 2)
  rw [Real.rpow_two] at hh
  have hm := mul_le_mul_of_nonneg_right hh (unloggedRate_nonneg d T P hP)
  convert hm using 1 <;> dsimp [curvedRate,unloggedRate] <;> ring

theorem small_path_rate_comparison (d T : ℕ) (P : ℝ) (hP : 0 ≤ P) (hP1 : P ≤ 1) :
    unloggedRate d T P ≤ (d : ℝ) + Real.sqrt ((T : ℝ)*P) := by
  let s := Real.sqrt ((T : ℝ)*P)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = (T : ℝ)*P := Real.sq_sqrt (by positivity)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hp2 : P^2 ≤ P := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ (d : ℝ)*T by positivity)
  have hc := unloggedRate_cube d T P hP
  have hc' : (unloggedRate d T P)^3 ≤ (d : ℝ)*s^2 := by nlinarith only [hc,hh,hs2]
  have hsum : (d : ℝ)*s^2 ≤ ((d : ℝ)+s)^3 := by
    nlinarith [mul_nonneg hd (sq_nonneg s),mul_nonneg (sq_nonneg (d : ℝ)) hs,
      pow_nonneg hd 3,pow_nonneg hs 3]
  exact nonneg_le_of_cube_le _ _ (unloggedRate_nonneg d T P hP) (by positivity) (hc'.trans hsum)

/-- Explicit logarithmic comparison between the displayed upper and lower
frontiers, including P=0 and the small-horizon regime. -/
theorem normalized_frontier_comparison (d T : ℕ) (hT : 0 < T) (P : ℝ) (hP : 0 ≤ P) :
    upperFrontier d T P ≤ 2*logFactor T^2*normalizedFrontier d T P := by
  let L := logFactor T^2
  let Q := unloggedRate d T P
  let s := Real.sqrt ((T : ℝ)*P)
  let r := Real.sqrt ((T : ℝ)*(1+P))
  have hL1 : 1 ≤ L := by dsimp [L]; nlinarith [logFactor_ge_one T hT]
  have hL : 0 ≤ L := by positivity
  have hQ : 0 ≤ Q := unloggedRate_nonneg d T P hP
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hq := curved_log_comparison d T hT P hP
  change curvedRate d T P ≤ L*Q at hq
  have hminq : min (curvedRate d T P) (min r T) ≤ L*Q := (min_le_left _ _).trans hq
  have hmins : min (curvedRate d T P) (min r T) ≤ L*((d : ℝ)+2*s) := by
    by_cases hP1 : P ≤ 1
    · have hh := small_path_rate_comparison d T P hP hP1
      change Q ≤ (d : ℝ)+s at hh
      have hm := mul_le_mul_of_nonneg_left hh hL
      nlinarith [mul_nonneg hL hs]
    · have hP1' : 1 ≤ P := le_of_not_ge hP1
      have hs2 : s^2 = (T : ℝ)*P := Real.sq_sqrt (by positivity)
      have hr2 : r^2 = (T : ℝ)*(1+P) := Real.sq_sqrt (by positivity)
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have htp := mul_le_mul_of_nonneg_left hP1' hT0
      have hrs : r ≤ 2*s := by nlinarith
      have hm : min (curvedRate d T P) (min r T) ≤ r := (min_le_right _ _).trans (min_le_left _ _)
      nlinarith [mul_nonneg (show 0 ≤ L-1 by linarith) hs,mul_nonneg hL hd]
  have hmT : min (curvedRate d T P) (min r T) ≤ T := (min_le_right _ _).trans (min_le_right _ _)
  change (d : ℝ)*L+min (curvedRate d T P) (min r T) ≤ 2*L*((d : ℝ)+min Q (min s T))
  by_cases hfirst : Q ≤ min s T
  · rw [min_eq_left hfirst]
    nlinarith [mul_nonneg hL hd,mul_nonneg hL hQ]
  · rw [min_eq_right (le_of_not_ge hfirst)]
    by_cases hsecond : s ≤ T
    · rw [min_eq_left hsecond]
      nlinarith
    · rw [min_eq_right (le_of_not_ge hsecond)]
      nlinarith [mul_nonneg (show 0 ≤ L-1 by linarith) hT0,mul_nonneg hL hd]

theorem normalized_upper :
    ∀ D G η : ℝ, 0 < D → 0 < G → 0 < η →
    ∃ C : ℝ, 0 < C ∧
    ∀ d T : ℕ, 0 < d → 0 < T → ∀ W : Domain d D,
    ∃ A : OnlineLearner W T,
    ∀ f : Fin T → Loss d, (∀ t, AdmissibleLoss W G η (f t)) →
    ∀ u : Fin T → W.carrier,
      regret A f u ≤ C*logFactor T^2*normalizedFrontier d T (pathLength u) := by
  intro D G η hD hG hη
  obtain ⟨C,hC,h⟩ := main_upper D G η hD hG hη
  refine ⟨2*C,by positivity,?_⟩
  intro d T hd hT W
  obtain ⟨A,hA⟩ := h d T hd hT W
  refine ⟨A,?_⟩
  intro f hf u
  have hh := mul_le_mul_of_nonneg_left
    (normalized_frontier_comparison d T hT (pathLength u) (pathLength_nonneg u)) hC.le
  have hr := hA f hf u
  nlinarith

end Paper254
#print axioms Paper254.normalized_upper
