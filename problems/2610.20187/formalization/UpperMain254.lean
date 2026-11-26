import GlobalCurved254
import AdaptiveGradient254

noncomputable section
namespace Paper254

theorem logarithmic_overhead_absorbed (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (η : ℝ) (hη : 0 < η) : logFactor T/η ≤ (1/η)*((d : ℝ)*logFactor T^2) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL := logFactor_ge_one T hT
  have hs : logFactor T ≤ (d : ℝ)*logFactor T^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ)-1 by linarith) (sq_nonneg (logFactor T))]
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1/η by positivity)
  convert hh using 1 <;> ring

theorem binary_overhead (T : ℕ) (hT : 0 < T) (η : ℝ) (hη : 0 < η)
    (j : Fin 2) : -Real.log ((uniformWeights 1).weight j)/η ≤ logFactor T/η := by
  rw [uniform_log_overhead]
  apply div_le_div_of_nonneg_right _ hη.le
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ 2*T by linarith)
  norm_num only [Nat.cast_one] at *
  unfold logFactor
  norm_num only [one_add_one_eq_two]
  linarith

theorem main_upper : MainUpperStatement := by
  intro D G η hD hG hη
  obtain ⟨C,hC,hcurved⟩ := global_curved_learner D G η hD hG hη
  let H := D^2+2*D+G^2+G*D*(1+D)
  let e := 1/η
  let K := C+H+G*D+2*e
  have hH : 0 < H := by dsimp [H]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro d T hd hT W
  obtain ⟨A,hA⟩ := hcurved d T hd hT W
  obtain ⟨w,hw⟩ := W.nonempty
  let w0 : W.carrier := ⟨w,hw⟩
  let B : OnlineLearner W T := adaptiveGradient W G η w0
  let experts : Fin 2 → OnlineLearner W T := fun j => if j.val = 0 then A else B
  let learner := aggregateOnline (uniformWeights 1) η w0 experts
  refine ⟨learner,?_⟩
  intro f hf u
  let S := (d : ℝ)*logFactor T^2
  let Q := curvedRate d T (pathLength u)
  let R := Real.sqrt ((T : ℝ)*(1+pathLength u))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hQ : 0 ≤ Q := curvedRate_nonneg d T _ (pathLength_nonneg u)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hE : logFactor T/η ≤ e*S := logarithmic_overhead_absorbed d T hd hT η hη
  have hm0 := aggregateOnline_regret (uniformWeights 1) hη w0 experts f hf u (0 : Fin 2) (by norm_num [uniformWeights])
  have hm1 := aggregateOnline_regret (uniformWeights 1) hη w0 experts f hf u (1 : Fin 2) (by norm_num [uniformWeights])
  have ho0 := binary_overhead T hT η hη (0 : Fin 2)
  have ho1 := binary_overhead T hT η hη (1 : Fin 2)
  have hb0 := hA f hf u
  have hb1 := adaptiveGradient_bound W hD hG hη hT w0 f hf u
  change regret learner f u ≤ regret A f u-Real.log ((uniformWeights 1).weight 0)/η at hm0
  change regret learner f u ≤ regret B f u-Real.log ((uniformWeights 1).weight 1)/η at hm1
  rw [sub_eq_add_neg, ← neg_div] at hm0 hm1
  change regret A f u ≤ C*(S+Q) at hb0
  change regret B f u ≤ H*R+logFactor T/η at hb1
  have hKC : C+e ≤ K := by dsimp [K]; linarith [mul_pos hG hD]
  have hKH : H ≤ K := by dsimp [K]; linarith [mul_pos hG hD]
  have hKe : 2*e ≤ K := by dsimp [K]; linarith [mul_pos hG hD]
  have hKG : G*D ≤ K := by dsimp [K]; linarith
  have hqbound : regret learner f u ≤ K*(S+Q) := by
    have hs := mul_le_mul_of_nonneg_right hKC hS
    have hq := mul_le_mul_of_nonneg_right (show C ≤ K by linarith) hQ
    nlinarith
  have hrbound : regret learner f u ≤ K*(S+R) := by
    have hs := mul_le_mul_of_nonneg_right hKe hS
    have hr := mul_le_mul_of_nonneg_right hKH hR
    nlinarith
  have htbound : regret learner f u ≤ K*(S+T) := by
    have hh := linear_regret_bound learner f u hG.le hf
    have ht := mul_le_mul_of_nonneg_right hKG hTr
    nlinarith [mul_nonneg hK.le hS]
  change regret learner f u ≤ K*(S+min Q (min R T))
  by_cases hq : Q ≤ min R T
  · rwa [min_eq_left hq]
  · rw [min_eq_right (le_of_not_ge hq)]
    by_cases hr : R ≤ T
    · rwa [min_eq_left hr]
    · rwa [min_eq_right (le_of_not_ge hr)]

end Paper254
#print axioms Paper254.main_upper
