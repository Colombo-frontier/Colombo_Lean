import SampleReuse.OracleBatchSize
import SampleReuse.ComplexityRates
import SampleReuse.CurvatureFirstTermination
import Mathlib.Analysis.SpecialFunctions.Log.Base

open SecondOrder

namespace SampleReuse
noncomputable section

/-- A numerical universal constant, shared by the logarithm and both budgets. -/
def sourceUpperConstant : ℝ := 2097152

def sourceLogScale (d T : ℕ) : ℝ :=
  1 + Real.log (sourceUpperConstant * (d + 1) * (T + 1))

def sourceConfidenceScale (d T : ℕ) (η : ℝ) : ℝ :=
  confidenceBatchScale d ((η / 4) / (binaryDepth T + 1)) ((1 / 96) / (T + 1))

def sourceIterationCap (P : Parameters) (ε γ : ℝ) : ℕ :=
  1 + ⌈48 * P.gap * (32 * P.gradientLip / (3 * ε^2) +
    12 * P.hessianLip^2 / γ^3)⌉₊

theorem sourceUpperConstant_pos : 0 < sourceUpperConstant := by norm_num [sourceUpperConstant]

theorem sourceLogScale_one_le (d T : ℕ) : 1 ≤ sourceLogScale d T := by
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have ht : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hx : 1 ≤ sourceUpperConstant * (d+1) * (T+1) := by
    dsimp [sourceUpperConstant]
    nlinarith [mul_nonneg hd ht]
  exact le_add_of_nonneg_right (Real.log_nonneg hx)

theorem binaryDepth_log_bound (d T : ℕ) :
    (binaryDepth T : ℝ) + 1 ≤ 2 * sourceLogScale d T := by
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    linarith
  have ht : Real.log T ≤ Real.log (T+1:ℝ) := by
    by_cases hz : T = 0
    · subst T; simp
    · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)) (by norm_num)
  have hn := Real.natLog_le_logb T 2
  simp only [Real.logb, Nat.cast_ofNat] at hn
  have hn' : (Nat.log 2 T:ℝ) * Real.log 2 ≤ Real.log T :=
    (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mp hn
  have hprod : (T+1:ℝ) ≤ sourceUpperConstant * (d+1) * (T+1) := by
    have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
    have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
    dsimp [sourceUpperConstant]
    nlinarith [mul_nonneg hd hT]
  have hl := Real.log_le_log (by positivity : (0:ℝ)<T+1) hprod
  have hh := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (Nat.log 2 T) : (0:ℝ)≤_)
  simp only [binaryDepth, Nat.cast_add, Nat.cast_one, sourceLogScale]
  linarith

theorem matrixMomentOrder_log_bound (d T : ℕ) :
    (matrixMomentOrder (d+1) ((1/96)/(T+1:ℝ)):ℝ) ≤ 2*sourceLogScale d T := by
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    linarith
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have ht : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have he : ((d+1:ℕ):ℝ) / ((1/96)/(T+1:ℝ)) = 96*(d+1)*(T+1) := by
    push_cast
    field_simp
    all_goals ring
  have hX : 1 ≤ 96*(d+1:ℝ)*(T+1) := by nlinarith [mul_nonneg hd ht]
  have hl0 : 0 ≤ Real.log (((d+1:ℕ):ℝ)/((1/96)/(T+1:ℝ))) := by
    rw [he]; exact Real.log_nonneg hX
  have hc := (Nat.ceil_lt_add_one (div_nonneg hl0 (by positivity : (0:ℝ)≤Real.log 2))).le
  have hratio : Real.log (((d+1:ℕ):ℝ)/((1/96)/(T+1:ℝ))) / Real.log 2 ≤
      2*Real.log (sourceUpperConstant*(d+1)*(T+1)) := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    have hcmp : 96*(d+1:ℝ)*(T+1) ≤ sourceUpperConstant*(d+1)*(T+1) := by
      dsimp [sourceUpperConstant]
      nlinarith [mul_nonneg hd ht]
    have hl := Real.log_le_log (by positivity : (0:ℝ)<96*(d+1)*(T+1)) hcmp
    have hz := Real.log_nonneg ((show (1:ℝ)≤96*(d+1)*(T+1) from hX).trans hcmp)
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left htwo hz]
  push_cast at hc hratio
  simp only [matrixMomentOrder, Nat.cast_add, Nat.cast_one, sourceLogScale]
  linarith

theorem sourceConfidenceScale_bound (d T : ℕ) {η : ℝ} (hη : 0 < η) :
    sourceConfidenceScale d T η ≤ 16384*(sourceLogScale d T)^3/η^2 := by
  have hk := matrixMomentOrder_log_bound d T
  have hb := binaryDepth_log_bound d T
  have hL := sourceLogScale_one_le d T
  have hb0 : (0:ℝ) ≤ (binaryDepth T:ℝ)+1 := by positivity
  have hk0 : (0:ℝ) ≤ (matrixMomentOrder (d+1) ((1/96)/(T+1:ℝ)):ℝ) := by positivity
  have hp := mul_le_mul hk (pow_le_pow_left₀ hb0 hb 2) (sq_nonneg _) (by linarith : 0≤2*sourceLogScale d T)
  have he : sourceConfidenceScale d T η =
      2048*(matrixMomentOrder (d+1) ((1/96)/(T+1:ℝ)):ℝ)*((binaryDepth T:ℝ)+1)^2/η^2 := by
    unfold sourceConfidenceScale confidenceBatchScale
    field_simp
    all_goals ring
  rw [he]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hη)).mpr
  nlinarith

theorem sourceIterationCap_pos (P : Parameters) (ε γ : ℝ) : 0 < sourceIterationCap P ε γ := by
  unfold sourceIterationCap
  omega

theorem sourceIterationCap_exhaustion (P : Parameters) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) :
    P.gap / (optimizerMinDecrease P ε γ * sourceIterationCap P ε γ) ≤ 1/48 := by
  have hg := P.gradientLip_pos
  have hh := P.hessianLip_pos
  have hp := P.gap_pos
  have hm := optimizerMinDecrease_pos P hε hγ
  have hc := Nat.le_ceil (48*P.gap*(32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3))
  have hcap : 48*P.gap*(32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3) ≤
      (sourceIterationCap P ε γ:ℝ) := by
    unfold sourceIterationCap
    push_cast
    linarith
  have hrec : 1 ≤ optimizerMinDecrease P ε γ *
      (32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3) := by
    unfold optimizerMinDecrease
    rcases le_total (3*ε^2/(32*P.gradientLip)) (γ^3/(12*P.hessianLip^2)) with h|h
    · rw [min_eq_left h]
      have he : (3*ε^2/(32*P.gradientLip))*(32*P.gradientLip/(3*ε^2)) = 1 := by field_simp
      have hn : 0 ≤ (3*ε^2/(32*P.gradientLip))*(12*P.hessianLip^2/γ^3) := by positivity
      nlinarith
    · rw [min_eq_right h]
      have he : (γ^3/(12*P.hessianLip^2))*(12*P.hessianLip^2/γ^3) = 1 := by field_simp
      have hn : 0 ≤ (γ^3/(12*P.hessianLip^2))*(32*P.gradientLip/(3*ε^2)) := by positivity
      nlinarith
  have hb := mul_le_mul_of_nonneg_left hcap hm.le
  have hrec' := mul_le_mul_of_nonneg_left hrec (by positivity : (0:ℝ)≤48*P.gap)
  apply (div_le_iff₀ (mul_pos hm (Nat.cast_pos.mpr (sourceIterationCap_pos P ε γ)))).mpr
  nlinarith

end
end SampleReuse

