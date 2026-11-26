import SparseOnlineBound254
import Mathlib.Data.Nat.Find

noncomputable section
namespace Paper254

def scaleCount (T : ℕ) : ℕ := Nat.log 2 T
def dyadicScale (D : ℝ) (k : ℕ) : ℝ := D/(2 : ℝ)^k
def dyadicVariance (D : ℝ) (T : ℕ) (k : Fin (scaleCount T+1)) : ℝ := (dyadicScale D k.val)^2

theorem dyadicScale_pos (D : ℝ) (hD : 0 < D) (k : ℕ) : 0 < dyadicScale D k := by
  unfold dyadicScale
  positivity

theorem dyadicVariance_pos (D : ℝ) (hD : 0 < D) (T : ℕ) (k : Fin (scaleCount T+1)) :
    0 < dyadicVariance D T k := sq_pos_of_pos (dyadicScale_pos D hD k.val)

theorem two_pow_ge_one (k : ℕ) : (1 : ℝ) ≤ 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; nlinarith

theorem dyadicScale_range (D : ℝ) (hD : 0 < D) (T : ℕ) (hT : 0 < T)
    (k : Fin (scaleCount T+1)) : D/T ≤ dyadicScale D k.val ∧ dyadicScale D k.val ≤ D := by
  have hk : k.val ≤ Nat.log 2 T := by have hh := k.isLt; dsimp [scaleCount] at hh; omega
  have hp : (2 : ℝ)^k.val ≤ T := by
    exact_mod_cast (Nat.pow_le_of_le_log (ne_of_gt hT) hk)
  have hpow : (0 : ℝ) < 2^k.val := by positivity
  constructor
  · exact div_le_div_of_nonneg_left hD.le hpow hp
  · unfold dyadicScale
    exact (div_le_iff₀ hpow).mpr (by nlinarith [two_pow_ge_one k.val])

theorem dyadicScale_last (D : ℝ) (hD : 0 < D) (T : ℕ) (hT : 0 < T) :
    dyadicScale D (scaleCount T) ≤ 2*(D/T) := by
  have hp : (T : ℝ) < 2*(2 : ℝ)^(scaleCount T) := by
    have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) T
    have hh' : (T : ℝ) < (2 : ℝ)^(Nat.log 2 T+1) := by exact_mod_cast hh
    simpa only [scaleCount, pow_succ, mul_comm] using hh'
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hpow : (0 : ℝ) < 2^(scaleCount T) := by positivity
  unfold dyadicScale
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hpow hTr).mpr
  nlinarith

theorem dyadicScale_succ (D : ℝ) (k : ℕ) : dyadicScale D k = 2*dyadicScale D (k+1) := by
  unfold dyadicScale
  rw [pow_succ]
  field_simp

/-- The actual logarithmic grid approximates every admissible smoothing
scale, including the lower endpoint D/T, without knowing path length. -/
theorem dyadic_scale_approx (D : ℝ) (hD : 0 < D) (T : ℕ) (hT : 0 < T)
    (τ : ℝ) (hlo : D/T ≤ τ) (hhi : τ ≤ D) :
    ∃ k : Fin (scaleCount T+1), τ ≤ dyadicScale D k.val ∧ dyadicScale D k.val ≤ 2*τ := by
  classical
  let P := fun k => τ ≤ dyadicScale D k
  let k := Nat.findGreatest P (scaleCount T)
  have hk : k ≤ scaleCount T := Nat.findGreatest_le _
  have hp0 : P 0 := by simpa [P, dyadicScale] using hhi
  have hlow : τ ≤ dyadicScale D k := Nat.findGreatest_spec (Nat.zero_le _) hp0
  refine ⟨⟨k, by omega⟩, hlow, ?_⟩
  change dyadicScale D k ≤ 2*τ
  by_cases hlast : k = scaleCount T
  · rw [hlast]
    exact le_trans (dyadicScale_last D hD T hT) (by linarith)
  · have hkplus : k+1 ≤ scaleCount T := by omega
    have hnot : ¬ P (k+1) := by
      intro hh
      have hmax := Nat.le_findGreatest hkplus hh
      change k+1 ≤ k at hmax
      omega
    have hn : dyadicScale D (k+1) < τ := lt_of_not_ge hnot
    rw [dyadicScale_succ D k]
    linarith

end Paper254
#print axioms Paper254.dyadic_scale_approx
