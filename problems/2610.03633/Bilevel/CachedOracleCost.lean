import Bilevel.StatefulAcceleratedSolver
import Bilevel.FreshBatchKernel

/-! Explicit arithmetic bounds for the exact natural call counts used by the
cached implementation. The initialization logarithm is shared by all solves;
the variance term is not multiplied by that logarithm. -/
noncomputable section
namespace Bilevel.CachedOracleCost
open AcceleratedInner StatefulAccelerated

def initializationLog (μ M R a : ℝ) : ℝ :=
  1 + Real.log (2+576*M*R^2/(μ*a^2))/Real.log 2

theorem initializationLog_nonneg {μ M R a : ℝ} (hμ : 0 < μ) (hM : 0 ≤ M) :
    0 ≤ initializationLog μ M R a := by
  have hx : 0 ≤ 576*M*R^2/(μ*a^2) := by positivity
  have hl : 0 ≤ Real.log (2+576*M*R^2/(μ*a^2)) := Real.log_nonneg (by linarith)
  unfold initializationLog
  positivity

theorem solve_cost {μ M α σ R a r : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hα : 0 < α) (hα1 : α ≤ 1) (hrel : α^2*M = μ)
    (ha : 0 < a) (har : a ≤ r) :
    (solveCalls μ M α σ R (r/12) : ℝ) ≤
      2*(Real.log 4+1)*initializationLog μ M R a/α +
        4608*(Real.log 4+1)*σ^2/(μ^2*r^2) := by
  have hr : 0 < r := ha.trans_le har
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  by_cases hRr : R ≤ r/12
  · simp only [solveCalls, if_pos hRr, Nat.cast_zero]
    have hi := initializationLog_nonneg (R := R) (a := a) hμ hM.le
    positivity
  · have hRr' : r/12 < R := lt_of_not_ge hRr
    have hR : 0 < R := (by positivity : 0 < r/12).trans hRr'
    have hb := solveCalls_bound (σ := σ) hM hμ hμM hα hα1 hrel
      (by positivity : 0 < r/12) hRr'
    have hT : 0 < μ*(r/12)^2/4 := by positivity
    have hTU : μ*(r/12)^2/4 < M*R^2 := by
      have hs : (r/12)^2 < R^2 := by nlinarith
      have hm := mul_lt_mul_of_pos_left hs hM
      have hn := mul_le_mul_of_nonneg_right hμM (sq_nonneg (r/12))
      nlinarith
    have hstage := (dyadicStageCount_bounds hT hTU).2.2
    have hratio : M*R^2/(μ*(r/12)^2/4) = 576*M*R^2/(μ*r^2) := by field_simp; ring
    have hsquare : a^2 ≤ r^2 := by nlinarith
    have hd : 576*M*R^2/(μ*r^2) ≤ 576*M*R^2/(μ*a^2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hsquare hμ.le)
    have hlog : Real.log (M*R^2/(μ*(r/12)^2/4)) ≤
        Real.log (2+576*M*R^2/(μ*a^2)) := by
      rw [hratio]
      apply Real.log_le_log (by positivity)
      linarith
    have hS : (dyadicStageCount (M*R^2) (μ*(r/12)^2/4) : ℝ) ≤
        initializationLog μ M R a := by
      have hh := div_le_div_of_nonneg_right hlog
        (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
      unfold initializationLog
      linarith
    have hdet := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 2*(Real.log 4+1))) hα.le
    have hnoise : 32*(Real.log 4+1)*σ^2/(μ^2*(r/12)^2) =
        4608*(Real.log 4+1)*σ^2/(μ^2*r^2) := by field_simp; ring
    rw [hnoise] at hb
    exact hb.trans (add_le_add_right hdet _)

theorem batch_cost (σ r : ℝ) :
    (FreshBatchKernel.count σ (r/12) : ℝ) ≤ 1+144*σ^2/r^2 := by
  have hh := FreshBatchKernel.count_le σ (r/12)
  convert hh using 1
  field_simp
  ring

/-- The implementation uses a separate anchor solve. Its deterministic
overhead is absorbed using M <= N; its variance is paid only M times. -/
theorem aggregate_cost {N M q S SA Bg Bf : ℕ} {d v vA bg bf : ℝ}
    (hMN : M ≤ N) (hd : 0 ≤ d)
    (hS : (S:ℝ) ≤ d+v) (hSA : (SA:ℝ) ≤ d+vA)
    (hBg : (Bg:ℝ) ≤ bg) (hBf : (Bf:ℝ) ≤ bf) :
    ((q*(2*N*S+M*SA+2*N*Bg+M*Bf) : ℕ):ℝ) ≤
      q*(3*N*d+2*N*v+M*vA+2*N*bg+M*bf) := by
  have hMN' : (M:ℝ) ≤ N := by exact_mod_cast hMN
  have hm := mul_le_mul_of_nonneg_right hMN' hd
  have hs := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ (2*N:ℝ))
  have hsa := mul_le_mul_of_nonneg_left hSA (by positivity : 0 ≤ (M:ℝ))
  have hbg := mul_le_mul_of_nonneg_left hBg (by positivity : 0 ≤ (2*N:ℝ))
  have hbf := mul_le_mul_of_nonneg_left hBf (by positivity : 0 ≤ (M:ℝ))
  push_cast
  exact mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg q)

end Bilevel.CachedOracleCost
