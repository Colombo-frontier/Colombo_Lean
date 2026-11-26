import ExactValue.SCPhases
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Complex.ExponentialBounds

set_option autoImplicit false
namespace ExactValue
noncomputable section

def logPlus (x : ℝ) : ℝ := max 0 (Real.log x)
def scCertifiedGap (μ R : ℝ) (s : ℕ) : ℝ := (μ * R ^ 2 / 32) / (2 : ℝ) ^ s
def scRestartCount (μ R ε : ℝ) : ℕ := ⌈max 0 (Real.logb 2 ((μ * R ^ 2 / 32) / ε))⌉₊

theorem scCertifiedGap_pos {μ R : ℝ} (hμ : 0 < μ) (hR : 0 < R) (s : ℕ) :
    0 < scCertifiedGap μ R s := by unfold scCertifiedGap; positivity

theorem scCertifiedGap_le_initial {μ R : ℝ} (hμ : 0 < μ) (hR : 0 < R) (s : ℕ) :
    scCertifiedGap μ R s ≤ μ * R ^ 2 / 32 := by
  apply div_le_self (by positivity)
  exact one_le_pow₀ (by norm_num)

theorem scCertifiedGap_succ (μ R : ℝ) (s : ℕ) :
    scCertifiedGap μ R (s + 1) = scCertifiedGap μ R s / 2 := by
  simp only [scCertifiedGap, pow_succ, div_mul_eq_div_div]

theorem scRestartCount_accuracy {μ R ε : ℝ} (hμ : 0 < μ) (hR : 0 < R) (hε : 0 < ε) :
    scCertifiedGap μ R (scRestartCount μ R ε) ≤ ε := by
  have hz : 0 < (μ * R ^ 2 / 32) / ε := by positivity
  have hceil : Real.logb 2 ((μ * R ^ 2 / 32) / ε) ≤ (scRestartCount μ R ε : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hp := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hz).mp hceil
  rw [Real.rpow_natCast] at hp
  have hm := (div_le_iff₀ hε).mp hp
  unfold scCertifiedGap
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem scRestartCount_bound {μ R ε : ℝ} (hμ : 0 < μ) (hR : 0 < R) (hε : 0 < ε) :
    (scRestartCount μ R ε : ℝ) + 1 ≤ 2 * (1 + logPlus (μ * R ^ 2 / ε)) := by
  let z := μ * R ^ 2 / ε
  have hz : 0 < z := by dsimp [z]; positivity
  have hlog2 : 1 / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog2p : 0 < Real.log 2 := by linarith
  have hnonneg : 0 ≤ logPlus z := le_max_left _ _
  have hlog : Real.log z ≤ logPlus z := le_max_right _ _
  have hsmall : (μ * R ^ 2 / 32) / ε ≤ z := by
    have heq : (μ * R ^ 2 / 32) / ε = z / 32 := by dsimp [z]; ring
    rw [heq]
    linarith
  have hl := Real.log_le_log (show 0 < (μ * R ^ 2 / 32) / ε by positivity) hsmall
  have hbase : Real.logb 2 ((μ * R ^ 2 / 32) / ε) ≤ 2 * logPlus z := by
    unfold Real.logb
    apply (div_le_iff₀ hlog2p).mpr
    have hm := mul_le_mul_of_nonneg_right hlog2.le hnonneg
    nlinarith
  have hmax : max 0 (Real.logb 2 ((μ * R ^ 2 / 32) / ε)) ≤ 2 * logPlus z :=
    max_le (by positivity) hbase
  have hc : (scRestartCount μ R ε : ℝ) < max 0 (Real.logb 2 ((μ * R ^ 2 / 32) / ε)) + 1 :=
    Nat.ceil_lt_add_one (le_max_left _ _)
  change (scRestartCount μ R ε : ℝ) + 1 ≤ 2 * (1 + logPlus z)
  linarith

theorem sc_restarted_call_count {d : ℕ} (hd : 0 < d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε) :
    (((d + 1) * scPhaseLength μ β * (scRestartCount μ R ε + 1) : ℕ) : ℝ) ≤
      36 * d * Real.sqrt (β / μ) * (1 + logPlus (μ * R ^ 2 / ε)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hK := (scPhaseLength_bounds hμ hμβ).2.2
  have hS := scRestartCount_bound hμ hR hε
  have hLP : 0 ≤ 1 + logPlus (μ * R ^ 2 / ε) := by
    have := le_max_left (0 : ℝ) (Real.log (μ * R ^ 2 / ε))
    dsimp [logPlus]
    linarith
  push_cast
  calc
    _ ≤ (2 * d) * (9 * Real.sqrt (β / μ)) * (2 * (1 + logPlus (μ * R ^ 2 / ε))) := by
      apply mul_le_mul _ hS (by positivity) (by positivity)
      exact mul_le_mul (by linarith) hK (by positivity) (by positivity)
    _ = _ := by ring

end
end ExactValue
