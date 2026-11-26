import NCConcave16991.BranchOracleSchedule
import NCConcave16991.BranchOracleBudgetBinomial
import Mathlib.Algebra.Order.Floor.Ring

/-! # The public branch budget bounds the actual terminal word mass -/

noncomputable section

namespace NCConcave16991.BranchOracleBudget

set_option maxHeartbeats 700000

def budget (n ρ : ℝ) (H : ℕ) : ℕ := ⌊ρ ^ 2 * n * H / (4 * Real.exp 1)⌋₊

theorem accountingBound_le_quarter (n ρ : ℝ) (hn : 0 < n) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (K r H : ℕ) (hH : 0 < H) (hrH : r ≤ H)
    (hK : (K : ℝ) ≤ ρ ^ 2 * n * H / (4 * Real.exp 1)) :
    BranchAccounting.accountingBound n ρ K r H ≤ ρ / 4 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase : Real.exp 1 * K / H ≤ ρ ^ 2 * n / 4 := by
    apply (div_le_iff₀ hHR).mpr
    have hh := mul_le_mul_of_nonneg_left hK he.le
    have hi : Real.exp 1 * (ρ ^ 2 * n * H / (4 * Real.exp 1)) = (ρ ^ 2 * n / 4) * H := by
      field_simp
    exact hi ▸ hh
  have hchoose : (K.choose H : ℝ) ≤ (ρ ^ 2 * n / 4) ^ H :=
    (choose_le_exp_pow K H hH).trans (pow_le_pow_left₀ (by positivity) hbase H)
  have hp : ρ ^ H ≤ ρ ^ r := pow_le_pow_of_le_one hρ.le hρ1 hrH
  have hden : n ^ H * ρ ^ H ≤ n ^ H * ρ ^ r := mul_le_mul_of_nonneg_left hp (pow_nonneg hn.le H)
  calc
    BranchAccounting.accountingBound n ρ K r H = (K.choose H : ℝ) / (n ^ H * ρ ^ r) := rfl
    _ ≤ (K.choose H : ℝ) / (n ^ H * ρ ^ H) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ (ρ ^ 2 * n / 4) ^ H / (n ^ H * ρ ^ H) :=
      div_le_div_of_nonneg_right hchoose (by positivity)
    _ = (ρ / 4) ^ H := by
      rw [← mul_pow,← div_pow]
      congr 1
      field_simp
    _ ≤ ρ / 4 := pow_le_of_le_one (by positivity) (by linarith) hH.ne'

theorem accountingBound_le_quarter_of_budget (n ρ : ℝ) (hn : 0 < n)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (K r M H : ℕ) (hH : 0 < H)
    (hrM : r ≤ M) (hMH : M ≤ H) (hK : K ≤ budget n ρ H) :
    BranchAccounting.accountingBound n ρ K r H ≤ ρ / 4 := by
  apply accountingBound_le_quarter n ρ hn hρ hρ1 K r H hH (hrM.trans hMH)
  have hnonneg : 0 ≤ ρ ^ 2 * n * H / (4 * Real.exp 1) := by positivity
  exact (show (K : ℝ) ≤ (budget n ρ H : ℝ) by exact_mod_cast hK).trans (Nat.floor_le hnonneg)

end NCConcave16991.BranchOracleBudget

namespace NCConcave16991.BranchOracle.WordProfile

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem ScheduledRun.terminal_mass_le_quarter {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K r : ℕ} {p : WordProfile ι} (run : ScheduledRun ρ K r p)
    (M H : ℕ) (hH : 0 < H) (hrM : r ≤ M) (hMH : M ≤ H)
    (hK : K ≤ BranchOracleBudget.budget (Fintype.card ι : ℝ) ρ H) :
    p.mass H ≤ ρ / 4 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact (run.chronological_bound hρ hρ1 H).trans
    (BranchOracleBudget.accountingBound_le_quarter_of_budget (Fintype.card ι : ℝ) ρ hn hρ hρ1 K r M H hH hrM hMH hK)

theorem ScheduledRun.terminal_mass_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K r : ℕ} {p : WordProfile ι} (run : ScheduledRun ρ K r p)
    (M H : ℕ) (hH : 0 < H) (hrM : r ≤ M) (hMH : M ≤ H)
    (hK : K ≤ BranchOracleBudget.budget (Fintype.card ι : ℝ) ρ H) :
    p.mass H ≤ ρ := by
  have hh := run.terminal_mass_le_quarter hρ hρ1 M H hH hrM hMH hK
  linarith

end NCConcave16991.BranchOracle.WordProfile
