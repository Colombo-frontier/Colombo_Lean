import Matvec.Model
import Matvec.GameScaleArithmetic
import Mathlib.Tactic

/-! Scalar estimates preserving the manuscript's query rate under a dyadic
hard core followed by dimension extension. -/
namespace Matvec
noncomputable section

def sourceDenominator (N : ℕ) : ℝ :=
  (Real.log (N + 2)) ^ 2 * Real.log (Real.log (N + Real.exp (Real.exp 1)))

theorem source_loglog_ge_one (N : ℕ) :
    1 ≤ Real.log (Real.log (N + Real.exp (Real.exp 1))) := by
  have hfirst : Real.exp 1 ≤ Real.log (N + Real.exp (Real.exp 1)) := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
      _ ≤ Real.log (N + Real.exp (Real.exp 1)) :=
        Real.log_le_log (Real.exp_pos _) (by
          have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have h := Real.log_le_log (Real.exp_pos 1) hfirst
  simpa only [Real.log_exp] using h

theorem sourceDenominator_pos (N : ℕ) : 0 < sourceDenominator N := by
  have hlog : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by
    have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hloglog : 0 < Real.log (Real.log (N + Real.exp (Real.exp 1))) :=
    lt_of_lt_of_le (by norm_num) (source_loglog_ge_one N)
  exact mul_pos (sq_pos_of_pos hlog) hloglog

theorem sourceDenominator_mono {m n : ℕ} (h : m ≤ n) :
    sourceDenominator m ≤ sourceDenominator n := by
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hlogm : 0 ≤ Real.log (m + 2 : ℝ) := (Real.log_pos (by
    have := Nat.cast_nonneg (α := ℝ) m; linarith)).le
  have hlogn : 0 ≤ Real.log (n + 2 : ℝ) := (Real.log_pos (by
    have := Nat.cast_nonneg (α := ℝ) n; linarith)).le
  have hlog : Real.log (m + 2 : ℝ) ≤ Real.log (n + 2 : ℝ) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsquare := (sq_le_sq₀ hlogm hlogn).mpr hlog
  have hinner : Real.log (m + Real.exp (Real.exp 1)) ≤
      Real.log (n + Real.exp (Real.exp 1)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hinnerpos : 0 < Real.log (m + Real.exp (Real.exp 1)) := by
    apply Real.log_pos
    have hbig : 1 < Real.exp (Real.exp 1) := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have houter := Real.log_le_log hinnerpos hinner
  exact mul_le_mul hsquare houter (by linarith [source_loglog_ge_one m]) (sq_nonneg _)

theorem sourceRate_pos {N : ℕ} (hN : 0 < N) : 0 < sourceRate N :=
  div_pos (by exact_mod_cast hN) (sourceDenominator_pos N)

theorem sourceRate_core_comparison {m n : ℕ} (hmn : m ≤ n) (hhalf : n ≤ 2 * m) :
    sourceRate n ≤ 2 * sourceRate m := by
  have hnum : (n : ℝ) ≤ 2 * m := by exact_mod_cast hhalf
  calc
    sourceRate n ≤ (2 * m : ℝ) / sourceDenominator n :=
      div_le_div_of_nonneg_right hnum (sourceDenominator_pos n).le
    _ ≤ (2 * m : ℝ) / sourceDenominator m :=
      div_le_div_of_nonneg_left (by positivity) (sourceDenominator_pos m)
        (sourceDenominator_mono hmn)
    _ = 2 * sourceRate m := by unfold sourceRate sourceDenominator; ring

theorem sourceDenominator_le_log_cube (N : ℕ) :
    sourceDenominator N ≤ Real.log (N + (Real.exp (Real.exp 1) + 2)) ^ 3 := by
  let C := Real.exp (Real.exp 1) + 2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC : 2 < C := by dsimp [C]; linarith [Real.exp_pos (Real.exp 1)]
  have hL : 0 ≤ Real.log (N + C) := (Real.log_pos (by linarith)).le
  have hinner : 0 < Real.log (N + Real.exp (Real.exp 1)) := by
    apply Real.log_pos
    have := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
    linarith
  have hlo : 0 ≤ Real.log (N + 2 : ℝ) := (Real.log_pos (by linarith)).le
  have hfirst : Real.log (N + 2 : ℝ) ≤ Real.log (N + C) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsecond : Real.log (Real.log (N + Real.exp (Real.exp 1))) ≤ Real.log (N + C) := by
    apply Real.log_le_log hinner
    have h := Real.log_le_self (by positivity : (0 : ℝ) ≤ N + Real.exp (Real.exp 1))
    dsimp [C]
    linarith
  have h := mul_le_mul ((sq_le_sq₀ hlo hL).mpr hfirst) hsecond
    (by linarith [source_loglog_ge_one N]) (sq_nonneg (Real.log (N + C)))
  change sourceDenominator N ≤ _ at h
  simpa only [pow_succ] using h

/-- The source rate diverges, allowing a proved K+1 lower bound to be
converted to a K lower bound after increasing the universal dimension cutoff. -/
theorem sourceRate_eventually_ge (B : ℝ) : ∀ᶠ N : ℕ in Filter.atTop, B ≤ sourceRate N := by
  let C := Real.exp (Real.exp 1) + 2
  have hlim : Filter.Tendsto (fun N : ℕ => Real.log (N + C) ^ 3 / (N : ℝ))
      Filter.atTop (nhds 0) := by
    have hshift : Filter.Tendsto (fun N : ℕ => (N : ℝ) + C) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ C tendsto_natCast_atTop_atTop
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-C) 3 one_ne_zero).comp hshift
    simpa only [Function.comp_def, one_mul, add_neg_cancel_right] using h
  let D := max B 1
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_right B 1)
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop, Real.log (N + C) ^ 3 / (N : ℝ) < 1 / D :=
    hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / D))
  filter_upwards [hsmall, Filter.eventually_gt_atTop (0 : ℕ)] with N hsmall hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden := sourceDenominator_pos N
  have hbound : sourceDenominator N / (N : ℝ) < 1 / D :=
    (div_le_div_of_nonneg_right (sourceDenominator_le_log_cube N) hNR.le).trans_lt hsmall
  have hmul := (div_lt_div_iff₀ hNR hD).mp hbound
  have hrate : D ≤ sourceRate N := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  exact (le_max_left B 1).trans hrate

theorem sourceRate_large (B : ℝ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, B ≤ sourceRate N :=
  Filter.eventually_atTop.mp (sourceRate_eventually_ge B)

theorem doubled_dimension_denominator_bound (N : ℕ) :
    Real.log (2 * (N : ℝ) + 2) ^ 2 * Real.log (Real.log (2 * (N : ℝ) + 2)) ≤
      8 * sourceDenominator N := by
  have hN := Nat.cast_nonneg (α := ℝ) N
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hee : (2 : ℝ) ≤ Real.exp (Real.exp 1) := by linarith [Real.add_one_le_exp (Real.exp 1)]
  have hln : 0 ≤ Real.log (N + 2 : ℝ) := (Real.log_pos (by linarith)).le
  have hld : 0 < Real.log (2 * (N : ℝ) + 2) := Real.log_pos (by linarith)
  have hlE : 0 < Real.log (N + Real.exp (Real.exp 1)) := Real.log_pos (by linarith)
  have hlog := log_twice_add_two hN
  have hs : Real.log (2 * (N : ℝ) + 2) ^ 2 ≤ 4 * Real.log (N + 2 : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ hld.le (mul_nonneg (by norm_num) hln)).mpr hlog
    nlinarith
  have hin : Real.log (2 * (N : ℝ) + 2) ≤ 2 * Real.log (N + Real.exp (Real.exp 1)) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < N + 2)
      (by linarith : (N : ℝ) + 2 ≤ N + Real.exp (Real.exp 1))
    linarith
  have hout : Real.log (Real.log (2 * (N : ℝ) + 2)) ≤
      2 * Real.log (Real.log (N + Real.exp (Real.exp 1))) := by
    have h := Real.log_le_log hld hin
    rw [Real.log_mul (by norm_num) hlE.ne'] at h
    have h2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢; exact h
    linarith [source_loglog_ge_one N]
  calc
    _ ≤ Real.log (2 * (N : ℝ) + 2) ^ 2 *
        (2 * Real.log (Real.log (N + Real.exp (Real.exp 1)))) :=
      mul_le_mul_of_nonneg_left hout (sq_nonneg _)
    _ ≤ (4 * Real.log (N + 2 : ℝ) ^ 2) *
        (2 * Real.log (Real.log (N + Real.exp (Real.exp 1)))) :=
      mul_le_mul_of_nonneg_right hs (by linarith [source_loglog_ge_one N])
    _ = _ := by unfold sourceDenominator; ring

theorem absorb_query_add_one {r C : ℝ} {K : ℕ} (hC : 0 < C)
    (hlarge : 2 * C ≤ r) (hbound : r ≤ C * (K + 1 : ℝ)) :
    (1 / (2 * C)) * r ≤ K := by
  have h : r ≤ 2 * C * K := by nlinarith
  have h' : r / (2 * C) ≤ (K : ℝ) :=
    (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr (by nlinarith)
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using h'

end
end Matvec
