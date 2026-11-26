import FreshGradientMinimax.RobinRecurrence
import FreshGradientMinimax.PathGauge

/-! The actual finite Robin operator, represented as r² I + A† A. The two
endpoint incidence rows have weight sqrt r, and all internal rows weight one. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def robinWeight (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = 0 ∨ i = Fin.last n then Real.sqrt (robinStep n) else 1

def robinIncidence (n : ℕ) : Euclid n →L[ℝ] Euclid (n + 1) :=
  (coordinateMultiplier (robinWeight n)).comp (pathIncidence (fun _ => 1))

def robinOperator (n : ℕ) : Euclid n →L[ℝ] Euclid n :=
  normalOperator (robinIncidence n) (robinStep n ^ 2) 1

def robinInverse (n : ℕ) (hn : 0 < n) : Euclid n →L[ℝ] Euclid n :=
  normalInverse (robinIncidence n) (robinStep n ^ 2) 1
    (sq_pos_of_pos (robinStep_pos hn)) (by norm_num)

theorem robinWeight_sq {n : ℕ} (i : Fin (n + 1)) :
    robinWeight n i ^ 2 = if i = 0 ∨ i = Fin.last n then robinStep n else 1 := by
  unfold robinWeight
  split_ifs <;> simp [Real.sq_sqrt (show 0 ≤ robinStep n by unfold robinStep; positivity)]

theorem robinWeight_abs_le {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    |robinWeight n i| ≤ 1 := by
  have hr : robinStep n ≤ 1 := by
    unfold robinStep
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  unfold robinWeight
  split_ifs
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_one).mpr hr
  · norm_num

theorem robinIncidence_norm {n : ℕ} (hn : 0 < n) (y : Euclid n) :
    ‖robinIncidence n y‖ ≤ 2 * ‖y‖ :=
  (coordinateMultiplier_norm_le (robinWeight_abs_le hn) _).trans
    (pathIncidence_norm_bound (by intro i; norm_num) y)

theorem robinIncidence_opNorm {n : ℕ} (hn : 0 < n) : ‖robinIncidence n‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (robinIncidence_norm hn)

theorem robinOperator_coordinate {n : ℕ} (y : Euclid n) (i : Fin n) :
    robinOperator n y i = robinStep n ^ 2 * y i +
      robinWeight n i.castSucc ^ 2 *
        (y i - Fin.cons (α := fun _ => ℝ) 0 (fun j => y j) i.castSucc) -
      robinWeight n i.succ ^ 2 *
        (Fin.snoc (α := fun _ => ℝ) (fun j => y j) 0 i.succ - y i) := by
  simp only [robinOperator, normalOperator_apply, robinIncidence,
    ContinuousLinearMap.adjoint_comp, coordinateMultiplier_adjoint,
    ContinuousLinearMap.comp_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, one_mul, pathIncidence_adjoint_apply,
    coordinateMultiplier_apply, pathIncidence_apply, Fin.snoc_castSucc, Fin.cons_succ]
  ring

theorem robinInverse_right {n : ℕ} (hn : 0 < n) (b : Euclid n) :
    robinOperator n (robinInverse n hn b) = b := normalInverse_right _ _ _ b

theorem robinInverse_eq_of_root {n : ℕ} (hn : 0 < n) {b y : Euclid n}
    (hy : robinOperator n y = b) : robinInverse n hn b = y :=
  normalInverse_eq_of_root _ _ _ hy

theorem robinOperator_first (n : ℕ) (y : Euclid (n + 2)) :
    robinOperator (n + 2) y 0 =
      (robinStep (n + 2) ^ 2 + 1 + robinStep (n + 2)) * y 0 - y 1 := by
  rw [robinOperator_coordinate, robinWeight_sq, robinWeight_sq]
  have h1 : (0 : Fin (n + 2)).succ ≠ Fin.last (n + 2) := by
    intro h; have := congrArg Fin.val h; simp at this
  have he : Fin.snoc (α := fun _ => ℝ) (fun j => y j) 0 (0 : Fin (n + 2)).succ = y 1 := by
    change Fin.snoc (α := fun _ => ℝ) (fun j => y j) 0 (1 : Fin (n + 2)).castSucc = _
    rw [Fin.snoc_castSucc]
  simp only [Fin.castSucc_zero, Fin.cons_zero, sub_zero, true_or, if_true,
    Fin.succ_ne_zero, h1, false_or, if_false, he, one_mul, eq_self_iff_true]
  ring

theorem robinOperator_last (n : ℕ) (y : Euclid (n + 2)) :
    robinOperator (n + 2) y (Fin.last (n + 1)) =
      (robinStep (n + 2) ^ 2 + 1 + robinStep (n + 2)) * y (Fin.last (n + 1)) -
        y (Fin.last n).castSucc := by
  rw [robinOperator_coordinate, robinWeight_sq, robinWeight_sq]
  have hz : (Fin.last (n + 1)).castSucc ≠ (0 : Fin (n + 3)) := by
    intro h; have := congrArg Fin.val h; simp at this
  simp only [Fin.castSucc_ne_last, hz, false_or, if_false, Fin.succ_last,
    or_true, if_true, Fin.snoc_last]
  rw [show (Fin.last (n + 1)).castSucc = (Fin.last n).castSucc.succ by ext; simp]
  rw [Fin.cons_succ]
  ring

theorem robinOperator_interior {n : ℕ} (y : Euclid (n + 2)) (i : Fin n) :
    robinOperator (n + 2) y i.succ.castSucc =
      (robinStep (n + 2) ^ 2 + 2) * y i.succ.castSucc -
        y i.castSucc.castSucc - y i.succ.succ := by
  rw [robinOperator_coordinate, robinWeight_sq, robinWeight_sq]
  have hz : i.succ.castSucc.castSucc ≠ (0 : Fin (n + 3)) := by
    intro h; have := congrArg Fin.val h; simp at this
  have hl : i.succ.castSucc.succ ≠ Fin.last (n + 2) := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  simp only [Fin.castSucc_ne_last, hz, false_or, Fin.succ_ne_zero, hl, if_false, one_mul]
  have hp : Fin.cons (α := fun _ => ℝ) 0 (fun j => y j) i.succ.castSucc.castSucc =
      y i.castSucc.castSucc := by
    rw [← Fin.succ_castSucc, ← Fin.succ_castSucc, Fin.cons_succ]
  have hs : Fin.snoc (α := fun _ => ℝ) (fun j => y j) 0 i.succ.castSucc.succ =
      y i.succ.succ := by rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  rw [hp, hs]
  ring

end FreshGradientMinimax
