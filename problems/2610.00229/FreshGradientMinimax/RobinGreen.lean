import FreshGradientMinimax.RobinOperator

/-! Both endpoint columns are checked against the actual Robin operator.
Uniqueness of its inverse then identifies the closed-form coefficients. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def robinGreenLast (n : ℕ) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun i => robinSequence n i.val / robinBoundaryDenominator n)

def robinGreenFirst (n : ℕ) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun i => robinSequence n (n - 1 - i.val) / robinBoundaryDenominator n)

theorem robinGreenLast_apply (n : ℕ) (i : Fin n) :
    robinGreenLast n i = robinSequence n i.val / robinBoundaryDenominator n := rfl

theorem robinGreenFirst_apply (n : ℕ) (i : Fin n) :
    robinGreenFirst n i = robinSequence n (n - 1 - i.val) / robinBoundaryDenominator n := rfl

theorem robinGreen_boundary_left {n : ℕ} (hn : 0 < n) :
    (robinStep n ^ 2 + 1 + robinStep n) *
        (robinSequence n 0 / robinBoundaryDenominator n) -
      robinSequence n 1 / robinBoundaryDenominator n = 0 := by
  rw [← mul_div_assoc, ← sub_div, robinSequence_first_boundary hn, zero_div]

theorem robinGreen_boundary_right {n : ℕ} (hn : 10 ≤ n) :
    (robinStep n ^ 2 + 1 + robinStep n) *
        (robinSequence n (n - 1) / robinBoundaryDenominator n) -
      robinSequence n (n - 2) / robinBoundaryDenominator n = 1 := by
  rw [← mul_div_assoc, ← sub_div, robinSequence_last_boundary (by omega),
    div_self (robinBoundaryDenominator_pos hn).ne']

theorem robinGreen_recurrence {n : ℕ} (hn : 0 < n) (i : ℕ) :
    (robinStep n ^ 2 + 2) * (robinSequence n (i + 1) / robinBoundaryDenominator n) -
      robinSequence n i / robinBoundaryDenominator n -
      robinSequence n (i + 2) / robinBoundaryDenominator n = 0 := by
  rw [← mul_div_assoc, ← sub_div, ← sub_div, robinSequence_recurrence hn, zero_div]

theorem robinGreenLast_root {n : ℕ} (hn : 10 ≤ n + 2) :
    robinOperator (n + 2) (robinGreenLast (n + 2)) =
      EuclideanSpace.single (Fin.last (n + 1)) 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [robinOperator_first]
    have hne : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
      intro h; have := congrArg Fin.val h; simp at this
    simp only [robinGreenLast_apply, Fin.val_zero, Fin.val_one, EuclideanSpace.single_apply,
      if_neg hne, if_neg hne.symm]
    exact robinGreen_boundary_left (by omega)
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.succ_last, robinOperator_last]
      simp only [robinGreenLast_apply, Fin.val_last, Fin.coe_castSucc,
        EuclideanSpace.single_apply, if_pos rfl]
      simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_right] using robinGreen_boundary_right hn
    · rw [Fin.succ_castSucc, robinOperator_interior]
      simp only [robinGreenLast_apply, Fin.coe_castSucc, Fin.val_succ,
        EuclideanSpace.single_apply, if_neg (Fin.castSucc_ne_last k.succ),
        if_neg (Fin.castSucc_ne_last k.succ).symm]
      convert robinGreen_recurrence (n := n + 2) (by omega) k.val using 1

theorem robinGreenFirst_root {n : ℕ} (hn : 10 ≤ n + 2) :
    robinOperator (n + 2) (robinGreenFirst (n + 2)) = EuclideanSpace.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [robinOperator_first]
    simp only [robinGreenFirst_apply, Fin.val_zero, Fin.val_one, Nat.sub_zero,
      EuclideanSpace.single_apply, if_pos rfl]
    convert robinGreen_boundary_right hn using 1
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.succ_last, robinOperator_last]
      have hne : Fin.last (n + 1) ≠ (0 : Fin (n + 2)) := by
        intro h; have := congrArg Fin.val h; simp at this
      simp only [robinGreenFirst_apply, Fin.val_last, Fin.coe_castSucc,
        EuclideanSpace.single_apply, if_neg hne, if_neg hne.symm]
      rw [show n + 2 - 1 - (n + 1) = 0 by omega, show n + 2 - 1 - n = 1 by omega]
      exact robinGreen_boundary_left (n := n + 2) (by omega)
    · rw [Fin.succ_castSucc, robinOperator_interior]
      have hne : k.succ.castSucc ≠ (0 : Fin (n + 2)) := by
        intro h; have := congrArg Fin.val h; simp at this
      simp only [robinGreenFirst_apply, Fin.coe_castSucc, Fin.val_succ,
        EuclideanSpace.single_apply, if_neg hne, if_neg hne.symm]
      have he1 : n + 2 - 1 - (k.val + 1) = (n - (k.val + 1)) + 1 := by omega
      have he2 : n + 2 - 1 - k.val = (n - (k.val + 1)) + 2 := by omega
      have he0 : n + 2 - 1 - (k.val + 1 + 1) = n - (k.val + 1) := by omega
      rw [he1, he2, he0]
      have hr := robinGreen_recurrence (n := n + 2) (by omega) (n - (k.val + 1))
      linarith only [hr]

theorem robinInverse_last {n : ℕ} (hn : 10 ≤ n + 2) :
    robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) =
      robinGreenLast (n + 2) := robinInverse_eq_of_root _ (robinGreenLast_root hn)

theorem robinInverse_first {n : ℕ} (hn : 10 ≤ n + 2) :
    robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) =
      robinGreenFirst (n + 2) := robinInverse_eq_of_root _ (robinGreenFirst_root hn)

end FreshGradientMinimax
