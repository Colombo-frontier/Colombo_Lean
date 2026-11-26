import Nonsmooth.ActualCyclicPeak

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem dyadicPeakCenter_value_ge (f : ℤ → ℝ) (c s : ℤ) :
    f c ≤ f (dyadicPeakCenter c s (f (c - s)) (f c) (f (c + s))) := by
  unfold dyadicPeakCenter
  split
  · rename_i hl
    split
    · exact hl.le
    · rename_i hr
      exact (hl.trans (lt_of_not_ge hr)).le
  · split
    · rename_i hr
      exact hr.le
    · exact le_rfl

theorem dyadicPeakSearch_value_ge (f : ℤ → ℝ) (n : ℕ) (c : ℤ) :
    f c ≤ f (dyadicPeakSearch f n c) := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih => exact (dyadicPeakCenter_value_ge f c (2 ^ n)).trans (ih _)

theorem cyclicDyadicPeak_value_ge (f : ℤ → ℝ) (N : ℕ) (i : Fin 4) :
    f ((i.val : ℤ) * 2 ^ N) ≤ f (cyclicDyadicPeak f N) :=
  (bestFourResponse_max (fun j => f ((j.val : ℤ) * 2 ^ N)) i).trans
    (dyadicPeakSearch_value_ge f N _)

theorem cyclicPeakPolicy_value_ge_zero (f : ℤ → ℝ) (N : ℕ) :
    f 0 ≤ f ((cyclicPeakPolicy N).result f () (3 * N + 4)) := by
  rw [cyclicPeakPolicy_result_exact]
  simpa using cyclicDyadicPeak_value_ge f N 0

end
end Nonsmooth
