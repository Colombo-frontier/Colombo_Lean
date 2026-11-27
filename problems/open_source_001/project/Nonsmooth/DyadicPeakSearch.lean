import Nonsmooth.ComparisonHistoryPolicy
import Mathlib.Tactic

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def dyadicPeakCenter (c s : ℤ) (left center right : ℝ) : ℤ :=
  if center < left then (if right ≤ left then c - s else c + s)
  else (if center < right then c + s else c)

theorem dyadicPeakCenter_bracket (f : ℤ → ℝ) (c s : ℤ)
    (hl : f (c - 2 * s) ≤ f c) (hr : f (c + 2 * s) ≤ f c) :
    let z := dyadicPeakCenter c s (f (c - s)) (f c) (f (c + s))
    f (z - s) ≤ f z ∧ f (z + s) ≤ f z := by
  dsimp only
  unfold dyadicPeakCenter
  split
  · rename_i hleft
    split
    · rename_i hright
      constructor
      · have he : c - s - s = c - 2 * s := by ring
        rw [he]
        exact hl.trans hleft.le
      · simpa using hleft.le
    · rename_i hright
      constructor
      · simpa using (hleft.trans (lt_of_not_ge hright)).le
      · have he : c + s + s = c + 2 * s := by ring
        rw [he]
        exact hr.trans (hleft.trans (lt_of_not_ge hright)).le
  · rename_i hleft
    split
    · rename_i hright
      constructor
      · simpa using hright.le
      · have he : c + s + s = c + 2 * s := by ring
        rw [he]
        exact hr.trans hright.le
    · rename_i hright
      exact ⟨le_of_not_gt hleft, le_of_not_gt hright⟩

def dyadicPeakSearch (f : ℤ → ℝ) : ℕ → ℤ → ℤ
  | 0, c => c
  | n + 1, c => dyadicPeakSearch f n
      (dyadicPeakCenter c (2 ^ n) (f (c - 2 ^ n)) (f c) (f (c + 2 ^ n)))

theorem dyadicPeakSearch_local_max (f : ℤ → ℝ) (n : ℕ) (c : ℤ)
    (hl : f (c - 2 ^ n) ≤ f c) (hr : f (c + 2 ^ n) ≤ f c) :
    f (dyadicPeakSearch f n c - 1) ≤ f (dyadicPeakSearch f n c) ∧
      f (dyadicPeakSearch f n c + 1) ≤ f (dyadicPeakSearch f n c) := by
  induction n generalizing c with
  | zero => simpa only [pow_zero, dyadicPeakSearch] using And.intro hl hr
  | succ n ih =>
    have he : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [he] at hl hr
    have hb := dyadicPeakCenter_bracket f c (2 ^ n) hl hr
    exact ih _ hb.1 hb.2

theorem dyadicPeakCenter_add_const (c s : ℤ) (l v r b : ℝ) :
    dyadicPeakCenter c s (l + b) (v + b) (r + b) = dyadicPeakCenter c s l v r := by
  simp only [dyadicPeakCenter, add_lt_add_iff_right, add_le_add_iff_right]

theorem dyadicPeakSearch_add_const (f : ℤ → ℝ) (b : ℝ) (n : ℕ) (c : ℤ) :
    dyadicPeakSearch (fun z => f z + b) n c = dyadicPeakSearch f n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [dyadicPeakSearch, dyadicPeakCenter_add_const, ih]

end
end Nonsmooth
