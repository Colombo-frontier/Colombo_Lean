import GradientHessian.SelectorPortBounds
import GradientHessian.SelectorRawProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Disjoint-register estimates used in selector composition. The hypothesis
on coordinate maps is the usual Hilbert direct-sum contraction, and is proved
for the literal `PiLp 2` register coordinates below. -/

namespace GradientHessian.SelectorCoordinateBounds
open SelectorProfileBounds SelectorPortBounds
open Classical
open scoped BigOperators
noncomputable section

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def CoordinateContraction (A : ι → F →L[ℝ] E) : Prop :=
  ∀ v, (∑ i, ‖A i v‖^2) ≤ ‖v‖^2

theorem registers_coordinate_contraction :
    CoordinateContraction (fun i : ι => PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) i) := by
  intro v
  simp only [PiLp.proj_apply, PiLp.norm_sq_eq_of_L2]
  exact le_rfl

theorem coordinate_norm_le {A : ι → F →L[ℝ] E} (hA : CoordinateContraction A) (i : ι) (v : F) :
    ‖A i v‖ ≤ ‖v‖ := by
  have h : ‖A i v‖^2 ≤ ∑ j, ‖A j v‖^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖A j v‖) (Finset.mem_univ i)
  have ht := h.trans (hA v)
  nlinarith [norm_nonneg (A i v), norm_nonneg v]

theorem coordinate_product_square_sum {A : ι → F →L[ℝ] E}
    (hA : CoordinateContraction A) {n : ℕ} (hn : 1 ≤ n) (v : Fin n → F) :
    (∑ i, (∏ l, ‖A i (v l)‖)^2) ≤ (∏ l, ‖v l‖)^2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  clear hn
  induction m with
  | zero => simpa using hA (v 0)
  | succ m ih =>
    calc
      _ = ∑ i, ‖A i (v 0)‖^2*(∏ l : Fin (m+1), ‖A i (v l.succ)‖)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.prod_univ_succ, mul_pow]
      _ ≤ ∑ i, ‖v 0‖^2*(∏ l : Fin (m+1), ‖A i (v l.succ)‖)^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (coordinate_norm_le hA i (v 0)) 2) (sq_nonneg _)
      _ = ‖v 0‖^2*(∑ i, (∏ l : Fin (m+1), ‖A i (v l.succ)‖)^2) := by rw [Finset.mul_sum]
      _ ≤ ‖v 0‖^2*(∏ l : Fin (m+1), ‖v l.succ‖)^2 :=
        mul_le_mul_of_nonneg_left (ih (fun l => v l.succ)) (sq_nonneg _)
      _ = _ := by simp only [Fin.prod_univ_succ, mul_pow]

theorem coordinate_pair_sum {A : ι → F →L[ℝ] E}
    (hA : CoordinateContraction A) (v w : F) :
    (∑ i, ‖A i v‖*‖A i w‖) ≤ ‖v‖*‖w‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖A i v‖) (fun i => ‖A i w‖)
  have h₂ : (∑ i, ‖A i v‖^2)*(∑ i, ‖A i w‖^2) ≤ ‖v‖^2*‖w‖^2 :=
    mul_le_mul (hA v) (hA w) (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)
  have h₃ := h.trans h₂
  have hn : 0 ≤ ‖v‖*‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

theorem coordinate_triple_sum {A : ι → F →L[ℝ] E}
    (hA : CoordinateContraction A) (v : Fin 3 → F) :
    (∑ i, ∏ l, ‖A i (v l)‖) ≤ ∏ l, ‖v l‖ := by
  norm_num [Fin.prod_univ_succ]
  calc
    _ ≤ ∑ i, (‖A i (v 0)‖*‖A i (v 1)‖)*‖v 2‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (coordinate_norm_le hA i (v 2))
        (mul_nonneg (norm_nonneg (A i (v 0))) (norm_nonneg (A i (v 1))))
      convert h using 1; ring
    _ = (∑ i, ‖A i (v 0)‖*‖A i (v 1)‖)*‖v 2‖ := by rw [Finset.sum_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (coordinate_pair_sum hA (v 0) (v 1)) (norm_nonneg (v 2))
      convert h using 1; ring

theorem variance_div_factor {a B p : ℝ} (hB : 0 ≤ B)
    (ha : |a| ≤ B*varianceRoot p) :
    varianceRoot p*(a/varianceRoot p) = a ∧ |a/varianceRoot p| ≤ B := by
  have hr : 0 ≤ varianceRoot p := Real.sqrt_nonneg _
  by_cases hz : varianceRoot p = 0
  · have ha0 : a = 0 := by
      rw [hz, mul_zero] at ha
      exact abs_eq_zero.mp (le_antisymm ha (abs_nonneg a))
    simp [ha0, hB]
  · constructor
    · field_simp
    · rw [abs_div, abs_of_nonneg hr]
      exact (div_le_iff₀ (lt_of_le_of_ne hr (Ne.symm hz))).mpr ha

end
end GradientHessian.SelectorCoordinateBounds
