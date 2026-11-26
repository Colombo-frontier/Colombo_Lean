import SecondOrder.DyadicEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

variable {J : Type*} [Fintype J] (E : J → Type*)
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]

abbrev BlockSpace := PiLp 2 E
abbrev LocalBlockSpace (s : Finset J) := PiLp 2 (fun j : s => E j)

def blockRestrictLinear (s : Finset J) : BlockSpace E →ₗ[ℝ] LocalBlockSpace E s where
  toFun x := (WithLp.equiv 2 (∀ j : s, E j)).symm (fun j => x j)
  map_add' x y := by ext j; rfl
  map_smul' c x := by ext j; rfl

theorem blockRestrictLinear_norm_sq (s : Finset J) (x : BlockSpace E) :
    ‖blockRestrictLinear E s x‖^2 = ∑ j ∈ s, ‖x j‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_coe_sort s (fun j => ‖x j‖^2)

theorem blockRestrictLinear_norm_le (s : Finset J) (x : BlockSpace E) :
    ‖blockRestrictLinear E s x‖ ≤ ‖x‖ := by
  have hs : ‖blockRestrictLinear E s x‖^2 ≤ ‖x‖^2 := by
    rw [blockRestrictLinear_norm_sq, PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (blockRestrictLinear E s x), norm_nonneg x]

/-- The genuine coordinate restriction, with operator norm at most one. -/
def blockRestrict (s : Finset J) : BlockSpace E →L[ℝ] LocalBlockSpace E s :=
  (blockRestrictLinear E s).mkContinuous 1 (by
    intro x
    simpa using blockRestrictLinear_norm_le E s x)

@[simp] theorem blockRestrict_apply (s : Finset J) (x : BlockSpace E) (j : s) :
    blockRestrict E s x j = x j := rfl

theorem blockRestrict_norm_sq (s : Finset J) (x : BlockSpace E) :
    ‖blockRestrict E s x‖^2 = ∑ j ∈ s, ‖x j‖^2 :=
  blockRestrictLinear_norm_sq E s x

theorem blockRestrict_norm_le (s : Finset J) (x : BlockSpace E) :
    ‖blockRestrict E s x‖ ≤ ‖x‖ := blockRestrictLinear_norm_le E s x

theorem blockRestrict_opNorm_le (s : Finset J) : ‖blockRestrict E s‖ ≤ 1 := by
  apply (blockRestrict E s).opNorm_le_bound (by norm_num)
  intro x
  simpa using blockRestrict_norm_le E s x

variable {I : Type*} [Fintype I] (S : I → Finset J) (r : ℕ)
  (hr : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ r)

include hr

/-- The only multiplicity is the number of local terms containing a block. -/
theorem blockRestrict_sq_sum (x : BlockSpace E) :
    (∑ i, ‖blockRestrict E (S i) x‖^2) ≤ (r:ℝ)*‖x‖^2 := by
  simp_rw [blockRestrict_norm_sq E]
  rw [PiLp.norm_sq_eq_of_L2]
  exact bounded_overlap_sum S r hr (fun j => ‖x j‖^2) (fun _ => sq_nonneg _)

theorem blockRestrict_cross_sum (x y : BlockSpace E) :
    (∑ i, ‖blockRestrict E (S i) x‖*‖blockRestrict E (S i) y‖) ≤ (r:ℝ)*‖x‖*‖y‖ := by
  have hx := blockRestrict_sq_sum E S r hr x
  have hy := blockRestrict_sq_sum E S r hr y
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖blockRestrict E (S i) x‖) (fun i => ‖blockRestrict E (S i) y‖)
  have hm := mul_le_mul hx hy (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  have hsq : (∑ i, ‖blockRestrict E (S i) x‖*‖blockRestrict E (S i) y‖)^2 ≤
      ((r:ℝ)*‖x‖*‖y‖)^2 := by nlinarith [hcs.trans hm]
  have hn : 0 ≤ (r:ℝ)*‖x‖*‖y‖ := by positivity
  nlinarith

theorem blockRestrict_triple_sum (x y z : BlockSpace E) :
    (∑ i, ‖blockRestrict E (S i) x‖*‖blockRestrict E (S i) y‖*‖blockRestrict E (S i) z‖) ≤
      (r:ℝ)*‖x‖*‖y‖*‖z‖ := by
  calc
    _ ≤ ∑ i, (‖blockRestrict E (S i) x‖*‖blockRestrict E (S i) y‖)*‖z‖ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (blockRestrict_norm_le E (S i) z) (by positivity))
    _ = (∑ i, ‖blockRestrict E (S i) x‖*‖blockRestrict E (S i) y‖)*‖z‖ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (blockRestrict_cross_sum E S r hr x y) (norm_nonneg z)

end
end SecondOrder
