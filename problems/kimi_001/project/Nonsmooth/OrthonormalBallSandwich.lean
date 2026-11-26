import Nonsmooth.SymmetricConvexCombination

open Set
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthonormal_coordinate_abs_sum_bound {ι : Type} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i, |e.repr x i| ≤ (Fintype.card ι : ℝ) * ‖x‖ := by
  calc
    ∑ i, |e.repr x i| ≤ ∑ _i : ι, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [e.repr_apply_apply]
      simpa only [e.norm_eq_one, one_mul] using abs_real_inner_le_norm (e i) x
    _ = (Fintype.card ι : ℝ) * ‖x‖ := by simp

theorem symmetric_convex_contains_small_ball {ι : Type} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (hd : 0 < Fintype.card ι)
    {S : Set E} (hconv : Convex ℝ S) (hzero : (0 : E) ∈ S)
    (hsym : ∀ x ∈ S, -x ∈ S) (he : ∀ i, e i ∈ S) :
    Metric.closedBall (0 : E) (1 / (Fintype.card ι : ℝ)) ⊆ S := by
  intro x hx
  have hnorm : ‖x‖ ≤ 1 / (Fintype.card ι : ℝ) := by simpa using hx
  have hdp : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hsum : ∑ i, |e.repr x i| ≤ 1 := by
    calc
      ∑ i, |e.repr x i| ≤ (Fintype.card ι : ℝ) * ‖x‖ := orthonormal_coordinate_abs_sum_bound e x
      _ ≤ (Fintype.card ι : ℝ) * (1 / (Fintype.card ι : ℝ)) :=
        mul_le_mul_of_nonneg_left hnorm hdp.le
      _ = 1 := mul_one_div_cancel hdp.ne'
  have h := symmetric_convex_signed_sum_mem hconv hzero hsym (fun i => e.repr x i) e hsum he
  simpa only [e.sum_repr] using h

theorem basis_change_norm_bound {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ E) (e : OrthonormalBasis ι ℝ E) {x : E}
    (hcoords : ∀ i, |b.repr x i| ≤ 1) :
    ‖b.equiv e.toBasis (Equiv.refl ι) x‖ ≤ (Fintype.card ι : ℝ) := by
  classical
  have heq : b.equiv e.toBasis (Equiv.refl ι) x = ∑ i, b.repr x i • e i := by
    have h := congrArg (b.equiv e.toBasis (Equiv.refl ι)) (b.sum_repr x)
    simpa only [map_sum, map_smul, Module.Basis.equiv_apply, Equiv.refl_apply,
      OrthonormalBasis.coe_toBasis] using h.symm
  rw [heq]
  calc
    ‖∑ i, b.repr x i • e i‖ ≤ ∑ i, ‖b.repr x i • e i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, Real.norm_eq_abs, e.norm_eq_one, mul_one] using hcoords i
    _ = (Fintype.card ι : ℝ) := by simp

end
end Nonsmooth
