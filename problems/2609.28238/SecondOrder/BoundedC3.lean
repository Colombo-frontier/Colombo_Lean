import SecondOrder.ScalarJetAlgebra

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Global bounds through order three, used only for sample regularity.
These bounds may depend on the finite chain length. -/
def BoundedC3 (f : E → ℝ) : Prop := ContDiff ℝ 3 f ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x k, k ≤ 3 → ‖iteratedFDeriv ℝ k f x‖ ≤ C

theorem boundedC3_const (c : ℝ) : BoundedC3 (fun _ : E => c) := by
  refine ⟨contDiff_const, |c|, abs_nonneg c, ?_⟩
  intro x k _
  cases k with
  | zero => simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, le_refl]
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; exact abs_nonneg c

theorem BoundedC3.add {f g : E → ℝ} (hf : BoundedC3 f) (hg : BoundedC3 g) :
    BoundedC3 (fun y => f y+g y) := by
  obtain ⟨hf, C, hC, hbC⟩ := hf
  obtain ⟨hg, D, hD, hbD⟩ := hg
  refine ⟨hf.add hg, C+D, add_nonneg hC hD, ?_⟩
  intro x k hk
  have hkc : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  rw [iteratedFDeriv_add_apply' (hf.of_le hkc).contDiffAt (hg.of_le hkc).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hbC x k hk) (hbD x k hk))

theorem BoundedC3.mul {f g : E → ℝ} (hf : BoundedC3 f) (hg : BoundedC3 g) :
    BoundedC3 (fun y => f y*g y) := by
  obtain ⟨hf, C, hC, hbC⟩ := hf
  obtain ⟨hg, D, hD, hbD⟩ := hg
  refine ⟨hf.mul hg, 8*C*D, by positivity, ?_⟩
  intro x k hk
  have hkc : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hsum : (∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)*C*D) ≤ 8*C*D := by
    interval_cases k <;> norm_num [Finset.sum_range_succ, Nat.choose] <;> nlinarith [mul_nonneg hC hD]
  apply (norm_iteratedFDeriv_mul_le hf hg x hkc).trans
  apply (Finset.sum_le_sum (fun i hi => ?_)).trans hsum
  have hi' : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hbC x i hi') (Nat.cast_nonneg _))
    (hbD x (k-i) (by omega)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)

theorem BoundedC3.const_mul {f : E → ℝ} (hf : BoundedC3 f) (c : ℝ) :
    BoundedC3 (fun y => c*f y) := (boundedC3_const c).mul hf

theorem BoundedC3.one_sub {f : E → ℝ} (hf : BoundedC3 f) :
    BoundedC3 (fun y => 1-f y) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using (boundedC3_const (1:ℝ)).add (hf.const_mul (-1))

theorem BoundedC3.comp_contraction {f : F → ℝ} (hf : BoundedC3 f)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) : BoundedC3 (f ∘ L) := by
  obtain ⟨hf, C, hC, hb⟩ := hf
  refine ⟨hf.comp L.contDiff, C, hC, ?_⟩
  intro x k hk
  exact (iteratedFDeriv_linear_contraction f L hL k (hf.of_le (by exact_mod_cast hk)) x).trans (hb (L x) k hk)

theorem boundedC3_finset_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, BoundedC3 (f i)) : BoundedC3 (fun y => ∑ i ∈ s, f i y) := by
  induction s using Finset.induction_on with
  | empty => simpa using boundedC3_const (E := E) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem boundedC3_finset_prod {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, BoundedC3 (f i)) : BoundedC3 (fun y => ∏ i ∈ s, f i y) := by
  induction s using Finset.induction_on with
  | empty => simpa using boundedC3_const (E := E) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem boundedC3_of_dimensionJet {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {C D : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hb : ∀ x, DimensionJetBound C D f x) :
    BoundedC3 f := by
  have hC0 : 0 ≤ C := by linarith
  refine ⟨hf, C, hC0, ?_⟩
  intro x k hk
  have hh := hb x
  interval_cases k
  · rw [norm_iteratedFDeriv_zero]
    exact hh.1.trans hC
  · exact hh.2.1.trans (div_le_self hC0 (Real.one_le_sqrt.mpr hD))
  · exact hh.2.2.1.trans (div_le_self hC0 hD)
  · exact hh.2.2.2.trans (div_le_self hC0 hD)

end
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem BoundedC3.hessian_lipschitz {f : H → ℝ} (hf : BoundedC3 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      ‖fderiv ℝ (gradient f) y-fderiv ℝ (gradient f) x‖ ≤ C*‖y-x‖ := by
  obtain ⟨hf, C, hC, hb⟩ := hf
  exact ⟨C, hC, fderiv_gradient_lipschitz_of_third_bound hf (fun x => hb x 3 le_rfl)⟩

end
end SecondOrder
