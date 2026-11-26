import SampleReuse.CurvatureScalarBounds
import SampleReuse.CurvatureGaussianBounds
import SampleReuse.CurvatureChain
import SecondOrder.CurvatureLocal

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

/-- A fixed scalar constant: its definition has no dimension or chain parameter. -/
def curvatureScalarConstant : ℝ :=
  1 + curvatureGate_boundedC3.2.choose + curvaturePotential_boundedC3.2.choose

theorem curvatureScalarConstant_ge_one : 1 ≤ curvatureScalarConstant := by
  have hg := curvatureGate_boundedC3.2.choose_spec.1
  have hb := curvaturePotential_boundedC3.2.choose_spec.1
  dsimp [curvatureScalarConstant]
  linarith

theorem curvatureScalarConstant_nonneg : 0 ≤ curvatureScalarConstant :=
  zero_le_one.trans curvatureScalarConstant_ge_one

theorem curvatureGate_iterated_bound (x : ℝ) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k curvatureGate x‖ ≤ curvatureScalarConstant := by
  apply (curvatureGate_boundedC3.2.choose_spec.2 x k hk).trans
  have h := curvaturePotential_boundedC3.2.choose_spec.1
  dsimp [curvatureScalarConstant]
  linarith

theorem curvaturePotential_iterated_bound (x : ℝ) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k curvaturePotential x‖ ≤ curvatureScalarConstant := by
  apply (curvaturePotential_boundedC3.2.choose_spec.2 x k hk).trans
  have h := curvatureGate_boundedC3.2.choose_spec.1
  dsimp [curvatureScalarConstant]
  linarith

theorem iterated_product_bound_three {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    {C : ℝ} (hC : 0 ≤ C) (x : E)
    (hbf : ∀ k, k ≤ 3 → ‖iteratedFDeriv ℝ k f x‖ ≤ C)
    (hbg : ∀ k, k ≤ 3 → ‖iteratedFDeriv ℝ k g x‖ ≤ C)
    (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ 8*C^2 := by
  have hkc : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hsum : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*C*C) ≤ 8*C^2 := by
    interval_cases k <;> norm_num [Finset.sum_range_succ, Nat.choose] <;>
      nlinarith [sq_nonneg C]
  apply (norm_iteratedFDeriv_mul_le hf hg x hkc).trans
  apply (Finset.sum_le_sum (fun i hi => ?_)).trans hsum
  have hi' : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hbf i hi') (Nat.cast_nonneg _))
    (hbg (k-i) (by omega)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)

def deterministicCurvatureLocalLink {T : ℕ} (i : Fin T)
    (y : LocalBlockSpace (fun _ : Fin (T+1) => ℝ) (chainSupport i)) : ℝ :=
  curvatureGate (y (chainLeft i))*curvaturePotential (y (chainRight i))

theorem deterministicCurvatureLocalLink_contDiff {T : ℕ} (i : Fin T) :
    ContDiff ℝ 3 (deterministicCurvatureLocalLink i) :=
  ((curvatureGate_contDiff 3).comp (blockProj (E := ℝ) (chainLeft i)).contDiff).mul
    ((curvaturePotential_contDiff 3).comp (blockProj (E := ℝ) (chainRight i)).contDiff)

theorem deterministicCurvatureLocalLink_bound {T : ℕ} (i : Fin T)
    (y : LocalBlockSpace (fun _ : Fin (T+1) => ℝ) (chainSupport i))
    (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (deterministicCurvatureLocalLink i) y‖ ≤
      8*curvatureScalarConstant^2 := by
  let L := blockProj (E := ℝ) (chainLeft i)
  let R := blockProj (E := ℝ) (chainRight i)
  apply iterated_product_bound_three
    ((curvatureGate_contDiff 3).comp L.contDiff)
    ((curvaturePotential_contDiff 3).comp R.contDiff)
    curvatureScalarConstant_nonneg y _ _ k hk
  · intro j hj
    exact (iteratedFDeriv_linear_contraction curvatureGate L (blockProj_norm_le_one _) j
      ((curvatureGate_contDiff 3).of_le (by exact_mod_cast hj)) y).trans
        (curvatureGate_iterated_bound (L y) j hj)
  · intro j hj
    exact (iteratedFDeriv_linear_contraction curvaturePotential R (blockProj_norm_le_one _) j
      ((curvaturePotential_contDiff 3).of_le (by exact_mod_cast hj)) y).trans
        (curvaturePotential_iterated_bound (R y) j hj)

theorem deterministicCurvatureChain_eq_local (T : ℕ) :
    deterministicCurvatureChain T = fun x => curvatureGate 1*curvaturePotential (x 0)+
      localObjective (fun _ : Fin (T+1) => ℝ) chainSupport deterministicCurvatureLocalLink x := rfl

/-- Actual second and third derivative operator norms, uniformly in chain length. -/
theorem deterministicCurvatureChain_iterated_bound (T k : ℕ) (hk : k=2 ∨ k=3)
    (x : Point (T+1)) :
    ‖iteratedFDeriv ℝ k (deterministicCurvatureChain T) x‖ ≤
      17*curvatureScalarConstant^2 := by
  let head : Point (T+1) → ℝ := fun y => curvaturePotential (y 0)
  let links := localObjective (fun _ : Fin (T+1) => ℝ) chainSupport deterministicCurvatureLocalLink
  have hk3 : k ≤ 3 := by omega
  have hkc : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk3
  have hh3 : ContDiff ℝ 3 head := (curvaturePotential_contDiff 3).comp
    (blockProj (E := ℝ) (0 : Fin (T+1))).contDiff
  have hl3 : ContDiff ℝ 3 links := localObjective_contDiff _ _ _
    deterministicCurvatureLocalLink_contDiff
  have hh : ‖iteratedFDeriv ℝ k head x‖ ≤ curvatureScalarConstant :=
    (iteratedFDeriv_linear_contraction curvaturePotential
      (blockProj (E := ℝ) (0 : Fin (T+1))) (blockProj_norm_le_one _) k
      ((curvaturePotential_contDiff 3).of_le hkc) x).trans
        (curvaturePotential_iterated_bound (x 0) k hk3)
  have hl : ‖iteratedFDeriv ℝ k links x‖ ≤ 16*curvatureScalarConstant^2 := by
    rcases hk with rfl | rfl
    · convert chainObjective_second_bound (fun _ : Fin (T+1) => ℝ)
        deterministicCurvatureLocalLink
        (fun i => (deterministicCurvatureLocalLink_contDiff i).of_le (by decide))
        (by positivity : 0 ≤ 8*curvatureScalarConstant^2)
        (fun i y => deterministicCurvatureLocalLink_bound i y 2 (by decide)) x using 1
      ring
    · convert chainObjective_third_bound (fun _ : Fin (T+1) => ℝ)
        deterministicCurvatureLocalLink deterministicCurvatureLocalLink_contDiff
        (by positivity : 0 ≤ 8*curvatureScalarConstant^2)
        (fun i y => deterministicCurvatureLocalLink_bound i y 3 le_rfl) x using 1
      ring
  rw [deterministicCurvatureChain_eq_local]
  change ‖iteratedFDeriv ℝ k (fun y => curvatureGate 1 • head y+links y) x‖ ≤ _
  rw [iteratedFDeriv_add_apply' ((hh3.of_le hkc).const_smul _).contDiffAt (hl3.of_le hkc).contDiffAt,
    iteratedFDeriv_const_smul_apply' (hh3.of_le hkc).contDiffAt]
  have hg : ‖curvatureGate 1‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (curvatureGate_nonneg 1)]
    exact curvatureGate_le_one 1
  have hhead : ‖curvatureGate 1 • iteratedFDeriv ℝ k head x‖ ≤ curvatureScalarConstant := by
    rw [norm_smul]
    exact (mul_le_mul hg hh (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hC := curvatureScalarConstant_ge_one
  exact (norm_add_le _ _).trans ((add_le_add hhead hl).trans (by nlinarith))

theorem deterministicCurvatureChain_gradient_lipschitz (T : ℕ) (x y : Point (T+1)) :
    ‖gradient (deterministicCurvatureChain T) y-gradient (deterministicCurvatureChain T) x‖ ≤
      17*curvatureScalarConstant^2*‖y-x‖ := by
  exact gradient_lipschitz_of_second_bound (deterministicCurvatureChain_contDiff T 2)
    (fun z => deterministicCurvatureChain_iterated_bound T 2 (Or.inl rfl) z) x y

theorem deterministicCurvatureChain_hessian_lipschitz (T : ℕ) (x y : Point (T+1)) :
    ‖hessian (deterministicCurvatureChain T) y-hessian (deterministicCurvatureChain T) x‖ ≤
      17*curvatureScalarConstant^2*‖y-x‖ :=
  fderiv_gradient_lipschitz_of_third_bound (deterministicCurvatureChain_contDiff T 3)
    (fun z => deterministicCurvatureChain_iterated_bound T 3 (Or.inr rfl) z) x y

end
end SampleReuse
