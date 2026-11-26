import SampleReuse.CurvatureRegularity

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

theorem chain_restriction_norm_sum (T : ℕ) (v : Point (T+1)) :
    (∑ i : Fin T, ‖blockRestrict (fun _ : Fin (T+1) => ℝ) (chainSupport i) v‖) ≤
      2*Real.sqrt (T+1:ℕ)*‖v‖ := by
  let a := fun i : Fin T => ‖blockRestrict (fun _ : Fin (T+1) => ℝ) (chainSupport i) v‖
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin T => (1:ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  have he := blockRestrict_sq_sum (fun _ : Fin (T+1) => ℝ) chainSupport 2
    (by intro j; convert chainSupport_overlap T j using 1; congr 1; ext i; simp) v
  have hmul := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α := ℝ) T)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (T+1))
  have hn : 0 ≤ 2*Real.sqrt (T+1:ℕ)*‖v‖ := by positivity
  have hnv := sq_nonneg ‖v‖
  have hnn : 0 ≤ (T:ℝ)*‖v‖^2 := mul_nonneg (Nat.cast_nonneg _) hnv
  have hsq : (∑ i, a i)^2 ≤ (2*Real.sqrt (T+1:ℕ)*‖v‖)^2 := by
    have hh := hcs.trans hmul
    dsimp [a] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [mul_pow, mul_pow, hs]
    push_cast
    nlinarith only [hh, hnv, hnn]
  nlinarith only [hsq, hn, sq_nonneg (2*Real.sqrt (T+1:ℕ)*‖v‖ - ∑ i, a i)]

theorem chainObjective_first_bound {T : ℕ}
    (φ : ∀ i : Fin T, LocalBlockSpace (fun _ : Fin (T+1) => ℝ) (chainSupport i) → ℝ)
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i y, ‖iteratedFDeriv ℝ 1 (φ i) y‖ ≤ M) (x : Point (T+1)) :
    ‖iteratedFDeriv ℝ 1 (localObjective (fun _ : Fin (T+1) => ℝ) chainSupport φ) x‖ ≤
      2*M*Real.sqrt (T+1:ℕ) := by
  rw [iteratedFDeriv_localObjective (k := 1) _ _ _ hφ]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [localTensorSum_apply]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ 1 (φ i)
        (blockRestrict (fun _ : Fin (T+1) => ℝ) (chainSupport i) x)
        (fun j => blockRestrict (fun _ : Fin (T+1) => ℝ) (chainSupport i) (v j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, M*‖blockRestrict (fun _ : Fin (T+1) => ℝ) (chainSupport i) (v 0)‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Fin.prod_univ_one] using ContinuousMultilinearMap.le_of_opNorm_le
        (hb i _) (fun j => blockRestrict (fun _ : Fin (T+1) => ℝ) (chainSupport i) (v j))
    _ = M*(∑ i, ‖blockRestrict (fun _ : Fin (T+1) => ℝ) (chainSupport i) (v 0)‖) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ M*(2*Real.sqrt (T+1:ℕ)*‖v 0‖) :=
      mul_le_mul_of_nonneg_left (chain_restriction_norm_sum T (v 0)) hM
    _ = _ := by rw [Fin.prod_univ_one]; ring

theorem deterministicCurvatureChain_gradient_bound (T : ℕ) (x : Point (T+1)) :
    ‖gradient (deterministicCurvatureChain T) x‖ ≤
      17*curvatureScalarConstant^2*Real.sqrt (T+1:ℕ) := by
  rw [norm_gradient_eq_fderiv, ← norm_first_iteratedFDeriv]
  let head : Point (T+1) → ℝ := fun y => curvaturePotential (y 0)
  let links := localObjective (fun _ : Fin (T+1) => ℝ) chainSupport deterministicCurvatureLocalLink
  have hh1 : ContDiff ℝ 1 head := (curvaturePotential_contDiff 1).comp
    (blockProj (E := ℝ) (0 : Fin (T+1))).contDiff
  have hl1 : ContDiff ℝ 1 links := localObjective_contDiff _ _ _
    (fun i => (deterministicCurvatureLocalLink_contDiff i).of_le (by decide))
  have hh : ‖iteratedFDeriv ℝ 1 head x‖ ≤ curvatureScalarConstant :=
    (iteratedFDeriv_linear_contraction curvaturePotential
      (blockProj (E := ℝ) (0 : Fin (T+1))) (blockProj_norm_le_one _) 1
      (curvaturePotential_contDiff 1) x).trans
        (curvaturePotential_iterated_bound (x 0) 1 (by decide))
  have hl : ‖iteratedFDeriv ℝ 1 links x‖ ≤
      16*curvatureScalarConstant^2*Real.sqrt (T+1:ℕ) := by
    convert chainObjective_first_bound deterministicCurvatureLocalLink
      (fun i => (deterministicCurvatureLocalLink_contDiff i).of_le (by decide))
      (by positivity : 0 ≤ 8*curvatureScalarConstant^2)
      (fun i y => deterministicCurvatureLocalLink_bound i y 1 (by decide)) x using 1
    ring
  rw [deterministicCurvatureChain_eq_local]
  change ‖iteratedFDeriv ℝ 1 (fun y => curvatureGate 1 • head y+links y) x‖ ≤ _
  rw [iteratedFDeriv_add_apply' (i := 1) (hh1.const_smul _).contDiffAt hl1.contDiffAt,
    iteratedFDeriv_const_smul_apply' (i := 1) hh1.contDiffAt]
  have hg : ‖curvatureGate 1‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (curvatureGate_nonneg 1)]
    exact curvatureGate_le_one 1
  have hhead : ‖curvatureGate 1 • iteratedFDeriv ℝ 1 head x‖ ≤ curvatureScalarConstant := by
    rw [norm_smul]
    exact (mul_le_mul hg hh (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hC := curvatureScalarConstant_ge_one
  have hC0 := curvatureScalarConstant_nonneg
  have hs : 1 ≤ Real.sqrt (T+1:ℕ) := Real.one_le_sqrt.mpr (by exact_mod_cast Nat.succ_pos T)
  have hcs : curvatureScalarConstant ≤ curvatureScalarConstant^2*Real.sqrt (T+1:ℕ) :=
    (show curvatureScalarConstant ≤ curvatureScalarConstant^2 by nlinarith).trans
      (le_mul_of_one_le_right (sq_nonneg _) hs)
  exact (norm_add_le _ _).trans ((add_le_add hhead hl).trans (by nlinarith only [hcs]))

end
end SampleReuse
