import Bilevel.ZeroChainResidual

/-! Actual gradient locality of the paper's exact tail-mask decomposition. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainResidualLocality
open ZeroChain ZeroChainProfiles ZeroChainPotential ZeroChainResidualCutoffs ZeroChainResidual

def componentDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  Fin.cases ((-phiSlope (z 0)) • EuclideanSpace.proj (𝕜:=ℝ) 0)
    (fun j => edgeLeft (z j.castSucc) (z j.succ) • EuclideanSpace.proj (𝕜:=ℝ) j.castSucc +
      edgeRight (z j.castSucc) (z j.succ) • EuclideanSpace.proj (𝕜:=ℝ) j.succ) i

def energyDerivative {n : ℕ} (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  ∑ j : Fin (n+1), if i ≤ j then
    (2*coordinateCutoff (z j)*deriv coordinateCutoff (z j)) • EuclideanSpace.proj (𝕜:=ℝ) j else 0

def maskDerivative {n : ℕ} (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  deriv energyCutoff (tailEnergy i z) • energyDerivative i z

def residualDerivative (n : ℕ) (z : Space n) : Space n →L[ℝ] ℝ :=
  ∑ i : Fin (n+1), (tailMask i z • componentDerivative n i z + component n i z • maskDerivative i z)

theorem component_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (component n i) (componentDerivative n i z) z := by
  refine Fin.cases ?_ (fun j => edge_hasFDerivAt j z) i
  convert ((phi_hasDerivAt (z 0)).hasFDerivAt.comp z
    (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin (n+1))).hasFDerivAt).neg using 1
  ext v
  simp [componentDerivative, ContinuousLinearMap.comp_apply, mul_comm]

theorem tailEnergy_hasFDerivAt {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (tailEnergy i) (energyDerivative i z) z := by
  apply HasFDerivAt.sum
  intro j _
  by_cases hij : i ≤ j
  · simp only [if_pos hij]
    have h := ((coordinateCutoff_contDiff.differentiable (by norm_num) (z j)).hasDerivAt.pow 2).hasFDerivAt.comp z
      (EuclideanSpace.proj (𝕜:=ℝ) j).hasFDerivAt
    convert h using 1
    ext v
    simp [ContinuousLinearMap.comp_apply]
    ring
  · simpa only [if_neg hij] using hasFDerivAt_const (0:ℝ) z

theorem tailMask_hasFDerivAt {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (tailMask i) (maskDerivative i z) z := by
  convert ((energyCutoff_contDiff.differentiable (by norm_num) (tailEnergy i z)).hasDerivAt.hasFDerivAt.comp z
    (tailEnergy_hasFDerivAt i z)) using 1
  ext v
  simp [maskDerivative, ContinuousLinearMap.comp_apply, mul_comm]

theorem rawResidual_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (rawResidual n) (residualDerivative n z) z := by
  convert HasFDerivAt.sum (fun i (_ : i ∈ Finset.univ) =>
    (component_hasFDerivAt n i z).mul (tailMask_hasFDerivAt i z)) using 1
  simp only [residualDerivative, add_comm]

theorem residual_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (residual n) (residualDerivative n z) z := by
  exact (rawResidual_hasFDerivAt n z).sub_const _

theorem value_hasFDerivAt_sum (n : ℕ) (z : Space n) :
    HasFDerivAt (value n) (∑ i : Fin (n+1), componentDerivative n i z) z := by
  convert HasFDerivAt.sum (fun i (_ : i ∈ Finset.univ) => component_hasFDerivAt n i z) using 1
  ext w
  exact (sum_component n w).symm

theorem revealed_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (revealed n) ((∑ i : Fin (n+1), componentDerivative n i z)-residualDerivative n z) z :=
  (value_hasFDerivAt_sum n z).sub (residual_hasFDerivAt n z)

theorem gradient_coordinate_eq {n : ℕ} {f : Space n → ℝ} {D : Space n →L[ℝ] ℝ}
    {z : Space n} (hf : HasFDerivAt f D z) (j : Fin (n+1)) : gradient f z j = D (basis j) := by
  have he := hf.unique hf.differentiableAt.hasGradientAt.hasFDerivAt
  rw [he, InnerProductSpace.toDual_apply, real_inner_comm, inner_basis]

theorem energyDerivative_basis {n : ℕ} (i j : Fin (n+1)) (z : Space n) :
    energyDerivative i z (basis j) =
      if i ≤ j then 2*coordinateCutoff (z j)*deriv coordinateCutoff (z j) else 0 := by
  classical
  have ht (k : Fin (n+1)) :
      ((if i ≤ k then (2*coordinateCutoff (z k)*deriv coordinateCutoff (z k)) •
        EuclideanSpace.proj (𝕜:=ℝ) k else 0) : Space n →L[ℝ] ℝ) (basis j) =
      if k = j then (if i ≤ j then 2*coordinateCutoff (z j)*deriv coordinateCutoff (z j) else 0) else 0 := by
    by_cases hkj : k = j
    · subst k
      split_ifs <;> simp_all [basis]
    · split_ifs <;> simp_all [basis]
  simp only [energyDerivative, ContinuousLinearMap.sum_apply, ht]
  simp

theorem maskDerivative_basis_small {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hj : |z j| ≤ 1/4) : maskDerivative i z (basis j) = 0 := by
  have hd : deriv coordinateCutoff (z j) = 0 := by
    simpa only [iteratedDeriv_one] using coordinateCutoff_flat_inner 1 (by norm_num) (z j) hj
  simp [maskDerivative, energyDerivative_basis, hd]

theorem componentDerivative_basis_late {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i < j) : componentDerivative n i z (basis j) = 0 := by
  revert hij
  refine Fin.cases ?_ (fun k => ?_) i
  · intro hj
    have hj0 : j ≠ 0 := ne_of_gt hj
    simp [componentDerivative, basis, hj0, hj0.symm]
  · intro hk
    have hj0 : j ≠ k.castSucc := by
      intro he
      rw [he] at hk
      change k.val+1 < k.val at hk
      omega
    have hj1 : j ≠ k.succ := ne_of_gt hk
    simp [componentDerivative, basis, hj0, hj1, hj0.symm, hj1.symm]

theorem residualDerivative_tail_eq_value {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1), r ≤ j.val → |z j| ≤ 1/4)
    (j : Fin (n+1)) (hj : r ≤ j.val) :
    residualDerivative n z (basis j) = (∑ i : Fin (n+1), componentDerivative n i z) (basis j) := by
  simp only [residualDerivative, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, maskDerivative_basis_small i j z (hz j hj), smul_zero, add_zero]
  by_cases hi : i.val < r
  · rw [componentDerivative_basis_late i j z (by change i.val < j.val; omega), smul_zero]
  · rw [tailMask_one_of_small i z (fun k hik => hz k (by
      have hik' : i.val ≤ k.val := hik
      omega)), one_smul]

/-- If coordinates after the revealed prefix lie in the flat window, the
actual gradient of A has no coordinates after that prefix. -/
theorem revealed_gradient_support {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1), r ≤ j.val → |z j| ≤ 1/4)
    (j : Fin (n+1)) (hj : r ≤ j.val) : gradient (revealed n) z j = 0 := by
  rw [gradient_coordinate_eq (revealed_hasFDerivAt n z), ContinuousLinearMap.sub_apply,
    residualDerivative_tail_eq_value r z hz j hj, sub_self]

/-- The actual residual gradient can expose at most the next coordinate. -/
theorem residual_gradient_support {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1), r ≤ j.val → |z j| ≤ 1/4)
    (j : Fin (n+1)) (hj : r+1 ≤ j.val) : gradient (residual n) z j = 0 := by
  have hd := residualDerivative_tail_eq_value r z hz j (by omega)
  rw [gradient_coordinate_eq (residual_hasFDerivAt n z), hd,
    ← gradient_coordinate_eq (value_hasFDerivAt_sum n z)]
  revert hj
  refine Fin.cases ?_ (fun k => ?_) j
  · intro hj
    simp only [Fin.val_zero] at hj
    omega
  · intro hk
    apply gradient_coord_inactive
    · have hp := hz k.castSucc (by change r ≤ k.val; simp only [Fin.val_succ] at hk; omega)
      linarith
    · have hs := hz k.succ (by simp only [Fin.val_succ] at hk ⊢; omega)
      linarith

theorem revealed_gradient_zero (n : ℕ) : gradient (revealed n) 0 = 0 := by
  ext j
  exact revealed_gradient_support 0 0 (by intro j _; simp) j (Nat.zero_le _)

end Bilevel.ZeroChainResidualLocality
