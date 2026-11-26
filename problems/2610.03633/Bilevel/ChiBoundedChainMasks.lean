import Bilevel.ChiBoundedChain

/-! Concrete smooth tail masks for the revised bounded chain. Both cutoffs
are C-infinity. The energy cutoff is squared for the source's square-root
derivative property; no old signed-edge residual is reused. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain

def coordinateCutoff (t : ℝ) : ℝ := Real.smoothTransition ((16*t^2-1)/3)
def energyCutoff (s : ℝ) : ℝ := (1-Real.smoothTransition ((4*s-1)/3))^2

theorem coordinateCutoff_contDiff {k : ℕ∞} : ContDiff ℝ k coordinateCutoff :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const).div_const 3)

theorem energyCutoff_contDiff {k : ℕ∞} : ContDiff ℝ k energyCutoff :=
  (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const 3))).pow 2

theorem coordinateCutoff_range (t : ℝ) : 0≤coordinateCutoff t ∧ coordinateCutoff t≤1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem energyCutoff_range (s : ℝ) : 0≤energyCutoff s ∧ energyCutoff s≤1 := by
  have h0 := Real.smoothTransition.nonneg ((4*s-1)/3)
  have h1 := Real.smoothTransition.le_one ((4*s-1)/3)
  unfold energyCutoff
  constructor
  · positivity
  · nlinarith

theorem coordinateCutoff_zero {t : ℝ} (ht : |t|≤1/4) : coordinateCutoff t=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at h
  nlinarith

theorem coordinateCutoff_one {t : ℝ} (ht : 1/2≤|t|) : coordinateCutoff t=1 := by
  apply Real.smoothTransition.one_of_one_le
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) ht 2
  rw [sq_abs] at h
  nlinarith

theorem energyCutoff_one {s : ℝ} (hs : s≤1/4) : energyCutoff s=1 := by
  rw [energyCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : (4*s-1)/3≤0)]
  norm_num

theorem energyCutoff_zero {s : ℝ} (hs : 1≤s) : energyCutoff s=0 := by
  rw [energyCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤(4*s-1)/3)]
  norm_num

theorem coordinateCutoff_deriv_zero {t : ℝ} (ht : |t|≤1/4) : deriv coordinateCutoff t=0 :=
  ZeroChainResidualCutoffs.deriv_zero_of_constant_on
    ((coordinateCutoff_contDiff (k:=1)).differentiable (by norm_num) t)
    (uniqueDiffOn_Icc (by norm_num : -(1/4:ℝ)<1/4))
    (fun _ hx => coordinateCutoff_zero (abs_le.mpr hx)) (abs_le.mp ht)

def tailEnergy {n : ℕ} (i : Fin (n+1)) (z : Space n) : ℝ :=
  ∑ j : Fin (n+1), if i≤j then coordinateCutoff (z j)^2 else 0

def tailMask {n : ℕ} (i : Fin (n+1)) (z : Space n) : ℝ := energyCutoff (tailEnergy i z)

def energyDerivative {n : ℕ} (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  ∑ j : Fin (n+1), if i≤j then
    (2*coordinateCutoff (z j)*deriv coordinateCutoff (z j)) • EuclideanSpace.proj (𝕜:=ℝ) j else 0

def maskDerivative {n : ℕ} (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  deriv energyCutoff (tailEnergy i z) • energyDerivative i z

theorem tailEnergy_contDiff {n : ℕ} (i : Fin (n+1)) (k : ℕ) : ContDiff ℝ k (tailEnergy i) := by
  apply ContDiff.sum
  intro j _
  by_cases hij : i≤j
  · simp only [if_pos hij]
    exact (coordinateCutoff_contDiff.comp (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff).pow 2
  · simpa only [if_neg hij] using contDiff_const

theorem tailMask_contDiff {n : ℕ} (i : Fin (n+1)) (k : ℕ) : ContDiff ℝ k (tailMask i) :=
  energyCutoff_contDiff.comp (tailEnergy_contDiff i k)

theorem tailEnergy_hasFDerivAt {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (tailEnergy i) (energyDerivative i z) z := by
  apply HasFDerivAt.sum
  intro j _
  by_cases hij : i≤j
  · simp only [if_pos hij]
    have h := (((coordinateCutoff_contDiff (k:=1)).differentiable (by norm_num) (z j)).hasDerivAt.pow 2).hasFDerivAt.comp z
      (EuclideanSpace.proj (𝕜:=ℝ) j).hasFDerivAt
    convert h using 1
    ext v
    simp [ContinuousLinearMap.comp_apply]
    ring
  · simpa only [if_neg hij] using hasFDerivAt_const (0:ℝ) z

theorem tailMask_hasFDerivAt {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (tailMask i) (maskDerivative i z) z := by
  convert (((energyCutoff_contDiff (k:=1)).differentiable (by norm_num) (tailEnergy i z)).hasDerivAt.hasFDerivAt.comp z
    (tailEnergy_hasFDerivAt i z)) using 1
  ext v
  simp [maskDerivative,ContinuousLinearMap.comp_apply,mul_comm]

theorem tailMask_range {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    0≤tailMask i z ∧ tailMask i z≤1 := energyCutoff_range _

theorem tailMask_zero_of_large_coordinate {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i≤j) (hj : 1/2≤|z j|) : tailMask i z=0 := by
  apply energyCutoff_zero
  have h := Finset.single_le_sum (f:=fun k : Fin (n+1) =>
    if i≤k then coordinateCutoff (z k)^2 else 0)
    (fun _ _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_univ j)
  simpa only [if_pos hij,coordinateCutoff_one hj,one_pow] using h

theorem tailMask_one_of_small {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hz : ∀ j,i≤j → |z j|≤1/4) : tailMask i z=1 := by
  have he : tailEnergy i z=0 := by
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hij
    · rw [coordinateCutoff_zero (hz j hij)]
      norm_num
    · rfl
  rw [tailMask,he]
  exact energyCutoff_one (by norm_num)

theorem energyDerivative_basis {n : ℕ} (i j : Fin (n+1)) (z : Space n) :
    energyDerivative i z (basis j)=
      if i≤j then 2*coordinateCutoff (z j)*deriv coordinateCutoff (z j) else 0 := by
  classical
  have ht (k : Fin (n+1)) :
      ((if i≤k then (2*coordinateCutoff (z k)*deriv coordinateCutoff (z k)) •
        EuclideanSpace.proj (𝕜:=ℝ) k else 0) : Space n →L[ℝ] ℝ) (basis j)=
      if k=j then (if i≤j then 2*coordinateCutoff (z j)*deriv coordinateCutoff (z j) else 0) else 0 := by
    by_cases hkj : k=j
    · subst k
      split_ifs <;> simp_all [basis]
    · split_ifs <;> simp_all [basis]
  simp only [energyDerivative,ContinuousLinearMap.sum_apply,ht]
  simp

theorem maskDerivative_basis_small {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hj : |z j|≤1/4) : maskDerivative i z (basis j)=0 := by
  simp [maskDerivative,energyDerivative_basis,coordinateCutoff_deriv_zero hj]

end Bilevel.ChiBoundedChain
