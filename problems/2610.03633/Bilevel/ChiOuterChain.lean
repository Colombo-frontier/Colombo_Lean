import Bilevel.ChiOuterPenalty
import Bilevel.ChiBoundedChainSize

/-! The actual bounded one-sided chain, including its negative-side linear
penalty. There are `n+1` coordinates. This is distinct from the two-sided
bounded receiver chain used inside the recursion. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiOuter
open ChiBoundedChain ZeroChainPotential

def edge (a b : ℝ) : ℝ := -psi a * phi b
def edgeLeft (a b : ℝ) : ℝ := -deriv psi a * phi b
def edgeRight (a b : ℝ) : ℝ := -psi a * phiSlope b

def value (n : ℕ) (z : Space n) : ℝ :=
  -phi (z 0) + ∑ i : Fin n, edge (z i.castSucc) (z i.succ) +
    ∑ i : Fin (n+1), penalty (z i)

def edgeGradient {n : ℕ} (i : Fin n) (z : Space n) : Space n :=
  edgeLeft (z i.castSucc) (z i.succ) • basis i.castSucc +
    edgeRight (z i.castSucc) (z i.succ) • basis i.succ

def gradientField (n : ℕ) (z : Space n) : Space n :=
  -phiSlope (z 0) • basis 0 + ∑ i : Fin n, edgeGradient i z +
    ∑ i : Fin (n+1), (-theta (-z i)) • basis i

theorem edge_contDiff {n : ℕ} (i : Fin n) (k : ℕ) :
    ContDiff ℝ k (fun z : Space n => edge (z i.castSucc) (z i.succ)) := by
  exact ((psi_contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).contDiff).neg).mul
    ((phi_contDiff k).comp (EuclideanSpace.proj (𝕜 := ℝ) i.succ).contDiff)

theorem value_contDiff (n k : ℕ) : ContDiff ℝ k (value n) := by
  exact (((phi_contDiff k).comp (EuclideanSpace.proj (𝕜 := ℝ)
    (0 : Fin (n+1))).contDiff).neg.add
    (ContDiff.sum (fun i _ => edge_contDiff i k))).add
    (ContDiff.sum (fun i _ => (penalty_contDiff k).comp
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff))

theorem edgeLeft_nonpos (a b : ℝ) : edgeLeft a b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (psi_deriv_nonneg a)) (phi_nonneg b)

theorem edgeRight_nonpos (a b : ℝ) : edgeRight a b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (psi_nonneg a)) (phiSlope_nonneg b)

theorem edgeRight_le_neg_one (a b : ℝ) (ha : 1 ≤ a) (hb : |b| ≤ 1) :
    edgeRight a b ≤ -1 := by
  have hφ := phi_deriv_ge_one b hb
  rw [phi_deriv] at hφ
  simp only [edgeRight, psi_one ha, neg_mul, one_mul]
  linarith

theorem edge_hasFDerivAt {n : ℕ} (i : Fin n) (z : Space n) :
    HasFDerivAt (fun w : Space n => edge (w i.castSucc) (w i.succ))
      (edgeLeft (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜 := ℝ) i.castSucc +
        edgeRight (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜 := ℝ) i.succ) z := by
  have hi := (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).hasFDerivAt (x := z)
  have hj := (EuclideanSpace.proj (𝕜 := ℝ) i.succ).hasFDerivAt (x := z)
  have hp := ((psi_contDiff (k := 1)).differentiable (by norm_num) (z i.castSucc)).hasDerivAt
  have hd := ((hp.hasFDerivAt.comp z hi).neg).mul ((phi_hasDerivAt (z i.succ)).hasFDerivAt.comp z hj)
  convert hd using 1
  ext v
  simp [edgeLeft, edgeRight, ContinuousLinearMap.comp_apply]
  ring

theorem value_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (value n)
      ((-phiSlope (z 0)) • EuclideanSpace.proj (𝕜 := ℝ) 0 +
        ∑ i : Fin n, (edgeLeft (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜 := ℝ) i.castSucc +
          edgeRight (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜 := ℝ) i.succ) +
        ∑ i : Fin (n+1), (-theta (-z i)) • EuclideanSpace.proj (𝕜 := ℝ) i) z := by
  have h0 := ((phi_hasDerivAt (z 0)).hasFDerivAt.comp z
    (EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt).neg
  have hs := HasFDerivAt.sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => edge_hasFDerivAt i z)
  have hp := HasFDerivAt.sum (fun (i : Fin (n+1)) (_ : i ∈ Finset.univ) =>
    (penalty_hasDerivAt (z i)).hasFDerivAt.comp z
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt)
  convert (h0.add hs).add hp using 1
  ext v
  simp [ContinuousLinearMap.comp_apply, mul_comm]

theorem value_hasGradientAt (n : ℕ) (z : Space n) :
    HasGradientAt (value n) (gradientField n z) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert value_hasFDerivAt n z using 1
  ext v
  simp [InnerProductSpace.toDual_apply, gradientField, edgeGradient, inner_add_left,
    real_inner_smul_left, inner_basis, inner_sum, basis, mul_ite]

theorem actual_gradient (n : ℕ) (z : Space n) : gradient (value n) z = gradientField n z :=
  (value_hasGradientAt n z).gradient

theorem edgeGradient_apply {n : ℕ} (i : Fin n) (z : Space n) (j : Fin (n+1)) :
    edgeGradient i z j =
      (if j = i.castSucc then edgeLeft (z i.castSucc) (z i.succ) else 0) +
      (if j = i.succ then edgeRight (z i.castSucc) (z i.succ) else 0) := by
  simp [edgeGradient, basis, smul_eq_mul, mul_ite]

theorem gradientField_apply (n : ℕ) (z : Space n) (j : Fin (n+1)) :
    gradientField n z j = (if j = 0 then -phiSlope (z 0) else 0) +
      ∑ i : Fin n, edgeGradient i z j - theta (-z j) := by
  classical
  have hs : (∑ i : Fin n, edgeGradient i z) j = ∑ i : Fin n, edgeGradient i z j :=
    map_sum (EuclideanSpace.proj (𝕜 := ℝ) j) (fun i : Fin n => edgeGradient i z) Finset.univ
  have hp : (∑ i : Fin (n+1), (-theta (-z i)) • basis i) j = -theta (-z j) := by
    rw [show (∑ i : Fin (n+1), (-theta (-z i)) • basis i) j =
      ∑ i : Fin (n+1), ((-theta (-z i)) • basis i) j from
        map_sum (EuclideanSpace.proj (𝕜 := ℝ) j)
          (fun i : Fin (n+1) => (-theta (-z i)) • basis i) Finset.univ]
    simp [basis, smul_eq_mul, mul_ite]
  simp only [gradientField, PiLp.add_apply, hs, hp]
  simp [basis, smul_eq_mul, mul_ite, sub_eq_add_neg]

theorem edgeGradient_coord_nonpos {n : ℕ} (i : Fin n) (z : Space n) (j : Fin (n+1)) :
    edgeGradient i z j ≤ 0 := by
  rw [edgeGradient_apply]
  exact add_nonpos (by split_ifs <;> simp [edgeLeft_nonpos])
    (by split_ifs <;> simp [edgeRight_nonpos])

theorem gradient_coord_nonpos (n : ℕ) (z : Space n) (j : Fin (n+1)) :
    gradient (value n) z j ≤ 0 := by
  rw [actual_gradient, gradientField_apply]
  have h0 : (if j = 0 then -phiSlope (z 0) else 0) ≤ 0 := by
    split_ifs <;> simp [phiSlope_nonneg]
  have hs := Finset.sum_nonpos (fun (i : Fin n) (_ : i ∈ Finset.univ) => edgeGradient_coord_nonpos i z j)
  have ht := (theta_range (-z j)).1
  linarith

theorem gradient_le_penalty (n : ℕ) (z : Space n) (j : Fin (n+1)) :
    gradient (value n) z j ≤ -theta (-z j) := by
  rw [actual_gradient, gradientField_apply]
  have h0 : (if j = 0 then -phiSlope (z 0) else 0) ≤ 0 := by
    split_ifs <;> simp [phiSlope_nonneg]
  have hs := Finset.sum_nonpos (fun (i : Fin n) (_ : i ∈ Finset.univ) => edgeGradient_coord_nonpos i z j)
  linarith

theorem gradient_first_le (n : ℕ) (z : Space n) :
    gradient (value n) z 0 ≤ -phiSlope (z 0) := by
  rw [actual_gradient, gradientField_apply, if_pos rfl]
  have hs := Finset.sum_nonpos (fun (i : Fin n) (_ : i ∈ Finset.univ) => edgeGradient_coord_nonpos i z 0)
  have ht := (theta_range (-z 0)).1
  linarith

theorem gradient_succ_le_incoming {n : ℕ} (z : Space n) (i : Fin n) :
    gradient (value n) z i.succ ≤ edgeRight (z i.castSucc) (z i.succ) := by
  classical
  rw [actual_gradient, gradientField_apply, if_neg (Fin.succ_ne_zero i), zero_add]
  have hterm : edgeGradient i z i.succ = edgeRight (z i.castSucc) (z i.succ) := by
    rw [edgeGradient_apply, if_neg, if_pos rfl, zero_add]
    intro he
    have hval := congrArg Fin.val he
    change i.val+1 = i.val at hval
    omega
  rw [← hterm]
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun k => edgeGradient k z i.succ) (Finset.mem_univ i)
  have hs := Finset.sum_nonpos (fun (k : Fin n) (_ : k ∈ Finset.univ.erase i) =>
    edgeGradient_coord_nonpos k z i.succ)
  have ht := (theta_range (-z i.succ)).1
  linarith

end Bilevel.ChiOuter
