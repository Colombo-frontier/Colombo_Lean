import Bilevel.ChiBoundedChainProfiles
import Bilevel.ZeroChainResidualScaled

/-! Actual revised bounded two-sided chain. The coordinate derivative proof
is adapted from the earlier chain, but all activations here are the concrete
bounded C-infinity `ChiBoundedChain.psi`, rather than the earlier exponential.
There are n+1 coordinates. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

def basis {n : ℕ} (i : Fin (n + 1)) : Space n := EuclideanSpace.single i 1

def edge (a b : ℝ) : ℝ := psi (-a) * phi (-b) - psi a * phi b

def edgeLeft (a b : ℝ) : ℝ := -deriv psi (-a) * phi (-b) - deriv psi a * phi b

def edgeRight (a b : ℝ) : ℝ := -psi (-a) * phiSlope (-b) - psi a * phiSlope b

def value (n : ℕ) (z : Space n) : ℝ :=
  -phi (z 0) + ∑ i : Fin n, edge (z i.castSucc) (z i.succ)

def edgeGradient {n : ℕ} (i : Fin n) (z : Space n) : Space n :=
  edgeLeft (z i.castSucc) (z i.succ) • basis i.castSucc +
    edgeRight (z i.castSucc) (z i.succ) • basis i.succ

def gradientField (n : ℕ) (z : Space n) : Space n :=
  -phiSlope (z 0) • basis 0 + ∑ i : Fin n, edgeGradient i z

theorem edge_contDiff {n : ℕ} (i : Fin n) (k : ℕ) :
    ContDiff ℝ k (fun z : Space n => edge (z i.castSucc) (z i.succ)) := by
  have hi : ContDiff ℝ k (fun z : Space n => z i.castSucc) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).contDiff
  have hj : ContDiff ℝ k (fun z : Space n => z i.succ) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i.succ).contDiff
  exact ((psi_contDiff.comp hi.neg).mul ((phi_contDiff k).comp hj.neg)).sub
    ((psi_contDiff.comp hi).mul ((phi_contDiff k).comp hj))

theorem value_contDiff (n k : ℕ) : ContDiff ℝ k (value n) := by
  have hp : ContDiff ℝ k (fun z : Space n => z 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).contDiff
  have h0 : ContDiff ℝ k (fun z : Space n => -phi (z 0)) :=
    ((phi_contDiff k).comp hp).neg
  exact h0.add (ContDiff.sum (fun i _ => edge_contDiff i k))

theorem inner_basis {n : ℕ} (i : Fin (n + 1)) (v : Space n) : ⟪basis i, v⟫ = v i := by
  simp [basis, EuclideanSpace.inner_single_left]

theorem edge_inactive (a b : ℝ) (ha : |a| ≤ 1 / 2) : edge a b = 0 := by
  have ha0 : a ≤ 1 / 2 := (abs_le.mp ha).2
  have ha1 : -a ≤ 1 / 2 := by linarith [(abs_le.mp ha).1]
  simp only [edge, psi_zero_of_le ha0, psi_zero_of_le ha1, zero_mul, sub_zero]

theorem edgeLeft_inactive (a b : ℝ) (ha : |a| ≤ 1 / 2) : edgeLeft a b = 0 := by
  have ha0 : a ≤ 1 / 2 := (abs_le.mp ha).2
  have ha1 : -a ≤ 1 / 2 := by linarith [(abs_le.mp ha).1]
  simp only [edgeLeft, psi_deriv_zero_of_le ha0, psi_deriv_zero_of_le ha1,
    neg_zero, zero_mul, sub_zero]

theorem edgeRight_inactive (a b : ℝ) (ha : |a| ≤ 1 / 2) : edgeRight a b = 0 := by
  have ha0 : a ≤ 1 / 2 := (abs_le.mp ha).2
  have ha1 : -a ≤ 1 / 2 := by linarith [(abs_le.mp ha).1]
  simp only [edgeRight, psi_zero_of_le ha0, psi_zero_of_le ha1, neg_zero, zero_mul, sub_zero]

theorem edgeGradient_inactive {n : ℕ} (i : Fin n) (z : Space n)
    (ha : |z i.castSucc| ≤ 1 / 2) : edgeGradient i z = 0 := by
  simp only [edgeGradient, edgeLeft_inactive _ _ ha, edgeRight_inactive _ _ ha,
    zero_smul, add_zero]

theorem edgeLeft_nonpos (a b : ℝ) : edgeLeft a b ≤ 0 := by
  have h0 := mul_nonneg (psi_deriv_nonneg (-a)) (phi_nonneg (-b))
  have h1 := mul_nonneg (psi_deriv_nonneg a) (phi_nonneg b)
  dsimp [edgeLeft]
  nlinarith

theorem phiSlope_nonneg (b : ℝ) : 0 ≤ phiSlope b := by
  rw [← phi_deriv]
  exact phi_deriv_nonneg b

theorem edgeRight_nonpos (a b : ℝ) : edgeRight a b ≤ 0 := by
  have h0 := mul_nonneg (psi_nonneg (-a)) (phiSlope_nonneg (-b))
  have h1 := mul_nonneg (psi_nonneg a) (phiSlope_nonneg b)
  dsimp [edgeRight]
  nlinarith

theorem edgeRight_le_neg_one (a b : ℝ) (ha : 1 ≤ |a|) (hb : |b| ≤ 1) :
    edgeRight a b ≤ -1 := by
  have hb0 : 1 ≤ phiSlope (-b) := by simpa only [phi_deriv, abs_neg] using phi_deriv_ge_one (-b) (by simpa using hb)
  have hb1 : 1 ≤ phiSlope b := by simpa only [phi_deriv] using phi_deriv_ge_one b hb
  have h0 := mul_nonneg (psi_nonneg (-a)) (phiSlope_nonneg (-b))
  have h1 := mul_nonneg (psi_nonneg a) (phiSlope_nonneg b)
  rcases le_or_gt 0 a with hapos | haneg
  · have hgate : 1 ≤ psi a := psi_ge_one (by simpa only [abs_of_nonneg hapos] using ha)
    have hp := mul_le_mul hgate hb1 (by norm_num : (0 : ℝ) ≤ 1) (psi_nonneg a)
    dsimp [edgeRight]
    nlinarith
  · have hgate : 1 ≤ psi (-a) := psi_ge_one (by simpa only [abs_of_neg haneg] using ha)
    have hp := mul_le_mul hgate hb0 (by norm_num : (0 : ℝ) ≤ 1) (psi_nonneg (-a))
    dsimp [edgeRight]
    nlinarith

theorem edge_hasFDerivAt {n : ℕ} (i : Fin n) (z : Space n) :
    HasFDerivAt (fun w : Space n => edge (w i.castSucc) (w i.succ))
      (edgeLeft (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜 := ℝ) i.castSucc +
        edgeRight (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜 := ℝ) i.succ) z := by
  have hp (t : ℝ) : HasDerivAt psi (deriv psi t) t := by rw [psi_deriv]; exact psi_hasDerivAt t
  have hi := (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).hasFDerivAt (x := z)
  have hj := (EuclideanSpace.proj (𝕜 := ℝ) i.succ).hasFDerivAt (x := z)
  have hm0 := (hp (-z i.castSucc)).hasFDerivAt.comp z hi.neg
  have hm1 := (phi_hasDerivAt (-z i.succ)).hasFDerivAt.comp z hj.neg
  have hp0 := (hp (z i.castSucc)).hasFDerivAt.comp z hi
  have hp1 := (phi_hasDerivAt (z i.succ)).hasFDerivAt.comp z hj
  convert (hm0.mul hm1).sub (hp0.mul hp1) using 1
  ext v
  simp [edgeLeft, edgeRight, ContinuousLinearMap.comp_apply]
  ring

theorem value_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (value n)
      ((-phiSlope (z 0)) • EuclideanSpace.proj (𝕜 := ℝ) 0 +
        ∑ i : Fin n, (edgeLeft (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜 := ℝ) i.castSucc +
          edgeRight (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜 := ℝ) i.succ)) z := by
  have h0 := ((phi_hasDerivAt (z 0)).hasFDerivAt.comp z
    (EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt).neg
  have hs := HasFDerivAt.sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => edge_hasFDerivAt i z)
  convert h0.add hs using 1
  ext v
  simp
  ring

theorem value_hasGradientAt (n : ℕ) (z : Space n) :
    HasGradientAt (value n) (gradientField n z) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert value_hasFDerivAt n z using 1
  ext v
  simp [InnerProductSpace.toDual_apply, gradientField, edgeGradient, inner_add_left,
    real_inner_smul_left, inner_basis, inner_sum, basis, mul_ite]

theorem actual_gradient (n : ℕ) (z : Space n) : gradient (value n) z = gradientField n z :=
  (value_hasGradientAt n z).gradient

theorem edgeGradient_apply {n : ℕ} (i : Fin n) (z : Space n) (j : Fin (n + 1)) :
    edgeGradient i z j =
      (if j = i.castSucc then edgeLeft (z i.castSucc) (z i.succ) else 0) +
      (if j = i.succ then edgeRight (z i.castSucc) (z i.succ) else 0) := by
  simp [edgeGradient, basis, smul_eq_mul, mul_ite]

theorem gradientField_apply (n : ℕ) (z : Space n) (j : Fin (n + 1)) :
    gradientField n z j = (if j = 0 then -phiSlope (z 0) else 0) +
      ∑ i : Fin n, edgeGradient i z j := by
  have hs : (∑ i : Fin n, edgeGradient i z) j = ∑ i : Fin n, edgeGradient i z j :=
    map_sum (EuclideanSpace.proj (𝕜 := ℝ) j) (fun i : Fin n => edgeGradient i z) Finset.univ
  simp [gradientField, basis, hs, smul_eq_mul, mul_ite]
  split_ifs <;> simp

theorem edgeGradient_coord_nonpos {n : ℕ} (i : Fin n) (z : Space n) (j : Fin (n + 1)) :
    edgeGradient i z j ≤ 0 := by
  rw [edgeGradient_apply]
  exact add_nonpos (by split_ifs <;> simp [edgeLeft_nonpos])
    (by split_ifs <;> simp [edgeRight_nonpos])

theorem gradient_coord_nonpos (n : ℕ) (z : Space n) (j : Fin (n + 1)) :
    gradient (value n) z j ≤ 0 := by
  rw [actual_gradient, gradientField_apply]
  exact add_nonpos (by split_ifs <;> simp [phiSlope_nonneg])
    (Finset.sum_nonpos (fun i _ => edgeGradient_coord_nonpos i z j))

theorem gradient_first_le (n : ℕ) (z : Space n) :
    gradient (value n) z 0 ≤ -phiSlope (z 0) := by
  rw [actual_gradient, gradientField_apply, if_pos rfl]
  have hs := Finset.sum_nonpos (fun (i : Fin n) (_ : i ∈ Finset.univ) => edgeGradient_coord_nonpos i z 0)
  linarith

theorem gradient_succ_le_incoming {n : ℕ} (z : Space n) (i : Fin n) :
    gradient (value n) z i.succ ≤ edgeRight (z i.castSucc) (z i.succ) := by
  classical
  rw [actual_gradient, gradientField_apply, if_neg (Fin.succ_ne_zero i), zero_add]
  have hterm : edgeGradient i z i.succ = edgeRight (z i.castSucc) (z i.succ) := by
    rw [edgeGradient_apply, if_neg, if_pos rfl, zero_add]
    intro he
    have hval := congrArg Fin.val he
    change i.val + 1 = i.val at hval
    omega
  rw [← hterm]
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun k => edgeGradient k z i.succ) (Finset.mem_univ i)
  have hs := Finset.sum_nonpos (fun (k : Fin n) (_ : k ∈ Finset.univ.erase i) =>
    edgeGradient_coord_nonpos k z i.succ)
  linarith

/-- Coordinate locality: an edge affects only its two adjacent coordinates. -/
theorem edgeGradient_coord_zero {n : ℕ} (i : Fin n) (z : Space n) (j : Fin (n + 1))
    (hleft : j ≠ i.castSucc) (hright : j ≠ i.succ) : edgeGradient i z j = 0 := by
  simp only [edgeGradient_apply, if_neg hleft, if_neg hright, add_zero]

/-- Robust zero-chain locality: when a coordinate and its predecessor remain
inside the inactive window, its actual gradient coordinate is exactly zero. -/
theorem gradient_coord_inactive {n : ℕ} (z : Space n) (i : Fin n)
    (hprev : |z i.castSucc| ≤ 1 / 2) (hself : |z i.succ| ≤ 1 / 2) :
    gradient (value n) z i.succ = 0 := by
  classical
  rw [actual_gradient, gradientField_apply, if_neg (Fin.succ_ne_zero i), zero_add]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hleft : i.succ = k.castSucc
  · have hk : |z k.castSucc| ≤ 1 / 2 := by rw [← hleft]; exact hself
    rw [edgeGradient_inactive k z hk]
    rfl
  by_cases hright : i.succ = k.succ
  · have hik : i = k := Fin.succ_injective n hright
    subst k
    rw [edgeGradient_inactive i z hprev]
    rfl
  · exact edgeGradient_coord_zero k z i.succ hleft hright

/-- The first under-threshold coordinate has a genuine gradient coordinate
at most minus one. The conclusion refers to the actual gradient. -/
theorem coordinate_endgame (n : ℕ) (z : Space n) (j : Fin (n + 1))
    (hj : |z j| < 1) (hprev : ∀ i : Fin (n + 1), i.val < j.val → 1 ≤ |z i|) :
    gradient (value n) z j ≤ -1 := by
  revert hj hprev
  refine Fin.cases ?_ (fun i => ?_) j
  · intro hj _
    have hφ : 1 ≤ phiSlope (z 0) := by
      simpa only [phi_deriv] using phi_deriv_ge_one (z 0) hj.le
    exact (gradient_first_le n z).trans (by linarith)
  · intro hj hprev
    have hi : 1 ≤ |z i.castSucc| := hprev i.castSucc (by simp)
    exact (gradient_succ_le_incoming z i).trans (edgeRight_le_neg_one _ _ hi hj.le)

theorem exists_gradient_coord_le_neg_one (n : ℕ) (z : Space n) (hlast : |z (Fin.last n)| < 1) :
    ∃ j : Fin (n + 1), gradient (value n) z j ≤ -1 := by
  classical
  let s : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => |z j| < 1)
  have hs : s.Nonempty := ⟨Fin.last n, by simp [s, hlast]⟩
  let j := s.min' hs
  have hjmem : j ∈ s := Finset.min'_mem s hs
  have hj : |z j| < 1 := (Finset.mem_filter.mp hjmem).2
  refine ⟨j, coordinate_endgame n z j hj ?_⟩
  intro i hi
  by_contra h
  have himem : i ∈ s := by simp [s, lt_of_not_ge h]
  have hji : j ≤ i := Finset.min'_le s i himem
  exact (not_lt_of_ge hji) hi

/-- The paper's zero-chain endgame: a small last coordinate forces a
nonstationary actual gradient, with a dimension-independent margin. -/
theorem endgame (n : ℕ) (z : Space n) (hlast : |z (Fin.last n)| < 1) :
    1 ≤ ‖gradient (value n) z‖ := by
  obtain ⟨j, hj⟩ := exists_gradient_coord_le_neg_one n z hlast
  have hc : |gradient (value n) z j| ≤ ‖gradient (value n) z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient (value n) z) j
  have ha := neg_abs_le (gradient (value n) z j)
  linarith


def chain (n : ℕ) (ℓ h : ℝ) : Space n → ℝ :=
  ZeroChainResidualScaled.scaled (value n) (ℓ*h^2) h

theorem chain_formula (n : ℕ) (ℓ h : ℝ) (z : Space n) :
    chain n ℓ h z = ℓ*h^2 * (-phi (z 0/h) + ∑ i : Fin n,
      (psi (-z i.castSucc/h)*phi (-z i.succ/h)-psi (z i.castSucc/h)*phi (z i.succ/h))) := by
  simp only [chain,ZeroChainResidualScaled.scaled,value,edge,PiLp.smul_apply,
    smul_eq_mul,div_eq_inv_mul,neg_mul,mul_neg]

theorem chain_gradient (n : ℕ) (ℓ h : ℝ) (hh : 0<h) (z : Space n) :
    gradient (chain n ℓ h) z=(ℓ*h) • gradient (value n) (h⁻¹ • z) := by
  rw [chain,ZeroChainResidualScaled.scaled_gradient
    ((value_contDiff n 1).differentiable (by norm_num))]
  congr 1
  field_simp
  ring

theorem chain_gradient_nonpos (n : ℕ) (ℓ h : ℝ) (hℓ : 0≤ℓ) (hh : 0<h)
    (z : Space n) (j : Fin (n+1)) : gradient (chain n ℓ h) z j≤0 := by
  rw [chain_gradient n ℓ h hh,PiLp.smul_apply,smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hℓ hh.le) (gradient_coord_nonpos n _ j)

theorem chain_endgame (n : ℕ) (ℓ h : ℝ) (hℓ : 0≤ℓ) (hh : 0<h)
    (z : Space n) (hlast : |z (Fin.last n)|<h) : ℓ*h≤‖gradient (chain n ℓ h) z‖ := by
  have hz : |(h⁻¹ • z) (Fin.last n)|<1 := by
    simp only [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hh)]
    exact (inv_mul_lt_iff₀ hh).mpr (by simpa using hlast)
  have hm := mul_le_mul_of_nonneg_left (endgame n (h⁻¹ • z) hz) (mul_nonneg hℓ hh.le)
  simpa only [chain_gradient n ℓ h hh,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hℓ hh.le),mul_one] using hm

theorem edge_rewrite (a b : ℝ) :
    edge a b = -evenGate a*phi b+(2*phi 0)*psi (-a) := by
  have he := phi_reflection b
  have hm := congrArg (fun x : ℝ => psi (-a)*x) he
  dsimp only at hm
  unfold edge evenGate
  nlinarith

end Bilevel.ChiBoundedChain
