import Bilevel.ZeroChainProfiles
import Bilevel.ZeroChainPotential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The actual finite-dimensional zero chain

There are `n+1` coordinates and `n` nearest-neighbor edges. This is exactly the
manuscript's first term and its subsequent two-coordinate summands.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChain
open ZeroChainProfiles ZeroChainPotential

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

def phiBound : ℝ := Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi)

theorem phiBound_nonneg : 0 ≤ phiBound := by unfold phiBound; positivity

theorem edge_abs_bound (a b : ℝ) : |edge a b| ≤ 2 * Real.exp 1 * phiBound := by
  have h0 := mul_le_mul (psi_le_exp_one (-a)) (phi_bounded (-b))
    (phi_nonneg (-b)) (Real.exp_pos 1).le
  have h1 := mul_le_mul (psi_le_exp_one a) (phi_bounded b)
    (phi_nonneg b) (Real.exp_pos 1).le
  have ht := abs_sub (psi (-a) * phi (-b)) (psi a * phi b)
  rw [abs_of_nonneg (mul_nonneg (psi_nonneg (-a)) (phi_nonneg (-b))),
    abs_of_nonneg (mul_nonneg (psi_nonneg a) (phi_nonneg b))] at ht
  dsimp [edge, phiBound]
  linarith

theorem value_abs_bound (n : ℕ) (z : Space n) :
    |value n z| ≤ phiBound + (n : ℝ) * (2 * Real.exp 1 * phiBound) := by
  have hs : |∑ i : Fin n, edge (z i.castSucc) (z i.succ)| ≤
      (n : ℝ) * (2 * Real.exp 1 * phiBound) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, (2 * Real.exp 1 * phiBound) :=
        Finset.sum_le_sum (fun i _ => edge_abs_bound _ _)
      _ = _ := by simp
  have hb : |-phi (z 0)| ≤ phiBound := by
    simpa only [abs_neg, abs_of_nonneg (phi_nonneg (z 0))] using phi_bounded (z 0)
  exact (abs_add _ _).trans (add_le_add hb hs)

theorem value_zero (n : ℕ) : value n 0 = -phi 0 := by
  have hp : psi 0 = 0 := psi_zero_of_le (by norm_num)
  simp [value, edge, hp]

/-- A genuine finite-gap certificate, linear in the number of coordinates. -/
theorem initial_gap_bound (n : ℕ) (z : Space n) :
    value n 0 - value n z ≤
      (1 + 2 * Real.exp 1) * phiBound * (n + 1 : ℕ) := by
  have ha := value_abs_bound n z
  have hb := neg_abs_le (value n z)
  have h0 := phi_nonneg 0
  have hB := phiBound_nonneg
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  rw [value_zero]
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg n) hB, mul_nonneg he hB]

theorem sum_injective_indicator_abs_le {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (j : κ) (a : ι → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (ha : ∀ i, |a i| ≤ A) :
    |∑ i, if j = f i then a i else 0| ≤ A := by
  classical
  by_cases h : ∃ i, j = f i
  · obtain ⟨i, rfl⟩ := h
    have he : ∀ k, f i = f k ↔ k = i := fun k =>
      ⟨fun h => (hf h).symm, fun h => by rw [h]⟩
    simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true] using ha i
  · have he : ∀ i, j ≠ f i := by simpa using h
    simpa only [if_neg (he _), Finset.sum_const_zero, abs_zero] using hA

theorem edgeLeft_abs_bound (K : ℝ) (hK : 0 ≤ K) (hpsi : ∀ t, |deriv psi t| ≤ K)
    (a b : ℝ) : |edgeLeft a b| ≤ 2 * K * phiBound := by
  have h0 := mul_le_mul (hpsi (-a)) (phi_bounded (-b)) (phi_nonneg (-b)) hK
  have h1 := mul_le_mul (hpsi a) (phi_bounded b) (phi_nonneg b) hK
  have ht := abs_sub (-deriv psi (-a) * phi (-b)) (deriv psi a * phi b)
  simp only [abs_mul, abs_neg, abs_of_nonneg (phi_nonneg _)] at ht
  dsimp [edgeLeft, phiBound]
  linarith

theorem edgeRight_abs_bound (a b : ℝ) :
    |edgeRight a b| ≤ 2 * Real.exp 1 * Real.sqrt (Real.exp 1) := by
  have hs (t : ℝ) : phiSlope t ≤ Real.sqrt (Real.exp 1) := by
    simpa only [phi_deriv, abs_of_nonneg (phiSlope_nonneg t)] using phi_first_bound t
  have h0 := mul_le_mul (psi_le_exp_one (-a)) (hs (-b)) (phiSlope_nonneg (-b)) (Real.exp_pos 1).le
  have h1 := mul_le_mul (psi_le_exp_one a) (hs b) (phiSlope_nonneg b) (Real.exp_pos 1).le
  have ht := abs_sub (-psi (-a) * phiSlope (-b)) (psi a * phiSlope b)
  simp only [abs_mul, abs_neg, abs_of_nonneg (phiSlope_nonneg _),
    abs_of_nonneg (psi_nonneg _)] at ht
  dsimp [edgeRight]
  linarith

/-- The infinity-norm gradient bound is independent of the chain length:
each coordinate receives at most one incoming and one outgoing edge. -/
theorem coordinate_gradient_uniform_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ (n : ℕ) (z : Space n) (j : Fin (n + 1)), |gradient (value n) z j| ≤ B := by
  obtain ⟨K, hK, hpsi⟩ := psi_common_bound
  have hψ : ∀ t, |deriv psi t| ≤ K := by
    intro t
    simpa only [Fin.val_one, iteratedDeriv_one] using hpsi 1 t
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hB := phiBound_nonneg
  refine ⟨Real.sqrt (Real.exp 1) + 2 * K * phiBound +
    2 * Real.exp 1 * Real.sqrt (Real.exp 1), by positivity, ?_⟩
  intro n z j
  rw [actual_gradient, gradientField_apply]
  simp_rw [edgeGradient_apply, Finset.sum_add_distrib]
  have h0 : |if j = 0 then -phiSlope (z 0) else 0| ≤ Real.sqrt (Real.exp 1) := by
    split_ifs
    · simpa only [abs_neg, phi_deriv] using phi_first_bound (z 0)
    · simp only [abs_zero]
      positivity
  have hleft := sum_injective_indicator_abs_le Fin.castSucc (Fin.castSucc_injective n) j
    (fun i => edgeLeft (z i.castSucc) (z i.succ)) (2 * K * phiBound) (by positivity)
    (fun i => edgeLeft_abs_bound K hK0 hψ _ _)
  have hright := sum_injective_indicator_abs_le Fin.succ (Fin.succ_injective n) j
    (fun i => edgeRight (z i.castSucc) (z i.succ))
    (2 * Real.exp 1 * Real.sqrt (Real.exp 1)) (by positivity) (fun i => edgeRight_abs_bound _ _)
  calc
    _ ≤ |if j = 0 then -phiSlope (z 0) else 0| +
        (|∑ i : Fin n, if j = i.castSucc then edgeLeft (z i.castSucc) (z i.succ) else 0| +
        |∑ i : Fin n, if j = i.succ then edgeRight (z i.castSucc) (z i.succ) else 0|) :=
      (abs_add _ _).trans (add_le_add_left (abs_add _ _) _)
    _ ≤ Real.sqrt (Real.exp 1) + ((2 * K * phiBound) +
        (2 * Real.exp 1 * Real.sqrt (Real.exp 1))) := add_le_add h0 (add_le_add hleft hright)
    _ = _ := by ring

end Bilevel.ZeroChain
