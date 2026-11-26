import Smoothness2601.ChainProfiles
import Smoothness2601.ConcreteFrontier

/-! The extensive source chain, with its actual Fréchet derivative. The
amplitude parameter is left explicit; choosing a larger fixed amplitude for
the existential hard construction is distinguished from the source's sharper
particular M_ch calibration. -/
noncomputable section
namespace Smoothness2601.ExtensiveChain
open Cutoffs ChainProfiles Finset
open scoped BigOperators RealInnerProductSpace Topology ContDiff

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

def link (M x y : ℝ) : ℝ := psi (-x) * profile M (-y) - psi x * profile M y

def extensive (M : ℝ) {n : ℕ} (z : Space n) : ℝ :=
  -profile M (z 0) + ∑ i : Fin n, link M (z i.castSucc) (z i.succ)

def leftSlope (M x y : ℝ) : ℝ :=
  -deriv psi (-x) * profile M (-y) - deriv psi x * profile M y

def rightSlope (M x y : ℝ) : ℝ := -gate x * deriv (profile M) y

def linkDerivative (M : ℝ) {n : ℕ} (z : Space n) (i : Fin n) : Space n →L[ℝ] ℝ :=
  leftSlope M (z i.castSucc) (z i.succ) • EuclideanSpace.proj i.castSucc +
    rightSlope M (z i.castSucc) (z i.succ) • EuclideanSpace.proj i.succ

def extensiveDerivative (M : ℝ) {n : ℕ} (z : Space n) : Space n →L[ℝ] ℝ :=
  -(deriv (profile M) (z 0)) • EuclideanSpace.proj 0 + ∑ i : Fin n, linkDerivative M z i

theorem link_hasFDerivAt (M : ℝ) {n : ℕ} (z : Space n) (i : Fin n) :
    HasFDerivAt (fun x : Space n => link M (x i.castSucc) (x i.succ)) (linkDerivative M z i) z := by
  have hp (j : Fin (n + 1)) := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt (x := z)
  have hψ (t : ℝ) := ((psi_contDiff 1).differentiable (by norm_num) t).hasDerivAt
  have hr (t : ℝ) := (profile_hasDerivAt M t).differentiableAt.hasDerivAt
  have hnψ := (hψ (-z i.castSucc)).comp_hasFDerivAt z (hp i.castSucc).neg
  have hnr := (hr (-z i.succ)).comp_hasFDerivAt z (hp i.succ).neg
  have hψp := (hψ (z i.castSucc)).comp_hasFDerivAt z (hp i.castSucc)
  have hrp := (hr (z i.succ)).comp_hasFDerivAt z (hp i.succ)
  convert (hnψ.mul hnr).sub (hψp.mul hrp) using 1
  ext v
  simp [linkDerivative, leftSlope, rightSlope, gate, profile_deriv_even]
  ring

theorem extensive_hasFDerivAt (M : ℝ) {n : ℕ} (z : Space n) :
    HasFDerivAt (extensive M) (extensiveDerivative M z) z := by
  have h0 := ((profile_hasDerivAt M (z 0)).differentiableAt.hasDerivAt.comp_hasFDerivAt z
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).hasFDerivAt).neg
  have hs := HasFDerivAt.sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => link_hasFDerivAt M z i)
  convert h0.add hs using 1
  ext v
  simp [extensiveDerivative]

theorem extensive_contDiff (M : ℝ) (n : ℕ) : ContDiff ℝ ∞ (extensive M (n := n)) := by
  have hp (i : Fin (n + 1)) : ContDiff ℝ ∞ (fun z : Space n => z i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  unfold extensive link
  apply ContDiff.add ((profile_smooth M).comp (hp 0)).neg
  apply ContDiff.sum
  intro i _
  exact (((psi_contDiff ⊤).comp (hp i.castSucc).neg).mul
    ((profile_smooth M).comp (hp i.succ).neg)).sub
    (((psi_contDiff ⊤).comp (hp i.castSucc)).mul ((profile_smooth M).comp (hp i.succ)))

theorem gradient_coordinate_of_hasFDerivAt {n : ℕ} {f : Space n → ℝ}
    {D : Space n →L[ℝ] ℝ} {z : Space n} (hf : HasFDerivAt f D z) (k : Fin (n + 1)) :
    gradient f z k = D (EuclideanSpace.single k 1) := by
  have h := hf.differentiableAt.hasGradientAt.hasFDerivAt.unique hf
  have he := congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single k 1)) h
  simpa [InnerProductSpace.toDual_apply, EuclideanSpace.inner_single_right] using he

def selector {n : ℕ} (j k : Fin (n + 1)) : ℝ := if j = k then 1 else 0

theorem extensive_gradient_coordinate (M : ℝ) {n : ℕ} (z : Space n) (k : Fin (n + 1)) :
    gradient (extensive M) z k =
      -deriv (profile M) (z 0) * selector 0 k +
        ∑ i : Fin n, (leftSlope M (z i.castSucc) (z i.succ) * selector i.castSucc k +
          rightSlope M (z i.castSucc) (z i.succ) * selector i.succ k) := by
  rw [gradient_coordinate_of_hasFDerivAt (extensive_hasFDerivAt M z) k]
  simp [extensiveDerivative, linkDerivative, selector, EuclideanSpace.single_apply]
  split_ifs <;> simp

theorem leftSlope_nonpos {M : ℝ} (hM : 0 ≤ M) (x y : ℝ) : leftSlope M x y ≤ 0 := by
  have h1 := mul_nonneg (psi_deriv_nonneg (-x)) (profile_nonneg hM (-y))
  have h2 := mul_nonneg (psi_deriv_nonneg x) (profile_nonneg hM y)
  unfold leftSlope
  nlinarith

theorem rightSlope_nonpos {M : ℝ} (hM : 0 ≤ M) (x y : ℝ) : rightSlope M x y ≤ 0 := by
  unfold rightSlope
  have h := mul_nonneg (gate_nonneg x) (profile_deriv_nonneg hM y)
  nlinarith

theorem selector_nonneg {n : ℕ} (i k : Fin (n + 1)) : 0 ≤ selector i k := by
  unfold selector
  split_ifs <;> norm_num

theorem link_coordinate_nonpos {M : ℝ} (hM : 0 ≤ M) {n : ℕ} (z : Space n)
    (i : Fin n) (k : Fin (n + 1)) :
    leftSlope M (z i.castSucc) (z i.succ) * selector i.castSucc k +
      rightSlope M (z i.castSucc) (z i.succ) * selector i.succ k ≤ 0 :=
  add_nonpos (mul_nonpos_of_nonpos_of_nonneg (leftSlope_nonpos hM _ _) (selector_nonneg _ _))
    (mul_nonpos_of_nonpos_of_nonneg (rightSlope_nonpos hM _ _) (selector_nonneg _ _))

theorem extensive_gradient_nonpos {M : ℝ} (hM : 0 ≤ M) {n : ℕ} (z : Space n) (k : Fin (n + 1)) :
    gradient (extensive M) z k ≤ 0 := by
  rw [extensive_gradient_coordinate]
  exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (profile_deriv_nonneg hM _))
    (selector_nonneg _ _)) (sum_nonpos fun i _ => link_coordinate_nonpos hM z i k)

theorem extensive_frontier_coordinate {M : ℝ} (hM : 0 ≤ M) {n : ℕ} (z : Space n)
    (k : Fin (n + 1)) (hfirst : ∀ j : Fin (n + 1), j < k → 1 ≤ |z j|) :
    gradient (extensive M) z k ≤ -deriv (profile M) (z k) := by
  induction k using Fin.cases with
  | zero =>
    rw [extensive_gradient_coordinate]
    have hs := sum_nonpos (fun i (_ : i ∈ (univ : Finset (Fin n))) => link_coordinate_nonpos hM z i 0)
    have hsel : selector (0 : Fin (n + 1)) 0 = 1 := by simp [selector]
    rw [hsel, mul_one]
    linarith
  | succ j =>
    have hprev : 1 ≤ |z j.castSucc| := hfirst j.castSucc (by exact_mod_cast Nat.lt_succ_self j.val)
    have hr : rightSlope M (z j.castSucc) (z j.succ) = -deriv (profile M) (z j.succ) := by
      simp only [rightSlope, gate_one hprev, neg_mul, one_mul]
    let f : Fin n → ℝ := fun i =>
      leftSlope M (z i.castSucc) (z i.succ) * selector i.castSucc j.succ +
        rightSlope M (z i.castSucc) (z i.succ) * selector i.succ j.succ
    have hsum : ∑ i, f i ≤ f j := by
      have h := sum_nonpos (fun i (_ : i ∈ (univ.erase j : Finset (Fin n))) => link_coordinate_nonpos hM z i j.succ)
      have he := sum_erase_add univ f (mem_univ j)
      change ∑ i ∈ univ.erase j, f i ≤ 0 at h
      linarith
    have hsel : selector j.castSucc j.succ = 0 := by
      apply if_neg
      intro he
      have := congrArg Fin.val he
      simp at this
    have hf : f j = -deriv (profile M) (z j.succ) := by
      change leftSlope M (z j.castSucc) (z j.succ) * selector j.castSucc j.succ +
        rightSlope M (z j.castSucc) (z j.succ) * selector j.succ j.succ = _
      rw [hsel, mul_zero, zero_add, show selector j.succ j.succ = 1 from by simp [selector], mul_one, hr]
    have hb : -deriv (profile M) (z 0) * selector 0 j.succ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (profile_deriv_nonneg hM _)) (selector_nonneg _ _)
    rw [extensive_gradient_coordinate]
    change -deriv (profile M) (z 0) * selector 0 j.succ + ∑ i, f i ≤ _
    rw [hf] at hsum
    linarith

theorem extensive_gradient_zero_near {M : ℝ} {n : ℕ} (z : Space n) (k : Fin (n + 1))
    (hk : |z k| ≤ 1/16) : gradient (extensive M) z k = 0 := by
  rw [extensive_gradient_coordinate]
  have hψp : deriv psi (z k) = 0 := psi_deriv_zero (by have := (abs_le.mp hk).2; linarith)
  have hψm : deriv psi (-z k) = 0 := psi_deriv_zero (by have := (abs_le.mp hk).1; linarith)
  have hr : deriv (profile M) (z k) = 0 := profile_deriv_zero_near M hk
  have hb : -deriv (profile M) (z 0) * selector 0 k = 0 := by
    by_cases h : (0 : Fin (n + 1)) = k
    · subst k
      simp [selector, hr]
    · simp [selector, h]
  rw [hb, zero_add]
  apply sum_eq_zero
  intro i _
  have hleft : leftSlope M (z i.castSucc) (z i.succ) * selector i.castSucc k = 0 := by
    by_cases h : i.castSucc = k
    · unfold leftSlope
      rw [h, hψp, hψm]
      simp
    · simp [selector, h]
  have hright : rightSlope M (z i.castSucc) (z i.succ) * selector i.succ k = 0 := by
    by_cases h : i.succ = k
    · unfold rightSlope
      rw [h, hr]
      simp
    · simp [selector, h]
  rw [hleft, hright, add_zero]

end Smoothness2601.ExtensiveChain
