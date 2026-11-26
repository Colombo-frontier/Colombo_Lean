import Bilevel.PolishedLiteralChain
import Bilevel.ChiBoundedChainMasks

/-! The literal one-sided selectors of eq:selectors, using the fixed
exponential activation and smooth tail masks. No capped-profile identity
is used in their support or uniqueness proof. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential

def selector (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  Fin.cases (tailMask 0 z) (fun j => psi (z j.castSucc)*tailMask j.succ z) i

def selectorDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  Fin.cases (maskDerivative 0 z) (fun j =>
    (deriv psi (z j.castSucc)*tailMask j.succ z) • EuclideanSpace.proj (𝕜:=ℝ) j.castSucc +
      psi (z j.castSucc) • maskDerivative j.succ z) i

theorem selector_nonneg (n : ℕ) (i : Fin (n+1)) (z : Space n) : 0 ≤ selector n i z := by
  refine Fin.cases (tailMask_range 0 z).1 (fun j => ?_) i
  exact mul_nonneg (psi_nonneg _) (tailMask_range _ _).1

theorem selector_le_exp_one (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    selector n i z ≤ Real.exp 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (tailMask_range 0 z).2.trans (Real.one_le_exp (by norm_num))
  · exact (mul_le_of_le_one_right (psi_nonneg _) (tailMask_range _ _).2).trans (psi_le_exp_one _)

theorem selector_contDiff (n k : ℕ) (i : Fin (n+1)) : ContDiff ℝ k (selector n i) := by
  refine Fin.cases (tailMask_contDiff 0 k) (fun j => ?_) i
  exact (psi_contDiff.comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff).mul
    (tailMask_contDiff j.succ k)

theorem selector_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (selector n i) (selectorDerivative n i z) z := by
  refine Fin.cases (tailMask_hasFDerivAt 0 z) (fun j => ?_) i
  have hd := ((psi_contDiff (k:=1)).differentiable (by norm_num) (z j.castSucc)).hasDerivAt
  have he := hd.hasFDerivAt.comp z (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).hasFDerivAt
  convert he.mul (tailMask_hasFDerivAt j.succ z) using 1
  ext v
  simp [selectorDerivative, ContinuousLinearMap.comp_apply]
  ring

theorem selector_mask_ne_zero {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hi : selector n i z ≠ 0) : tailMask i z ≠ 0 := by
  revert hi
  refine Fin.cases (fun h => h) (fun j h => (mul_ne_zero_iff.mp h).2) i

theorem selector_active_tail_small {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hi : selector n i z ≠ 0) (j : Fin (n+1)) (hij : i ≤ j) : |z j| < 1/2 := by
  by_contra h
  exact selector_mask_ne_zero i z hi
    (tailMask_zero_of_large_coordinate i j z hij (le_of_not_gt h))

theorem selector_succ_predecessor {n : ℕ} (i : Fin n) (z : Space n)
    (hi : selector n i.succ z ≠ 0) : 1/2 < z i.castSucc := by
  by_contra h
  apply hi
  simp only [selector,Fin.cases_succ,psi_zero (le_of_not_gt h),zero_mul]

theorem selector_ordered_incompatible {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i < j) (hi : selector n i z ≠ 0) (hj : selector n j z ≠ 0) : False := by
  revert hij hj
  refine Fin.cases ?_ (fun k hlt hsucc => ?_) j
  · intro hlt _
    exact (not_lt_of_ge (Fin.zero_le _)) hlt
  · have hpred := selector_succ_predecessor k z hsucc
    have htail := selector_active_tail_small i z hi k.castSucc (by
      apply Fin.le_iff_val_le_val.mpr
      have hv : i.val < k.val+1 := hlt
      change i.val ≤ k.val
      omega)
    have hval := le_abs_self (z k.castSucc)
    linarith

theorem selector_unique {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hi : selector n i z ≠ 0) (hj : selector n j z ≠ 0) : i=j := by
  rcases lt_trichotomy i j with h|h|h
  · exact False.elim (selector_ordered_incompatible i j z h hi hj)
  · exact h
  · exact False.elim (selector_ordered_incompatible j i z h hj hi)

theorem selector_sum_le_exp_one (n : ℕ) (z : Space n) :
    ∑ i : Fin (n+1), selector n i z ≤ Real.exp 1 := by
  classical
  by_cases h : ∃ i,selector n i z ≠ 0
  · obtain ⟨i,hi⟩ := h
    have hs : ∑ j : Fin (n+1),selector n j z=selector n i z := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_contra hj
        exact hji (selector_unique j i z hj hi)
      · simp
    rw [hs]
    exact selector_le_exp_one n i z
  · have hz : ∀ i,selector n i z=0 := by simpa only [not_exists,not_not] using h
    simp only [hz,Finset.sum_const_zero]
    exact (Real.exp_pos _).le

def residualTerm (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ := -selector n i z*phi (z i)

theorem residualTerm_nonpos (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    residualTerm n i z ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (selector_nonneg n i z)) (phi_nonneg _)

theorem residualTerm_contDiff (n k : ℕ) (i : Fin (n+1)) :
    ContDiff ℝ k (residualTerm n i) :=
  (selector_contDiff n k i).neg.mul ((phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)

def residualTermDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  (-phi (z i)) • selectorDerivative n i z +
    (-selector n i z*phiSlope (z i)) • EuclideanSpace.proj (𝕜:=ℝ) i

theorem residualTerm_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (residualTerm n i) (residualTermDerivative n i z) z := by
  convert (selector_hasFDerivAt n i z).neg.mul
    ((phi_hasDerivAt (z i)).hasFDerivAt.comp z (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt) using 1
  ext v
  simp [residualTermDerivative, ContinuousLinearMap.comp_apply]
  ring

theorem residualTerm_abs_bound (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    |residualTerm n i z| ≤ gaussianBound*selector n i z := by
  rw [residualTerm, abs_mul, abs_neg, abs_of_nonneg (selector_nonneg n i z),
    abs_of_nonneg (phi_nonneg _)]
  simpa only [gaussianBound, mul_comm] using mul_le_mul_of_nonneg_left (phi_bounded (z i)) (selector_nonneg n i z)


theorem selectorDerivative_zero_of_zero {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hi : selector n i z=0) : selectorDerivative n i z=0 := by
  have hm : IsLocalMin (selector n i) z := by
    apply Filter.Eventually.of_forall
    intro w
    rw [hi]
    exact selector_nonneg n i w
  exact hm.hasFDerivAt_eq_zero (selector_hasFDerivAt n i z)

end Bilevel.PolishedLiteral
