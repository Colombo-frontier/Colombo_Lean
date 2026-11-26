import Smoothness2601.ChainNonstationary

/-! Exact prefix locality for the actual extensive and bounded potentials. -/
noncomputable section
namespace Smoothness2601.ExtensiveChain
open Cutoffs ChainProfiles Finset Filter
open scoped BigOperators RealInnerProductSpace Topology ContDiff

theorem leftSlope_zero_near (M x y : ℝ) (hx : |x| ≤ 1/16) : leftSlope M x y = 0 := by
  have h1 : deriv psi x = 0 := psi_deriv_zero (by have := (abs_le.mp hx).2; linarith)
  have h2 : deriv psi (-x) = 0 := psi_deriv_zero (by have := (abs_le.mp hx).1; linarith)
  simp [leftSlope,h1,h2]

theorem rightSlope_zero_near (M x y : ℝ) (hy : |y| ≤ 1/16) : rightSlope M x y = 0 := by
  simp [rightSlope,profile_deriv_zero_near M hy]

theorem extensive_gradient_prefix_locality (M : ℝ) {n : ℕ} (k : ℕ) (z w : Space n)
    (heq : ∀ i : Fin (n+1), i.val < k → z i = w i)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |z i| ≤ 1/16 ∧ |w i| ≤ 1/16) :
    gradient (extensive M) z = gradient (extensive M) w := by
  have hbase : deriv (profile M) (z 0) = deriv (profile M) (w 0) := by
    by_cases h : (0 : ℕ) < k
    · rw [heq 0 h]
    · have ht := htail 0 (by simpa using le_of_not_gt h)
      rw [profile_deriv_zero_near M ht.1,profile_deriv_zero_near M ht.2]
  have hl (i : Fin n) : leftSlope M (z i.castSucc) (z i.succ) =
      leftSlope M (w i.castSucc) (w i.succ) := by
    by_cases hc : i.castSucc.val < k
    · have hr : profile M (z i.succ) = profile M (w i.succ) := by
        by_cases hs : i.succ.val < k
        · rw [heq i.succ hs]
        · exact profile_constant_near M (htail i.succ (le_of_not_gt hs)).1 (htail i.succ (le_of_not_gt hs)).2
      have hrn : profile M (-z i.succ) = profile M (-w i.succ) := by
        by_cases hs : i.succ.val < k
        · rw [heq i.succ hs]
        · exact profile_constant_near M (by simpa using (htail i.succ (le_of_not_gt hs)).1)
            (by simpa using (htail i.succ (le_of_not_gt hs)).2)
      simp only [leftSlope,heq i.castSucc hc,hr,hrn]
    · rw [leftSlope_zero_near M _ _ (htail i.castSucc (le_of_not_gt hc)).1,
        leftSlope_zero_near M _ _ (htail i.castSucc (le_of_not_gt hc)).2]
  have hr (i : Fin n) : rightSlope M (z i.castSucc) (z i.succ) =
      rightSlope M (w i.castSucc) (w i.succ) := by
    by_cases hs : i.succ.val < k
    · have hc : i.castSucc.val < k := by simpa using Nat.lt_of_succ_lt hs
      rw [heq i.castSucc hc,heq i.succ hs]
    · rw [rightSlope_zero_near M _ _ (htail i.succ (le_of_not_gt hs)).1,
        rightSlope_zero_near M _ _ (htail i.succ (le_of_not_gt hs)).2]
  ext j
  simp only [extensive_gradient_coordinate,hbase,hl,hr]

theorem extensive_gradient_supported_prefix (M : ℝ) {n : ℕ} (k : ℕ) (z : Space n)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |z i| ≤ 1/16) :
    ∀ i : Fin (n+1), k ≤ i.val → gradient (extensive M) z i = 0 :=
  fun i hi => extensive_gradient_zero_near z i (htail i hi)

def throughProjection {n : ℕ} (k : Fin (n+1)) : Space n →L[ℝ] Space n :=
  PrefixProducts.diagonalOperator fun i => if i ≤ k then 1 else 0

theorem throughProjection_apply {n : ℕ} (k i : Fin (n+1)) (z : Space n) :
    throughProjection k z i = if i ≤ k then z i else 0 := by
  change (if i ≤ k then 1 else 0)*z i = _
  split_ifs <;> simp

def frontierThrough {n : ℕ} (k : Fin (n+1)) (z : Space n) : ℝ :=
  -∑ i ∈ univ.filter (fun i => i ≤ k), BoundedFrontier.summand gate bump i z

theorem frontierThrough_contDiff {n : ℕ} (k : Fin (n+1)) : ContDiff ℝ ∞ (frontierThrough k) := by
  unfold frontierThrough BoundedFrontier.summand BoundedFrontier.prefixValue
  apply ContDiff.neg
  apply ContDiff.sum
  intro i _
  apply ContDiff.mul
  · apply contDiff_prod
    intro j _
    exact (gate_contDiff ⊤).comp (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  · exact (bump_contDiff ⊤).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem frontierThrough_projected {n : ℕ} (k : Fin (n+1)) (z : Space n) :
    frontierThrough k z = frontierThrough k (throughProjection k z) := by
  unfold frontierThrough
  congr 1
  apply sum_congr rfl
  intro i hi
  have hik := (mem_filter.mp hi).2
  unfold BoundedFrontier.summand BoundedFrontier.prefixValue
  rw [throughProjection_apply,if_pos hik]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [throughProjection_apply,if_pos ((BoundedFrontier.mem_prefixSet.mp hj).le.trans hik)]

theorem frontier_eventually_through {n : ℕ} (k : Fin (n+1)) (z : Space n) (hk : |z k| ≤ 1/16) :
    Cutoffs.frontier =ᶠ[𝓝 z] frontierThrough k := by
  have hnear : ∀ᶠ x : Space n in 𝓝 z, |x k| < 1/2 :=
    (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.abs continuous_const).mem_nhds
      (show |z k| < 1/2 by linarith)
  filter_upwards [hnear] with x hx
  unfold Cutoffs.frontier BoundedFrontier.frontier frontierThrough
  congr 1
  symm
  apply sum_subset (filter_subset _ _)
  intro i _ hi
  have hki : k < i := by simpa using hi
  simp [BoundedFrontier.summand,BoundedFrontier.prefix_zero_of_earlier hki (gate_zero hx.le)]

theorem frontierThrough_derivative {n : ℕ} (k : Fin (n+1)) (z : Space n) :
    HasFDerivAt (frontierThrough k)
      ((fderiv ℝ (frontierThrough k) (throughProjection k z)).comp (throughProjection k)) z := by
  have hd := ((frontierThrough_contDiff k).differentiable (by norm_num) (throughProjection k z)).hasFDerivAt
  have h := hd.comp z (throughProjection k).hasFDerivAt
  convert h using 1
  exact funext (frontierThrough_projected k)

theorem frontier_prefix_locality {n : ℕ} (k : Fin (n+1)) (z w : Space n)
    (hkz : |z k| ≤ 1/16) (hkw : |w k| ≤ 1/16)
    (heq : ∀ i : Fin (n+1), i ≤ k → z i = w i) :
    Cutoffs.frontier z = Cutoffs.frontier w ∧
      gradient Cutoffs.frontier z = gradient Cutoffs.frontier w := by
  have hp : throughProjection k z = throughProjection k w := by
    ext i
    simp only [throughProjection_apply]
    split_ifs with hi
    · exact heq i hi
    · rfl
  have hz := frontier_eventually_through k z hkz
  have hw := frontier_eventually_through k w hkw
  constructor
  · rw [hz.eq_of_nhds,hw.eq_of_nhds,frontierThrough_projected k z,frontierThrough_projected k w,hp]
  · rw [hz.gradient_eq,hw.gradient_eq]
    apply (InnerProductSpace.toDual ℝ (Space n)).injective
    have hd1 := (frontierThrough_derivative k z).differentiableAt.hasGradientAt.hasFDerivAt.unique (frontierThrough_derivative k z)
    have hd2 := (frontierThrough_derivative k w).differentiableAt.hasGradientAt.hasFDerivAt.unique (frontierThrough_derivative k w)
    rw [hd1,hd2,hp]

theorem frontier_gradient_supported_through {n : ℕ} (k : Fin (n+1)) (z : Space n)
    (hk : |z k| ≤ 1/16) (j : Fin (n+1)) (hj : k < j) : gradient Cutoffs.frontier z j = 0 := by
  rw [(frontier_eventually_through k z hk).gradient_eq,
    gradient_coordinate_of_hasFDerivAt (frontierThrough_derivative k z) j,ContinuousLinearMap.comp_apply]
  have hp : throughProjection k (EuclideanSpace.single j 1) = 0 := by
    ext i
    rw [throughProjection_apply]
    split_ifs with hi
    · have hij : i ≠ j := ne_of_lt (hi.trans_lt hj)
      simp [EuclideanSpace.single_apply,hij,Ne.symm hij]
    · simp
  rw [hp,map_zero]

end Smoothness2601.ExtensiveChain
