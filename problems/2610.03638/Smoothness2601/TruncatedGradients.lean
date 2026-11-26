import Smoothness2601.ChainLocality
import Smoothness2601.RadialWrapper

/-! Derivatives of the actual truncated composite functions. Artificial tail
coordinates are constants, so no unexposed gradient components are retained. -/
noncomputable section
namespace Smoothness2601.ExtensiveChain
open Cutoffs ChainProfiles Finset
open scoped BigOperators RealInnerProductSpace

def cutProjection {n : ℕ} (k : ℕ) : Space n →L[ℝ] Space n :=
  PrefixProducts.diagonalOperator fun i => if i.val < k then 1 else 0

theorem cutProjection_apply {n : ℕ} (k : ℕ) (z : Space n) (i : Fin (n+1)) :
    cutProjection k z i = if i.val < k then z i else 0 := by
  change (if i.val < k then 1 else 0)*z i = _
  split_ifs <;> simp

theorem cutProjection_selfadjoint {n : ℕ} (k : ℕ) (z v : Space n) :
    ⟪cutProjection k z,v⟫ = ⟪z,cutProjection k v⟫ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,cutProjection_apply]
  apply sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem cutProjection_of_support {n : ℕ} (k : ℕ) (z : Space n)
    (hz : ∀ i : Fin (n+1), k ≤ i.val → z i = 0) : cutProjection k z = z := by
  ext i
  rw [cutProjection_apply]
  split_ifs with hi
  · rfl
  · exact (hz i (le_of_not_gt hi)).symm

theorem cut_comp_hasGradientAt {n : ℕ} (k : ℕ) {f : Space n → ℝ} {g : Space n}
    {z : Space n} (hf : HasGradientAt f g (cutProjection k z)) :
    HasGradientAt (fun x => f (cutProjection k x)) (cutProjection k g) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hf.hasFDerivAt.comp z (cutProjection k).hasFDerivAt using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply]
  exact cutProjection_selfadjoint k g v

theorem extensive_truncated_gradient (M : ℝ) {n : ℕ} (k : ℕ) (z : Space n)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |z i| ≤ 1/16) :
    gradient (fun x : Space n => extensive M (cutProjection k x)) z = gradient (extensive M) z := by
  have he := extensive_gradient_prefix_locality M k z (cutProjection k z)
    (fun i hi => by rw [cutProjection_apply,if_pos hi])
    (fun i hi => ⟨htail i hi,by rw [cutProjection_apply,if_neg (not_lt.mpr hi)]; norm_num⟩)
  rw [(cut_comp_hasGradientAt k (extensive_hasFDerivAt M (cutProjection k z)).differentiableAt.hasGradientAt).gradient,
    ← he]
  exact cutProjection_of_support k _ (extensive_gradient_supported_prefix M k z htail)

theorem frontier_truncated_value_gradient {n : ℕ} (k : ℕ) (z : Space n)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |z i| ≤ 1/16) :
    Cutoffs.frontier (cutProjection (k+1) z) = Cutoffs.frontier z ∧
    gradient (fun x : Space n => Cutoffs.frontier (cutProjection (k+1) x)) z = gradient Cutoffs.frontier z := by
  by_cases hk : k < n+1
  · let j : Fin (n+1) := ⟨k,hk⟩
    have heq : ∀ i : Fin (n+1), i ≤ j → z i = cutProjection (k+1) z i := by
      intro i hi
      rw [cutProjection_apply,if_pos (by have : i.val ≤ k := hi; omega)]
    have hjz := htail j (le_refl k)
    have hjw : |cutProjection (k+1) z j| ≤ 1/16 := by rw [← heq j le_rfl]; exact hjz
    have hh := frontier_prefix_locality j z (cutProjection (k+1) z) hjz hjw heq
    refine ⟨hh.1.symm,?_⟩
    rw [(cut_comp_hasGradientAt (k+1) (actual_frontier_differentiable (cutProjection (k+1) z)).1.hasGradientAt).gradient,
      ← hh.2]
    apply cutProjection_of_support
    intro i hi
    exact frontier_gradient_supported_through j z hjz i (by change k < i.val; omega)
  · have hc : cutProjection (n := n) (k+1) = ContinuousLinearMap.id ℝ (Space n) := by
      ext v i
      rw [cutProjection_apply,if_pos (by have := i.isLt; omega)]
      rfl
    simp only [hc,ContinuousLinearMap.id_apply]
    trivial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem carried_extensive_truncated_gradient (R M : ℝ) {n : ℕ} (k : ℕ)
    (P : E →L[ℝ] Space n) (w : E)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |P (Bilevel.RadialWrapper.compress R w) i| ≤ 1/16) :
    gradient (RadialWrapper.carried R P (fun z => extensive M (cutProjection k z))) w =
      gradient (RadialWrapper.carried R P (extensive M)) w := by
  have hf : ∀ z : Space n, HasGradientAt (extensive M) (gradient (extensive M) z) z :=
    fun z => (extensive_hasFDerivAt M z).differentiableAt.hasGradientAt
  have ht : ∀ z : Space n, HasGradientAt (fun x => extensive M (cutProjection k x))
      (gradient (fun x => extensive M (cutProjection k x)) z) z :=
    fun z => (cut_comp_hasGradientAt k (hf (cutProjection k z))).differentiableAt.hasGradientAt
  rw [(RadialWrapper.carried_hasGradientAt R P _ _ ht w).gradient,
    (RadialWrapper.carried_hasGradientAt R P _ _ hf w).gradient]
  simp only [RadialWrapper.carriedGradient,extensive_truncated_gradient M k _ htail]

theorem carried_frontier_truncated_value_gradient (R : ℝ) {n : ℕ} (k : ℕ)
    (P : E →L[ℝ] Space n) (w : E)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |P (Bilevel.RadialWrapper.compress R w) i| ≤ 1/16) :
    RadialWrapper.carried R P (fun z => Cutoffs.frontier (cutProjection (k+1) z)) w =
      RadialWrapper.carried R P Cutoffs.frontier w ∧
    gradient (RadialWrapper.carried R P (fun z => Cutoffs.frontier (cutProjection (k+1) z))) w =
      gradient (RadialWrapper.carried R P Cutoffs.frontier) w := by
  have hfg := frontier_truncated_value_gradient k (P (Bilevel.RadialWrapper.compress R w)) htail
  refine ⟨hfg.1,?_⟩
  have hf : ∀ z : Space n, HasGradientAt Cutoffs.frontier (gradient Cutoffs.frontier z) z :=
    fun z => (actual_frontier_differentiable z).1.hasGradientAt
  have ht : ∀ z : Space n, HasGradientAt (fun x => Cutoffs.frontier (cutProjection (k+1) x))
      (gradient (fun x => Cutoffs.frontier (cutProjection (k+1) x)) z) z :=
    fun z => (cut_comp_hasGradientAt (k+1) (hf (cutProjection (k+1) z))).differentiableAt.hasGradientAt
  rw [(RadialWrapper.carried_hasGradientAt R P _ _ ht w).gradient,
    (RadialWrapper.carried_hasGradientAt R P _ _ hf w).gradient]
  simp only [RadialWrapper.carriedGradient,hfg.2]

end Smoothness2601.ExtensiveChain
