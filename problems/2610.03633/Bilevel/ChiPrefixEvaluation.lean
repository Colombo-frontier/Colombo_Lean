import Bilevel.ChiBoundedChainLocality
import Mathlib.Analysis.Calculus.MeanValue

/-! Prefix evaluation from actual flat-tail derivatives. This general
calculus lemma supplies equality of values, rather than only membership of
the gradient in a revealed subspace. Construction-specific applications
discharge its derivative-support premise separately. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain

def retain (n s : ℕ) : Space n →L[ℝ] Space n :=
  ∑ k : Fin (n+1),if k.val<s then (EuclideanSpace.proj (𝕜:=ℝ) k).smulRight (basis k) else 0

theorem retain_apply (n s : ℕ) (z : Space n) (k : Fin (n+1)) :
    retain n s z k=if k.val<s then z k else 0 := by
  change (EuclideanSpace.proj (𝕜:=ℝ) k) (retain n s z)=_
  rw [retain,ContinuousLinearMap.sum_apply,map_sum]
  rw [Finset.sum_eq_single k]
  · by_cases hk : k.val<s <;> simp [hk,basis]
  · intro i _ hik
    by_cases hi : i.val<s <;> simp [hi,basis,hik,hik.symm]
  · simp

def line (n s : ℕ) (z : Space n) (t : ℝ) : Space n :=
  retain n s z+t • (z-retain n s z)

theorem line_blind {n r s : ℕ} {τ : ℝ} (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤τ)
    (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) (k : Fin (n+1)) (hk : r≤k.val) :
    |line n s z t k|≤τ := by
  simp only [line,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,retain_apply]
  by_cases hs : k.val<s
  · simpa only [if_pos hs,sub_self,mul_zero,add_zero] using hz k hk
  · simp only [if_neg hs,sub_zero,zero_add,abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans (hz k hk)

theorem line_hasDerivAt (n s : ℕ) (z : Space n) (t : ℝ) :
    HasDerivAt (line n s z) (z-retain n s z) t := by
  convert ((hasDerivAt_id t).smul_const (z-retain n s z)).const_add (retain n s z) using 1
  simp

theorem value_eq_retain {n r s : ℕ} {τ : ℝ} (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hs : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → gradient f w k=0)
    (z : Space n) (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤τ) :
    f z=f (retain n s z) := by
  have hd (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) : HasDerivAt (f ∘ line n s z) 0 t := by
    have h := (hf (line n s z t)).hasFDerivAt.comp_hasDerivAt t (line_hasDerivAt n s z t)
    have he : fderiv ℝ f (line n s z t) (z-retain n s z)=0 := by
      rw [((hf (line n s z t)).hasGradientAt.hasFDerivAt).fderiv,InnerProductSpace.toDual_apply,PiLp.inner_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k.val<s
      · simp only [PiLp.sub_apply,retain_apply,if_pos hk,sub_self,inner_zero_right]
      · rw [hs _ (line_blind z hz t ht) k (by omega),inner_zero_left]
    simpa only [he] using h
  have hc : ContinuousOn (f ∘ line n s z) (Set.Icc (0:ℝ) 1) :=
    (hf.continuous.comp (continuous_iff_continuousAt.mpr
      (fun t => (line_hasDerivAt n s z t).continuousAt))).continuousOn
  have he := constant_of_has_deriv_right_zero hc
    (fun t ht => (hd t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt) 1 (by constructor <;> norm_num)
  simpa only [Function.comp_apply,line,one_smul,add_sub_cancel,zero_smul,add_zero] using he

theorem carrier_value_eq_retain {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤1/4) :
    carrier n z=carrier n (retain n r z) :=
  value_eq_retain (carrier n) (fun w => (carrier_hasFDerivAt n w).differentiableAt)
    (fun w hw k hk => carrier_gradient_support r w hw k hk) z hz

end Bilevel.ChiPrefixEvaluation
