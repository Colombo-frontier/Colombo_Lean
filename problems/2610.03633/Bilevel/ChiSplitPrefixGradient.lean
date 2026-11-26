import Bilevel.ChiSplitPayloadPrefix

/-! Exact self-adjoint split-prefix projection and the resulting separate
source/target gradient support for the actual split payload and fine atoms. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiSplitFine
open ChiBoundedChain ChiPrefixEvaluation PrimitiveGeometry

theorem retainSplit_inner (n r : ℕ) (z v : Latent n) :
    ⟪retainSplit n r z,v⟫=⟪z,retainSplit n r v⟫ := by
  change ⟪retain n (r+1) z.fst,v.fst⟫+⟪retain n r z.snd,v.snd⟫=
    ⟪z.fst,retain n (r+1) v.fst⟫+⟪z.snd,retain n r v.snd⟫
  rw [inner_retain_right,inner_retain_right]

theorem gradient_comp_retainSplit {n : ℕ} (r : ℕ) (f : Latent n → ℝ)
    (hf : Differentiable ℝ f) (z : Latent n) :
    gradient (f ∘ retainSplit n r) z=retainSplit n r (gradient f (retainSplit n r z)) := by
  have hd := (hf (retainSplit n r z)).hasGradientAt.hasFDerivAt.comp z (retainSplit n r).hasFDerivAt
  have hg : HasGradientAt (f ∘ retainSplit n r) (retainSplit n r (gradient f (retainSplit n r z))) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hd using 1
    ext v
    simp only [ContinuousLinearMap.comp_apply,InnerProductSpace.toDual_apply,retainSplit_inner]
  exact hg.gradient

theorem gradient_support_of_prefix_germ {n : ℕ} (r : ℕ) (f : Latent n → ℝ)
    (hf : Differentiable ℝ f) (z : Latent n)
    (he : Filter.EventuallyEq (nhds z) f (f ∘ retainSplit n r)) :
    (∀ k : Fin (n+1),r+1≤k.val → (gradient f z).fst k=0) ∧
    (∀ k : Fin (n+1),r≤k.val → (gradient f z).snd k=0) := by
  rw [he.gradient_eq,gradient_comp_retainSplit r f hf z]
  constructor
  · intro k hk
    change retain n (r+1) _ k=0
    rw [retain_apply,if_neg (by omega)]
  · intro k hk
    change retain n r _ k=0
    rw [retain_apply,if_neg (by omega)]

theorem pieces_gradient_support (P : ChiFine.Parameters) (n j r : ℕ) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|<P.β/4) :
    (∀ k : Fin (n+1),r+1≤k.val → (gradient (pieces P n j) z).fst k=0) ∧
    (∀ k : Fin (n+1),r≤k.val → (gradient (pieces P n j) z).snd k=0) :=
  gradient_support_of_prefix_germ r (pieces P n j) ((pieces_contDiff P n j).differentiable (by norm_num)) z
    (value_prefix_eventually _ r (P.β/4) (pieces_prefix_value P n j r) z hz)

theorem payload_gradient_support (n r : ℕ) (ell h A ν g hp T : ℝ) (hh : 0<h)
    (z : Latent n) (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|<h/4) :
    (∀ k : Fin (n+1),r+1≤k.val → (gradient (ChiSplitChain.payload n ell h A ν g hp T) z).fst k=0) ∧
    (∀ k : Fin (n+1),r≤k.val → (gradient (ChiSplitChain.payload n ell h A ν g hp T) z).snd k=0) :=
  gradient_support_of_prefix_germ r _ ((ChiSplitChain.payload_contDiff n 3 ell h A ν g hp T).differentiable (by norm_num)) z
    (ChiSplitChain.payload_prefix_eventually n r ell h A ν g hp T hh z hz)

end Bilevel.ChiSplitFine
