import Bilevel.ChiPrefixJets
import Bilevel.WrappedPrefixLocality

/-! Prefix-only radial/frame evaluation. The virtual evaluator is globally
independent of every undisclosed frame column, and its actual ambient first
jet agrees with the complete function inside the blind region. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain WrappedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem coordinates_inner (n : ℕ) (R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (u : E) (k : Fin (n+1)) :
    coordinates n R U u k=⟪U (basis k),RadialWrapper.compress R u⟫ := by
  have hh := U.toContinuousLinearMap.adjoint_inner_right (basis k) (RadialWrapper.compress R u)
  simpa only [basis,EuclideanSpace.inner_single_left,one_mul,conj_trivial] using hh

theorem retained_coordinates_eq (n s : ℕ) (R : ℝ) (U V : Space n →ₗᵢ[ℝ] E)
    (hUV : ∀ k : Fin (n+1),k.val<s → U (basis k)=V (basis k)) (u : E) :
    retain n s (coordinates n R U u)=retain n s (coordinates n R V u) := by
  ext k
  rw [retain_apply,retain_apply]
  by_cases hk : k.val<s
  · rw [if_pos hk,if_pos hk,coordinates_inner,coordinates_inner,hUV k hk]
  · rw [if_neg hk,if_neg hk]

def prefixWrapped (n s : ℕ) (R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (f : Space n → ℝ) : E → ℝ :=
  f ∘ retain n s ∘ coordinates n R U

theorem prefixWrapped_frame_independent (n s : ℕ) (R : ℝ) (U V : Space n →ₗᵢ[ℝ] E)
    (hUV : ∀ k : Fin (n+1),k.val<s → U (basis k)=V (basis k)) (f : Space n → ℝ) :
    prefixWrapped n s R U f=prefixWrapped n s R V f := by
  funext u
  exact congrArg f (retained_coordinates_eq n s R U V hUV u)

theorem wrapped_prefix_jet {n r s : ℕ} {τ : ℝ} (hτ : 0<τ)
    (R : ℝ) (hR : 0<R) (U : Space n →ₗᵢ[ℝ] E) (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hs : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → gradient f w k=0)
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n R U u k|<τ) :
    f (coordinates n R U u)=prefixWrapped n s R U f u ∧
      gradient (f ∘ coordinates n R U) u=gradient (prefixWrapped n s R U f) u := by
  refine ⟨value_eq_retain f hf hs _ (fun k hk => (hu k hk).le),?_⟩
  change gradient (f ∘ coordinates n R U) u=gradient ((f ∘ retain n s) ∘ coordinates n R U) u
  rw [WrappedPrefixLocality.carried_gradient n R hR U f hf,
    WrappedPrefixLocality.carried_gradient n R hR U (f ∘ retain n s) (hf.comp (retain n s).differentiable),
    gradient_comp_retain f hf,←gradient_eq_retain hτ f hf hs _ hu,
    retain_eq_of_tail_zero _ (hs _ (fun k hk => (hu k hk).le))]

theorem wrapped_frame_completion_jet {n r s : ℕ} {τ : ℝ} (hτ : 0<τ)
    (R : ℝ) (hR : 0<R) (U V : Space n →ₗᵢ[ℝ] E)
    (hUV : ∀ k : Fin (n+1),k.val<s → U (basis k)=V (basis k)) (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hs : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → gradient f w k=0)
    (u : E) (hU : ∀ k : Fin (n+1),r≤k.val → |coordinates n R U u k|<τ)
    (hV : ∀ k : Fin (n+1),r≤k.val → |coordinates n R V u k|<τ) :
    f (coordinates n R U u)=f (coordinates n R V u) ∧
      gradient (f ∘ coordinates n R U) u=gradient (f ∘ coordinates n R V) u := by
  obtain ⟨hvU,hgU⟩ := wrapped_prefix_jet hτ R hR U f hf hs u hU
  obtain ⟨hvV,hgV⟩ := wrapped_prefix_jet hτ R hR V f hf hs u hV
  rw [prefixWrapped_frame_independent n s R U V hUV f] at hvU hgU
  exact ⟨hvU.trans hvV.symm,hgU.trans hgV.symm⟩

end Bilevel.ChiPrefixEvaluation
