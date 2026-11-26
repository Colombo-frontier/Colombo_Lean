import Bilevel.ChiPrefixReadout

/-! A local scalar equality for the explicit finite-column evaluator. It is
derived by integrating the proved latent gradient support along erased tails. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain WrappedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem disclosedEvaluator_actual_germ {n r s : ℕ} {τ : ℝ}
    (R : ℝ) (columns : Fin (n+1) → E) (U : Space n →ₗᵢ[ℝ] E)
    (hU : ∀ k : Fin (n+1),k.val<s → columns k=U (basis k)) (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hs : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → gradient f w k=0)
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n R U u k|<τ) :
    (f ∘ coordinates n R U)=ᶠ[𝓝 u] disclosedEvaluator n s R columns f := by
  have ho : IsOpen {v : E | ∀ k : Fin (n+1),r≤k.val → |coordinates n R U v k|<τ} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (((EuclideanSpace.proj (𝕜:=ℝ) k).continuous.comp
      (ZeroChainWrappedResidual.coordinates_contDiff n R U).continuous).abs) continuous_const
  rw [disclosedEvaluator_eq_prefix n s R columns U hU f]
  filter_upwards [ho.mem_nhds hu] with v hv
  exact value_eq_retain f hf hs _ (fun k hk => (hv k hk).le)

end Bilevel.ChiPrefixEvaluation
