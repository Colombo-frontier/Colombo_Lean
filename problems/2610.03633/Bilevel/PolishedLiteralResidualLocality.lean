import Bilevel.PolishedLiteralPrefixLocality
import Bilevel.PolishedLiteralFlattening
import Bilevel.PolishedLiteralSelectorJets

/-! Actual active residual reveals at most one next latent column; actual
flattened residuals reveal no new column inside their flattening core. -/
noncomputable section
open scoped Topology
open Filter
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ChiPrefixEvaluation ZeroChainPotential PolishedLiteralFlattenMap PolishedLiteralFlattenCutoff

theorem selector_future_flat (n r : ℕ) (i : Fin (n+1)) (hi : r+1 ≤ i.val) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤1/4) (q : ℕ) (hq : q≤3) :
    iteratedFDeriv ℝ q (selector n i) z=0 := by
  revert hi
  refine Fin.cases (by intro h;have : (0:ℕ)≥r+1 := h;omega) (fun j => ?_) i
  intro hi
  have hj : r≤j.castSucc.val := by
    change r≤j.val
    change r+1≤j.val+1 at hi
    omega
  exact selector_succ_flat_all j z (by linarith [(abs_le.mp (hz j.castSucc hj)).2]) q hq

theorem selector_future_zero (n r : ℕ) (i : Fin (n+1)) (hi : r+1 ≤ i.val) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤1/4) : selector n i z=0 := by
  have ht := selector_future_flat n r i hi z hz 0 (by norm_num)
  simpa only [iteratedFDeriv_zero_apply] using congrArg (fun f => f 0) ht

theorem normalizedResidual_prefix_value (n r : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤1/4) :
    normalizedResidual n z=normalizedResidual n (retain n (r+1) z) := by
  have hr (k : Fin (n+1)) (hk : r≤k.val) : |retain n (r+1) z k|≤1/4 := by
    rw [retain_apply]
    split_ifs with h
    · exact hz k hk
    · norm_num
  unfold normalizedResidual
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val<r+1
  · simp only [residualTerm,selector_prefix_value n (r+1) i z
      (fun k hk => hz k (by omega)),retain_apply,if_pos hi]
  · simp only [residualTerm,selector_future_zero n r i (by omega) z hz,
      selector_future_zero n r i (by omega) (retain n (r+1) z) hr,neg_zero,zero_mul]

theorem prefix_gradient_of_value_general {n r s : ℕ} {τ : ℝ} (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hval : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      f w=f (retain n s w)) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|<τ) :
    gradient f z=retain n s (gradient f (retain n s z)) := by
  have ho : IsOpen {w : Space n | ∀ k : Fin (n+1),r≤k.val → |w k|<τ} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (EuclideanSpace.proj (𝕜:=ℝ) k).continuous.abs continuous_const
  have he : f=ᶠ[𝓝 z] (f ∘ retain n s) := by
    filter_upwards [ho.mem_nhds hz] with w hw
    exact hval w (fun k hk => (hw k hk).le)
  have hg : gradient f z=gradient (f ∘ retain n s) z := by simp only [gradient,he.fderiv_eq]
  rw [hg,ChiPrefixEvaluation.gradient_comp_retain f hf]

theorem normalizedResidual_prefix_gradient (n r : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|<1/4) :
    gradient (normalizedResidual n) z=retain n (r+1)
      (gradient (normalizedResidual n) (retain n (r+1) z)) :=
  prefix_gradient_of_value_general _ ((normalizedResidual_contDiff n 3).differentiable (by norm_num))
    (normalizedResidual_prefix_value n r) z hz

theorem flattenMap_retain (n r : ℕ) (δ : ℝ) :
    (fun z => flattenMap n δ (retain n r z))=fun z => retain n r (flattenMap n δ z) := by
  funext z
  ext k
  simp only [flattenMap,coordinateMap_apply,retain_apply]
  split_ifs
  · rfl
  · simp only [flatten,zero_div,zero_mul]

theorem normalizedFlat_prefix_value (n r : ℕ) (δ : ℝ) (hδ : 0<δ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤δ) :
    normalizedFlat n δ z=normalizedFlat n δ (retain n r z) := by
  have he : retain n r (flattenMap n δ z)=flattenMap n δ z := by
    apply retain_eq_of_tail_zero
    intro k hk
    exact flatten_zero hδ (hz k hk)
  unfold normalizedFlat
  rw [congrFun (flattenMap_retain n r δ) z,he]

theorem normalizedFlat_prefix_gradient (n r : ℕ) (δ : ℝ) (hδ : 0<δ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|<δ) :
    gradient (normalizedFlat n δ) z=retain n r (gradient (normalizedFlat n δ) (retain n r z)) :=
  prefix_gradient_of_value _ ((normalizedFlat_contDiff n δ).differentiable (by norm_num))
    (normalizedFlat_prefix_value n r δ hδ) z hz


theorem residual_prefix_value (n r : ℕ) (L β : ℝ) (hβ : 0<β) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤β/4) :
    residual n L β z=residual n L β (retain n (r+1) z) := by
  unfold residual
  rw [normalizedResidual_prefix_value n r (β⁻¹ • z)
    (fun k hk => ZeroChainResidualScaled.scaled_coordinate_small β hβ z k (hz k hk)),map_smul]

theorem flatResidual_prefix_value (n r : ℕ) (L β δ : ℝ) (hδ : 0<δ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤δ) :
    flatResidual n L β δ z=flatResidual n L β δ (retain n r z) := by
  have he : retain n r (flattenMap n δ z)=flattenMap n δ z := by
    apply retain_eq_of_tail_zero
    intro k hk
    exact flatten_zero hδ (hz k hk)
  unfold flatResidual
  rw [congrFun (flattenMap_retain n r δ) z,he]

theorem wrapped_prefix_of_value_general {n r s : ℕ} {τ : ℝ} (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hval : ∀ z : Space n,(∀ k : Fin (n+1),r≤k.val → |z k|≤τ) → f z=f (retain n s z))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (hR : 0<R) (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n R U u k|<τ) :
    f (WrappedChain.coordinates n R U u)=ChiPrefixEvaluation.prefixWrapped n s R U f u ∧
    gradient (f ∘ WrappedChain.coordinates n R U) u=
      gradient (ChiPrefixEvaluation.prefixWrapped n s R U f) u := by
  refine ⟨hval _ (fun k hk => (hu k hk).le),?_⟩
  change gradient (f ∘ WrappedChain.coordinates n R U) u=
    gradient ((f ∘ retain n s) ∘ WrappedChain.coordinates n R U) u
  rw [WrappedPrefixLocality.carried_gradient n R hR U f hf,
    WrappedPrefixLocality.carried_gradient n R hR U (f ∘ retain n s) (hf.comp (retain n s).differentiable),
    ChiPrefixEvaluation.gradient_comp_retain f hf,
    ← prefix_gradient_of_value_general f hf hval (WrappedChain.coordinates n R U u) hu]

theorem residual_wrapped_prefix {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n r : ℕ) (L β R : ℝ) (hβ : 0<β) (hR : 0<R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n R U u k|<β/4) :
    residual n L β (WrappedChain.coordinates n R U u)=
      ChiPrefixEvaluation.prefixWrapped n (r+1) R U (residual n L β) u ∧
    gradient (residual n L β ∘ WrappedChain.coordinates n R U) u=
      gradient (ChiPrefixEvaluation.prefixWrapped n (r+1) R U (residual n L β)) u :=
  wrapped_prefix_of_value_general _ ((residual_contDiff n 3 L β).differentiable (by norm_num))
    (residual_prefix_value n r L β hβ) R hR U u hu

theorem flatResidual_wrapped_prefix {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n r : ℕ) (L β δ R : ℝ) (hδ : 0<δ) (hR : 0<R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n R U u k|<δ) :
    flatResidual n L β δ (WrappedChain.coordinates n R U u)=
      ChiPrefixEvaluation.prefixWrapped n r R U (flatResidual n L β δ) u ∧
    gradient (flatResidual n L β δ ∘ WrappedChain.coordinates n R U) u=
      gradient (ChiPrefixEvaluation.prefixWrapped n r R U (flatResidual n L β δ)) u :=
  wrapped_prefix_of_value _ ((flatResidual_contDiff n L β δ).differentiable (by norm_num))
    (flatResidual_prefix_value n r L β δ hδ) R hR U u hu

end Bilevel.PolishedLiteral
