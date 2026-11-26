import Bilevel.ChiPrefixEvaluation

/-! Exact first-jet equality with the prefix evaluator on the open blind
region. The proof differentiates a local equality of actual scalar values;
gradient support alone is not used as a substitute for evaluation equality. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace Topology
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain

theorem retain_eq_of_tail_zero {n s : ℕ} (z : Space n)
    (hz : ∀ k : Fin (n+1),s≤k.val → z k=0) : retain n s z=z := by
  ext k
  rw [retain_apply]
  by_cases hk : k.val<s
  · exact if_pos hk
  · rw [if_neg hk,hz k (by omega)]

theorem inner_retain_right {n s : ℕ} (z v : Space n) :
    ⟪retain n s z,v⟫=⟪z,retain n s v⟫ := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val<s <;> simp [retain_apply,hk]

theorem gradient_comp_retain {n s : ℕ} (f : Space n → ℝ) (hf : Differentiable ℝ f) (z : Space n) :
    gradient (f ∘ retain n s) z=retain n s (gradient f (retain n s z)) := by
  have hd := (hf (retain n s z)).hasGradientAt.hasFDerivAt.comp z (retain n s).hasFDerivAt
  have hg : HasGradientAt (f ∘ retain n s) (retain n s (gradient f (retain n s z))) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hd using 1
    ext v
    simp only [ContinuousLinearMap.comp_apply,InnerProductSpace.toDual_apply,inner_retain_right]
  exact hg.gradient

theorem gradient_eq_retain {n r s : ℕ} {τ : ℝ} (hτ : 0<τ) (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hs : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → gradient f w k=0)
    (z : Space n) (hz : ∀ k : Fin (n+1),r≤k.val → |z k|<τ) :
    gradient f z=gradient f (retain n s z) := by
  have ho : IsOpen {w : Space n | ∀ k : Fin (n+1),r≤k.val → |w k|<τ} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (EuclideanSpace.proj (𝕜:=ℝ) k).continuous.abs continuous_const
  have he : f =ᶠ[𝓝 z] (fun w => f (retain n s w)) := by
    filter_upwards [ho.mem_nhds hz] with w hw
    exact value_eq_retain f hf hs w (fun k hk => (hw k hk).le)
  have hb : ∀ k : Fin (n+1),r≤k.val → |retain n s z k|≤τ := by
    intro k hk
    rw [retain_apply]
    by_cases hk' : k.val<s
    · simpa only [if_pos hk'] using (hz k hk).le
    · simpa only [if_neg hk',abs_zero] using hτ.le
  have hfix := retain_eq_of_tail_zero (gradient f (retain n s z)) (hs _ hb)
  have hd := (hf (retain n s z)).hasGradientAt.hasFDerivAt.comp z (retain n s).hasFDerivAt
  have hg : HasGradientAt (fun w => f (retain n s w)) (gradient f (retain n s z)) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hd using 1
    ext v
    simp only [ContinuousLinearMap.comp_apply,InnerProductSpace.toDual_apply]
    rw [←inner_retain_right,hfix]
  exact (hg.congr_of_eventuallyEq he).gradient

theorem carrier_jet_eq_retain {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|<1/4) :
    carrier n z=carrier n (retain n r z) ∧
      gradient (carrier n) z=gradient (carrier n) (retain n r z) :=
  ⟨carrier_value_eq_retain r z (fun k hk => (hz k hk).le),
    gradient_eq_retain (by norm_num) (carrier n) (fun w => (carrier_hasFDerivAt n w).differentiableAt)
      (fun w hw k hk => carrier_gradient_support r w hw k hk) z hz⟩

end Bilevel.ChiPrefixEvaluation
