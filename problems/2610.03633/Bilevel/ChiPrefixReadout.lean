import Bilevel.ChiPrefixClosedJet
import Bilevel.RadialRegularity

/-! A finite disclosed-vector evaluator, defined even for invalid lists.
No orthonormal completion is chosen. On a valid prefix it is exactly the
prefixWrapped evaluator and therefore gives the actual blind-region jet. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain WrappedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def readout (n s : ℕ) (R : ℝ) (columns : Fin (n+1) → E) (u : E) : Space n :=
  ∑ k : Fin (n+1),if k.val<s then ⟪columns k,RadialWrapper.compress R u⟫ • basis k else 0

omit [CompleteSpace E] in
theorem readout_apply (n s : ℕ) (R : ℝ) (columns : Fin (n+1) → E) (u : E) (k : Fin (n+1)) :
    readout n s R columns u k=if k.val<s then ⟪columns k,RadialWrapper.compress R u⟫ else 0 := by
  change (EuclideanSpace.proj (𝕜:=ℝ) k) (readout n s R columns u)=_
  rw [readout,map_sum,Finset.sum_eq_single k]
  · by_cases hk : k.val<s <;> simp [hk,basis]
  · intro i _ hik
    by_cases hi : i.val<s <;> simp [hi,basis,hik,hik.symm]
  · simp

theorem readout_eq_retained (n s : ℕ) (R : ℝ) (columns : Fin (n+1) → E)
    (U : Space n →ₗᵢ[ℝ] E) (hU : ∀ k : Fin (n+1),k.val<s → columns k=U (basis k)) (u : E) :
    readout n s R columns u=retain n s (coordinates n R U u) := by
  ext k
  rw [readout_apply,retain_apply]
  by_cases hk : k.val<s
  · rw [if_pos hk,if_pos hk,hU k hk,coordinates_inner]
  · rw [if_neg hk,if_neg hk]

omit [CompleteSpace E] in
theorem readout_continuous (n s : ℕ) (R : ℝ) :
    Continuous (fun p : (Fin (n+1) → E) × E => readout n s R p.1 p.2) := by
  unfold readout
  apply continuous_finset_sum
  intro k _
  by_cases hk : k.val<s
  · simp only [if_pos hk]
    exact (((continuous_apply k).comp continuous_fst).inner
      ((RadialWrapper.compress_contDiff R 1).continuous.comp continuous_snd)).smul continuous_const
  · simp only [if_neg hk]
    exact continuous_const

def disclosedEvaluator (n s : ℕ) (R : ℝ) (columns : Fin (n+1) → E) (f : Space n → ℝ) : E → ℝ :=
  f ∘ readout n s R columns

theorem disclosedEvaluator_eq_prefix (n s : ℕ) (R : ℝ) (columns : Fin (n+1) → E)
    (U : Space n →ₗᵢ[ℝ] E) (hU : ∀ k : Fin (n+1),k.val<s → columns k=U (basis k)) (f : Space n → ℝ) :
    disclosedEvaluator n s R columns f=prefixWrapped n s R U f := by
  funext u
  exact congrArg f (readout_eq_retained n s R columns U hU u)

omit [CompleteSpace E] in
theorem disclosedEvaluator_continuous (n s : ℕ) (R : ℝ) (f : Space n → ℝ) (hf : Continuous f) :
    Continuous (fun p : (Fin (n+1) → E) × E => disclosedEvaluator n s R p.1 f p.2) :=
  hf.comp (readout_continuous n s R)

theorem disclosedEvaluator_actual_jet {n r s : ℕ} {τ : ℝ} (hτ : 0<τ)
    (R : ℝ) (hR : 0<R) (columns : Fin (n+1) → E) (U : Space n →ₗᵢ[ℝ] E)
    (hU : ∀ k : Fin (n+1),k.val<s → columns k=U (basis k)) (f : Space n → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hs : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → gradient f w k=0)
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n R U u k|≤τ) :
    f (coordinates n R U u)=disclosedEvaluator n s R columns f u ∧
      gradient (f ∘ coordinates n R U) u=gradient (disclosedEvaluator n s R columns f) u := by
  rw [disclosedEvaluator_eq_prefix n s R columns U hU f]
  exact wrapped_prefix_jet_closed hτ R hR U f hf hs u hu

end Bilevel.ChiPrefixEvaluation
