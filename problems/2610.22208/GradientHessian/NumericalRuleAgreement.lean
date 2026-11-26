import GradientHessian.NumericalPriorCache
import GradientHessian.GeometricMaskedEarly

/-! Exact pre-supply and post-supply numerical rules from the charged
prior-readout cache. The current target hit is identically suppressed,
while every preceding hit and every other repair predicate is preserved. -/

noncomputable section
namespace GradientHessian.NumericalRuleAgreement
open Classical HigherHierarchy HierarchyAddresses GeometricRepair FrontierState TaskState
  ComparisonController ComparisonControllerReplay NumericalCachedOracle NumericalShadowRules
  GeometricMaskedEarly

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
  (fallback : Fin d → ℝ) (t : ℕ) (leaf : Leaf (t+1))

theorem current_before_supply (j : Fin (4096*J^2+1))
    (s : State (t+1) (4096*J^2+1) ell) (hs : markSupplied leaf j s=false)
    (hc : TaskState.current s=some leaf) : (s.completed leaf).val<j.val := by
  have hh := of_decide_eq_false hs
  by_contra hn
  exact hh (Or.inr ⟨hc,by omega⟩)

theorem cached_hit_before_supply (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (j : Fin (4096*J^2+1))
    (ha : ∀ k,k<j → c.2 k=(leafCoefficients (RawHierarchy.assemble P B fallback t x) leaf).a k)
    (s : State (t+1) (4096*J^2+1) ell) (hs : markSupplied leaf j s=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    cachedHit P B fallback t leaf (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c s Z=
      hit (RawHierarchy.assemble P B fallback t x) s Z := by
  apply cached_hit_exact P B fallback t leaf x c s
  intro hc
  exact ha _ (current_before_supply t leaf j s hs hc)

theorem cached_hit_after_supply (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (j : Fin (4096*J^2+1))
    (ha : ∀ k,k<j → c.2 k=(leafCoefficients (RawHierarchy.assemble P B fallback t x) leaf).a k)
    (hz : c.2 j=0)
    (s : State (t+1) (4096*J^2+1) ell) (hs : taskDisclosed leaf j s=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    cachedHit P B fallback t leaf (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c s Z=
      if targetTask leaf j s then false else hit (RawHierarchy.assemble P B fallback t x) s Z := by
  by_cases hc : TaskState.current s=some leaf
  · have hle : (s.completed leaf).val≤j.val := by
      have hh := of_decide_eq_false hs
      change ¬j.val<(s.completed leaf).val at hh
      omega
    by_cases hj : (s.completed leaf).val=j.val
    · have he : (⟨(s.completed leaf).val,current_live s hc⟩ : Fin (4096*J^2+1))=j := Fin.ext hj
      simp [cachedHit,hc,he,hz,targetTask,hj]
    · have ht : targetTask leaf j s=false := by simp [targetTask,hc,hj]
      rw [ht]
      simp only [Bool.false_eq_true,if_false]
      apply cached_hit_exact P B fallback t leaf x c s
      intro hh
      exact ha _ (by change (s.completed leaf).val<j.val; omega)
  · have ht : targetTask leaf j s=false := by simp [targetTask,hc]
    rw [ht]
    simp only [Bool.false_eq_true,if_false]
    apply cached_hit_exact P B fallback t leaf x c s
    intro hh
    exact False.elim (hc hh)

theorem pre_rules (K : ℝ) (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (j : Fin (4096*J^2+1))
    (ha : ∀ k,k<j → c.2 k=(leafCoefficients (RawHierarchy.assemble P B fallback t x) leaf).a k)
    (s : State (t+1) (4096*J^2+1) ell) (hs : markSupplied leaf j s=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    let R := shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
    let T := suppress (rules (ell := ell) K (RawHierarchy.assemble P B fallback t x)) (blockLeaf leaf)
    R.priority=T.priority ∧ R.target=T.target ∧ (∀ a,R.trigger s Z a=T.trigger s Z a) ∧ R.hit s Z=T.hit s Z :=
  ⟨rfl,rfl,fun a => shadow_trigger_exact P B fallback t leaf K x c s Z a,
    cached_hit_before_supply P B fallback t leaf x c j ha s hs Z⟩

theorem post_rules (K : ℝ) (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (j : Fin (4096*J^2+1))
    (ha : ∀ k,k<j → c.2 k=(leafCoefficients (RawHierarchy.assemble P B fallback t x) leaf).a k)
    (hz : c.2 j=0)
    (s : State (t+1) (4096*J^2+1) ell) (hs : taskDisclosed leaf j s=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    let R := shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
    let T := ControllerHitMasking.mask
      (suppress (rules (ell := ell) K (RawHierarchy.assemble P B fallback t x)) (blockLeaf leaf)) (targetTask leaf j)
    R.priority=T.priority ∧ R.target=T.target ∧ (∀ a,R.trigger s Z a=T.trigger s Z a) ∧ R.hit s Z=T.hit s Z :=
  ⟨rfl,rfl,fun a => shadow_trigger_exact P B fallback t leaf K x c s Z a,
    cached_hit_after_supply P B fallback t leaf x c j ha hz s hs Z⟩

variable {Seed : Type*} [MeasurableSpace Seed]

theorem store_readouts_exact (j : Fin (4096*J^2+1))
    (x : RawHierarchy.Raw d n r J E H t × Seed) (k : Fin (4096*J^2+1)) (hk : k<j) :
    (NumericalPriorCache.store B j (ReadoutOracle.readout (ReadoutFilter.matrixUpper J) P
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 ((leafEquiv t).symm leaf)).1) fallback)
      (RawNumericalExperiment.factor t ((leafEquiv t).symm leaf) j x).1.2.1).2 k=
        (leafCoefficients (RawHierarchy.assemble P B fallback t x.1) leaf).a k := by
  rw [NumericalPriorCache.prior_value_exact P B fallback t ((leafEquiv t).symm leaf) j k x hk]
  rw [NumericalPriorCache.coefficient_a]
  change _=(leafData t (RawHierarchy.assemble P B fallback t x.1) ((leafEquiv t).symm leaf)).a k
  rw [RawLeafFactor.leaf_a_assemble]
  rfl

end GradientHessian.NumericalRuleAgreement
