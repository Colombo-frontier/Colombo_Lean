import Bilevel.ChiHierarchyStore
import Bilevel.ChiVirtualTwoStoreReply

/-! The finite disclosed store supplies every input of the explicit virtual
evaluator. The adapter reads only its counter and stored columns; the fixed
template contributes numerical node sizes, never hidden frame columns. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyIndex
open ChiPrefixEvaluation ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteVirtualState (counts : ℕ → ℕ) (J : ℕ) (M : ChiRecursive.Node E) (D : Geometry E)
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
    (s : Store counts J E) : VirtualState M D :=
  (s.1,((fun i => s.2 (Sum.inl ()) (Fin.cast (congrArg (fun k => k+1) hM) i)),
    fun j I i => extendColumns s.2 j I (Fin.cast (congrArg (fun k => k+1) (hD j I)) i)))

theorem prefixGram_cast {a b r : ℕ} (h : a=b) (columns : Fin (b+1) → E)
    (hg : PrefixGram b r columns) :
    PrefixGram a r (fun i => columns (Fin.cast (congrArg (fun k => k+1) h) i)) := by
  subst b
  exact hg

theorem finiteVirtualState_valid (counts : ℕ → ℕ) (J : ℕ) (M : ChiRecursive.Node E) (D : Geometry E)
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1)) (s : Store counts J E)
    (hs : ∀ i,PrefixGram (chainSize i) (retained counts J s.1 i) (s.2 i)) :
    ValidState M D (fun q => ChiTreeProgress.counter counts (J+1) q 0 [])
      (canonicalCounter counts J) (finiteVirtualState counts J M D hM hD s) := by
  constructor
  · exact prefixGram_cast hM _ (hs (Sum.inl ()))
  · intro j I
    exact prefixGram_cast (hD j I) _ (extendColumns_gram s.2 s.1 hs j I)

theorem finiteVirtualState_actual_valid (counts : ℕ → ℕ) (J : ℕ) (M : ChiRecursive.Node E) (D : Geometry E)
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
    (U : FiniteColumns counts J E) (hU : ∀ i,Orthonormal ℝ (U i)) (q : ℕ) :
    ValidState M D (fun q => ChiTreeProgress.counter counts (J+1) q 0 [])
      (canonicalCounter counts J) (finiteVirtualState counts J M D hM hD (actual counts J q U)) :=
  finiteVirtualState_valid counts J M D hM hD _ (actual_gram counts J q U hU)

theorem finiteVirtualState_reframe (counts : ℕ → ℕ) (J : ℕ) (M : ChiRecursive.Node E) (D : Geometry E)
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
    (UM : Space M.n →ₗᵢ[ℝ] E) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] E) (s : Store counts J E) :
    finiteVirtualState counts J (reframeNode M UM) (reframeGeometry D U) hM hD s=
      finiteVirtualState counts J M D hM hD s := rfl

variable [MeasurableSpace E]

theorem finiteVirtualState_measurable (counts : ℕ → ℕ) (J : ℕ) (M : ChiRecursive.Node E) (D : Geometry E)
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1)) :
    Measurable (finiteVirtualState counts J M D hM hD) := by
  apply measurable_fst.prodMk
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply _).comp ((measurable_pi_apply (Sum.inl ())).comp measurable_snd)
  · apply measurable_pi_lambda
    intro j
    apply measurable_pi_lambda
    intro I
    apply measurable_pi_lambda
    intro i
    have he := (extendColumns_measurable (E:=E) counts J).comp
      (measurable_snd : Measurable (Prod.snd : Store counts J E → FiniteColumns counts J E))
    exact (measurable_pi_apply _).comp ((measurable_pi_apply I).comp ((measurable_pi_apply j).comp he))

end Bilevel.ChiHierarchyIndex
