import Bilevel.ChiFrontierSupport
import Bilevel.ChiOuterFineLocality
import Bilevel.ChiFineInactiveForce

/-! The macro-fixed lower problem selects at most one outer branch.
Only that branch's unfinished frontier needs its next column disclosed. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerValueStage (M : Node E) (a : E) : Fin (M.n+1) := by
  classical
  exact if h : ∃ i : Fin (M.n+1),wrappedSelector M i a≠0 then Classical.choose h else 0

omit [CompleteSpace F] in
theorem outerValueStage_eq (M : Node E) (a : E) (i : Fin (M.n+1)) (hi : wrappedSelector M i a≠0) :
    outerValueStage M a=i := by
  classical
  have he : ∃ i : Fin (M.n+1),wrappedSelector M i a≠0 := ⟨i,hi⟩
  rw [outerValueStage,dif_pos he]
  exact wrappedSelector_unique M _ i a (Classical.choose_spec he) hi

theorem outerSelected_inner_support_at_stage (m : ℕ) (M : Node E)
    (f : Fin (M.n+1) → Blocks m F → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (a : E) (x : Blocks m F) (W : Submodule ℝ (Blocks m F))
    (hstage : gradient (f (outerValueStage M a)) x∈W) :
    gradient (fun y => outerSelected m M f (pack a y)) x∈W := by
  change gradient (fun y => ∑ i : Fin (M.n+1),wrappedSelector M i a*f i y) x∈W
  apply gradient_sum_mem Finset.univ W _ (fun i => contDiff_const.mul (hf i))
  intro i _
  rw [ChiFine.gradient_const_mul_C3 (hf i)]
  by_cases hi : wrappedSelector M i a=0
  · rw [hi,zero_smul]
    exact W.zero_mem
  · apply W.smul_mem
    rw [← outerValueStage_eq M a i hi]
    exact hstage

theorem outerCoupling_frontier_support {m : ℕ} (M : Node E) (D : Geometry F) (d : ℕ)
    (hm : d<m) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
    (r : ℕ → List ℕ → ℕ) (htree : TreeBlind D 0 d (by simpa using hm) W x r)
    (hfront : FrontierKnown D r (W ⟨d,hm⟩) d 0 [(outerValueStage M a).val])
    (c v s : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v) (hell : ∀ P,0≤(D d P).ell) :
    gradient (fun y => outerCoupling m M D d c v
      (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) s 0)) x∈knownSpace W := by
  rw [funext (outerCoupling_inner_eq m M D d c v s a)]
  apply outerSelected_inner_support_at_stage m M _
    (fun i => selectedCoupling_slice_contDiff m D d 0 [i.val] c v s) a x (knownSpace W)
  exact selectedCoupling_frontier_support D d 0 [(outerValueStage M a).val] (by simpa using hm) W x r htree
    (by simpa only [zero_add] using hfront) c v s hc hcs hv (by simpa only [zero_add] using hell)

end Bilevel.ChiOuter
