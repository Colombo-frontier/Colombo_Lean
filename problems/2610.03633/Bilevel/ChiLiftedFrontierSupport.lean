import Bilevel.ChiLiftedSelection
import Bilevel.ChiFrontierSupport

/-! Selector-path support on a heterogeneous Hilbert ambient space. The
frontier premise concerns only reachable children; future selector values
vanish and their derivatives are already in the known space. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiLiftedCarrier
open ChiBoundedChain ChiRecursive ChiCarrier
variable {E X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem selectFamily_gradient_mem_frontier {m : ℕ} (D : Geometry E)
    (A : X →L[ℝ] Blocks m E) (leaf : ℕ → List ℕ → X → ℝ)
    (hleaf : ∀ k P,ContDiff ℝ 3 (leaf k P)) (d j : ℕ) (I : List ℕ)
    (V : Submodule ℝ E) (W : Submodule ℝ X) (x : X)
    (r : ℕ → List ℕ → ℕ) (hfront : FrontierKnown D r V d j I)
    (hsel : ∀ k P,j≤k → k<j+d → ∀ i : Fin ((D k P).n+1),
      gradient (selector m k (D k P) A i) x∈W)
    (hzero : ∀ k P,j≤k → k<j+d → ∀ i : Fin ((D k P).n+1),r k P< i.val →
      selector m k (D k P) A i x=0)
    (hbase : ∀ P,FrontierKnown D r V 0 (j+d) P → gradient (leaf (j+d) P) x∈W) :
    gradient (selectFamily m D A leaf d j I) x∈W := by
  induction d generalizing j I with
  | zero => exact hbase I hfront
  | succ d ih =>
    change gradient (fun y => ∑ i : Fin ((D j I).n+1),selector m j (D j I) A i y*
      selectFamily m D A leaf d (j+1) (child I i.val) y) x∈W
    apply gradient_sum_mem Finset.univ W _
      (fun i => (selector_contDiff m j (D j I) A i 3).mul
        (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val)))
    intro i _
    rw [gradient_mul_C3 (selector_contDiff m j (D j I) A i 3)
      (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val))]
    apply W.add_mem
    · by_cases hi : selector m j (D j I) A i x=0
      · rw [hi,zero_smul]
        exact W.zero_mem
      · have hir : i.val≤r j I := by
          by_contra hh
          exact hi (hzero j I le_rfl (by omega) i (by omega))
        apply W.smul_mem
        apply ih (j+1) (child I i.val) (hfront i hir)
        · exact fun k P hk hkd a => hsel k P (by omega) (by omega) a
        · exact fun k P hk hkd a ha => hzero k P (by omega) (by omega) a ha
        · intro P hp
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
            hbase P (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp)
    · exact W.smul_mem _ (hsel j I le_rfl (by omega) i)

end Bilevel.ChiLiftedCarrier
