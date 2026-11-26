import Bilevel.ChiCarrierSupportAlgebra
import Bilevel.ChiCarrierFineSelection

/-! Exact support propagation through every actual ancestor selector.
The generic induction exposes its leaf premise. The construction-specific
wrapper replaces every selector-support premise by explicit coordinates. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual query is included because radial compression contributes its
direction. The remaining fields are coordinate and frame statements. -/
structure BlindNode {m : ℕ} (W : Fin m → Submodule ℝ E) (x : Blocks m E)
    (j : Fin m) (D : Node E) (r : ℕ) : Prop where
  width_pos : 0 < D.width
  radius_pos : 0 < D.radius
  query_mem : x j ∈ W j
  columns_mem : ∀ k : Fin (D.n+1),k.val < r → D.frame (basis k) ∈ W j
  blind : ∀ k : Fin (D.n+1),r ≤ k.val → |D.coordinates (x j) k| ≤ D.width/4

theorem BlindNode.selector_mem {m : ℕ} {W : Fin m → Submodule ℝ E} {x : Blocks m E}
    {j : Fin m} {D : Node E} {r : ℕ} (h : BlindNode W x j D r) (i : Fin (D.n+1)) :
    gradient (jointSelector m j.val D i) x ∈ knownSpace W :=
  actual_jointSelector_gradient_mem W x j D r h.width_pos h.radius_pos
    h.query_mem h.columns_mem h.blind i

/-- Pure support induction; the concrete leaf support is intentionally an
explicit interface and is discharged separately for actual fine pieces. -/
theorem selectFamily_gradient_mem {m : ℕ} (D : Geometry E)
    (leaf : ℕ → List ℕ → Blocks m E → ℝ) (hleaf : ∀ k P,ContDiff ℝ 3 (leaf k P))
    (d j : ℕ) (I : List ℕ) (W : Submodule ℝ (Blocks m E)) (x : Blocks m E)
    (hsel : ∀ k P,j ≤ k → k < j+d → ∀ i : Fin ((D k P).n+1),
      gradient (jointSelector m k (D k P) i) x ∈ W)
    (hbase : ∀ P,gradient (leaf (j+d) P) x ∈ W) :
    gradient (selectFamily m D leaf d j I) x ∈ W := by
  induction d generalizing j I with
  | zero => exact hbase I
  | succ d ih =>
    change gradient (fun y => ∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i y*
      selectFamily m D leaf d (j+1) (child I i.val) y) x ∈ W
    apply gradient_sum_mem Finset.univ W _
      (fun i => (jointSelector_contDiff m j (D j I) i 3).mul
        (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val)))
    intro i _
    apply gradient_mul_mem W (jointSelector_contDiff m j (D j I) i 3)
      (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val)) x
    · exact hsel j I le_rfl (by omega) i
    · apply ih (j+1) (child I i.val)
      · intro k P hk hkd a
        exact hsel k P (by omega) (by omega) a
      · intro P
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbase P

theorem selectFamily_gradient_mem_of_blind {m : ℕ} (D : Geometry E)
    (leaf : ℕ → List ℕ → Blocks m E → ℝ) (hleaf : ∀ k P,ContDiff ℝ 3 (leaf k P))
    (d j : ℕ) (I : List ℕ) (hm : j+d < m) (W : Fin m → Submodule ℝ E) (x : Blocks m E)
    (r : ℕ → List ℕ → ℕ)
    (hblind : ∀ k P (_hk : j ≤ k) (hkt : k < j+d),
      BlindNode W x ⟨k,by omega⟩ (D k P) (r k P))
    (hbase : ∀ P,gradient (leaf (j+d) P) x ∈ knownSpace W) :
    gradient (selectFamily m D leaf d j I) x ∈ knownSpace W := by
  apply selectFamily_gradient_mem D leaf hleaf d j I (knownSpace W) x _ hbase
  intro k P hk hkt i
  exact (hblind k P hk hkt).selector_mem i

end Bilevel.ChiCarrier
