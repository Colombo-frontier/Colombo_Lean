import Bilevel.ChiCarrierForcePath

/-! Actual selected gradients need leaf support only on the selector path.
This avoids requiring disclosure of every terminal frontier in the tree. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem selectFamily_gradient_mem_at_path {m : ℕ} (D : Geometry E)
    (leaf : ℕ → List ℕ → Blocks m E → ℝ) (hleaf : ∀ k P,ContDiff ℝ 3 (leaf k P))
    (d j : ℕ) (I : List ℕ) (W : Submodule ℝ (Blocks m E)) (x : Blocks m E)
    (hsel : ∀ k P,j≤k → k<j+d → ∀ i : Fin ((D k P).n+1),
      gradient (jointSelector m k (D k P) i) x∈W)
    (hbase : gradient (leaf (j+d) (terminalPrefix m D d j I x)) x∈W) :
    gradient (selectFamily m D leaf d j I) x∈W := by
  induction d generalizing j I with
  | zero => exact hbase
  | succ d ih =>
    change gradient (fun y => ∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i y*
      selectFamily m D leaf d (j+1) (child I i.val) y) x∈W
    apply gradient_sum_mem Finset.univ W _
      (fun i => (jointSelector_contDiff m j (D j I) i 3).mul
        (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val)))
    intro i _
    rw [gradient_mul_C3 (jointSelector_contDiff m j (D j I) i 3)
      (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val))]
    apply W.add_mem
    · by_cases hi : jointSelector m j (D j I) i x=0
      · rw [hi,zero_smul]
        exact W.zero_mem
      · apply W.smul_mem
        apply ih (j+1) (child I i.val)
        · intro k P hk hkd a
          exact hsel k P (by omega) (by omega) a
        · have ha := jointSelector_ne_zero_activeChild m j (D j I) x i hi
          simpa only [terminalPrefix,ha,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbase
    · exact W.smul_mem _ (hsel j I le_rfl (by omega) i)

theorem selectedFinePiece_gradient_mem_at_path {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d<m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D j d hm W x r)
    (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v)
    (hell : 0≤(D (j+d) (terminalPrefix m D d j I x)).ell)
    (hnew : ∀ k : Fin ((D (j+d) (terminalPrefix m D d j I x)).n+1),
      k.val=r (j+d) (terminalPrefix m D d j I x) →
      (D (j+d) (terminalPrefix m D d j I x)).frame (basis k)∈W ⟨j+d,hm⟩)
    (p : ℕ) : gradient (selectedFinePiece m D d j I c v p) x∈knownSpace W := by
  apply selectFamily_gradient_mem_at_path D _
    (fun k P => jointFinePiece_contDiff m k (D k P) c v p) d j I (knownSpace W) x
    (fun k P hk hkt i => (htree k P hk (by omega)).selector_mem i)
  let P := terminalPrefix m D d j I x
  have hb := htree (j+d) P (by omega) le_rfl
  apply jointFinePiece_gradient_mem W x ⟨j+d,hm⟩ (D (j+d) P) c v hc hcs hv hell
    hb.width_pos hb.radius_pos p (r (j+d) P) hb.query_mem _ hb.blind
  intro k hk
  by_cases hkr : k.val<r (j+d) P
  · exact hb.columns_mem k hkr
  · exact hnew k (by change k.val=r (j+d) P;omega)

theorem selectedCoupling_tangent_support_at_path {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d<m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D j d hm W x r)
    (c v s : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v)
    (hell : 0≤(D (j+d) (terminalPrefix m D d j I x)).ell)
    (hnew : ∀ k : Fin ((D (j+d) (terminalPrefix m D d j I x)).n+1),
      k.val=r (j+d) (terminalPrefix m D d j I x) →
      (D (j+d) (terminalPrefix m D d j I x)).frame (basis k)∈W ⟨j+d,hm⟩) :
    gradient (fun y => selectedCoupling m D d j I c v (CompensatedMean.pack (Blocks m E) y s 0)) x∈knownSpace W := by
  rw [funext (selectedCoupling_slice_eq m D d j I c v s)]
  apply gradient_sum_mem _ (knownSpace W) _
    (fun p => (selectedFinePiece_contDiff m D d j I c v p).mul contDiff_const)
  intro p _
  exact gradient_mul_mem (knownSpace W) (selectedFinePiece_contDiff m D d j I c v p) contDiff_const x
    (selectedFinePiece_gradient_mem_at_path D d j I hm W x r htree c v hc hcs hv hell hnew p)
    (gradient_const_mem (knownSpace W) _ _)

end Bilevel.ChiCarrier
