import Bilevel.ChiFrontierProtocol

/-! Actual selected fine-gradient support under finite prefix bookkeeping.
Future selectors vanish from the actual blind coordinates; completed older
subtrees require no new columns. Only the unfinished frontier is disclosed. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem selectFamily_gradient_mem_frontier {m : ℕ} (D : Geometry E)
    (leaf : ℕ → List ℕ → Blocks m E → ℝ) (hleaf : ∀ k P,ContDiff ℝ 3 (leaf k P))
    (d j : ℕ) (I : List ℕ) (V : Submodule ℝ E) (W : Submodule ℝ (Blocks m E)) (x : Blocks m E)
    (r : ℕ → List ℕ → ℕ) (hfront : FrontierKnown D r V d j I)
    (hsel : ∀ k P,j≤k → k<j+d → ∀ i : Fin ((D k P).n+1),
      gradient (jointSelector m k (D k P) i) x∈W)
    (hzero : ∀ k P,j≤k → k<j+d → ∀ i : Fin ((D k P).n+1),r k P < i.val →
      jointSelector m k (D k P) i x=0)
    (hbase : ∀ P,FrontierKnown D r V 0 (j+d) P → gradient (leaf (j+d) P) x∈W) :
    gradient (selectFamily m D leaf d j I) x∈W := by
  induction d generalizing j I with
  | zero => exact hbase I hfront
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
      · have hir : i.val≤r j I := by
          by_contra hh
          exact hi (hzero j I le_rfl (by omega) i (by omega))
        apply W.smul_mem
        apply ih (j+1) (child I i.val) (hfront i hir)
        · intro k P hk hkd a
          exact hsel k P (by omega) (by omega) a
        · intro k P hk hkd a ha
          exact hzero k P (by omega) (by omega) a ha
        · intro P hp
          have hh := hbase P (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp)
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    · exact W.smul_mem _ (hsel j I le_rfl (by omega) i)

theorem selectedFinePiece_frontier_support {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d<m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D j d hm W x r) (hfront : FrontierKnown D r (W ⟨j+d,hm⟩) d j I)
    (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v) (hell : ∀ P,0≤(D (j+d) P).ell)
    (p : ℕ) : gradient (selectedFinePiece m D d j I c v p) x∈knownSpace W := by
  apply selectFamily_gradient_mem_frontier D _
    (fun k P => jointFinePiece_contDiff m k (D k P) c v p) d j I (W ⟨j+d,hm⟩) (knownSpace W) x r hfront
    (fun k P hk hkt i => (htree k P hk (by omega)).selector_mem i)
    (fun k P hk hkt i hi => (htree k P hk (by omega)).selector_future_zero i hi)
  intro P hp
  have hb := htree (j+d) P (by omega) le_rfl
  apply jointFinePiece_gradient_mem W x ⟨j+d,hm⟩ (D (j+d) P) c v hc hcs hv (hell P)
    hb.width_pos hb.radius_pos p (r (j+d) P) hb.query_mem _ hb.blind
  intro k hk
  by_cases hkr : k.val<r (j+d) P
  · exact hb.columns_mem k hkr
  · exact hp k (by omega)

theorem selectedCoupling_frontier_support {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d<m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D j d hm W x r) (hfront : FrontierKnown D r (W ⟨j+d,hm⟩) d j I)
    (c v s : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v) (hell : ∀ P,0≤(D (j+d) P).ell) :
    gradient (fun y => selectedCoupling m D d j I c v (CompensatedMean.pack (Blocks m E) y s 0)) x∈knownSpace W := by
  rw [funext (selectedCoupling_slice_eq m D d j I c v s)]
  apply gradient_sum_mem _ (knownSpace W) _
    (fun p => (selectedFinePiece_contDiff m D d j I c v p).mul contDiff_const)
  intro p _
  exact gradient_mul_mem (knownSpace W) (selectedFinePiece_contDiff m D d j I c v p) contDiff_const x
    (selectedFinePiece_frontier_support D d j I hm W x r htree hfront c v hc hcs hv hell p)
    (gradient_const_mem (knownSpace W) _ _)

end Bilevel.ChiCarrier
