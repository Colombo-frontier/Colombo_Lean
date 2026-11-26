import Bilevel.ChiLiftedSelection

/-! A single actual ancestor path controls every nonzero mixed jet, even
when leaves depend on a heterogeneous ambient product. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiLiftedCarrier
open ChiBoundedChain ChiRecursive ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def activeChild (m j : ℕ) (D : Node E) (A : X →L[ℝ] Blocks m E) (x : X) : Fin (D.n+1) := by
  classical
  exact if h : ∃ i : Fin (D.n+1),∃ q : Fin 4,iteratedFDeriv ℝ q.val (selector m j D A i) x≠0
    then Classical.choose h else 0

theorem activeChild_eq (m j : ℕ) (D : Node E) (A : X →L[ℝ] Blocks m E) (x : X) (i : Fin (D.n+1))
    (q : ℕ) (hq : q≤3) (hi : iteratedFDeriv ℝ q (selector m j D A i) x≠0) :
    activeChild m j D A x=i := by
  classical
  have he : ∃ l : Fin (D.n+1),∃ k : Fin 4,iteratedFDeriv ℝ k.val (selector m j D A l) x≠0 :=
    ⟨i,⟨q,by omega⟩,hi⟩
  rw [activeChild,dif_pos he]
  obtain ⟨k,hk⟩ := Classical.choose_spec he
  exact selector_jets_unique m j D A _ i x k.val q (by omega) hq hk hi

def terminalPrefix (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E) : ℕ → ℕ → List ℕ → X → List ℕ
  | 0,_,I,_ => I
  | d+1,j,I,x => terminalPrefix m D A d (j+1) (child I (activeChild m j (D j I) A x).val) x

theorem selectFamily_nonzero_child (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E)
    (leaf : ℕ → List ℕ → X → ℝ) (hleaf : ∀ j I,ContDiff ℝ 3 (leaf j I))
    (d j : ℕ) (I : List ℕ) (x : X) (q : ℕ) (hq : q≤3)
    (hn : iteratedFDeriv ℝ q (selectFamily m D A leaf (d+1) j I) x≠0) :
    ∃ i : Fin ((D j I).n+1),iteratedFDeriv ℝ q (fun y => selector m j (D j I) A i y*
      selectFamily m D A leaf d (j+1) (child I i.val) y) x≠0 := by
  by_contra! hzero
  apply hn
  change iteratedFDeriv ℝ q (fun y => ∑ i : Fin ((D j I).n+1),selector m j (D j I) A i y*
      selectFamily m D A leaf d (j+1) (child I i.val) y) x=0
  rw [iteratedFDeriv_sum (fun i _ => ((selector_contDiff m j (D j I) A i 3).mul
    (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val))).of_le
      (show (q:WithTop ℕ∞)≤3 by exact_mod_cast hq))]
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => hzero i)

/-- The path depends only on the actual selectors and the query, and is
shared by all candidate leaves and all derivative orders up to three. -/
theorem selectFamily_jet_at_terminal (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E)
    (leaf : ℕ → List ℕ → X → ℝ) (hleaf : ∀ j I,ContDiff ℝ 3 (leaf j I))
    (d j : ℕ) (I : List ℕ) (x : X) (q : ℕ) (hq : q≤3)
    (hn : iteratedFDeriv ℝ q (selectFamily m D A leaf d j I) x≠0) :
    ∃ k≤q,iteratedFDeriv ℝ k (leaf (j+d) (terminalPrefix m D A d j I x)) x≠0 := by
  induction d generalizing j I q with
  | zero => exact ⟨q,le_rfl,hn⟩
  | succ d ih =>
    obtain ⟨i,hi⟩ := selectFamily_nonzero_child m D A leaf hleaf d j I x q hq hn
    obtain ⟨a,ha,hai⟩ := selected_product_jet_selector m j (D j I) A i
      (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val)) x q hq hi
    have hchosen := activeChild_eq m j (D j I) A x i a (by omega) hai
    have hright : ∃ b≤q,iteratedFDeriv ℝ b (selectFamily m D A leaf d (j+1) (child I i.val)) x≠0 := by
      by_contra! hz
      exact hi (ZeroChainResidualBounds.jet_mul_zero_right (selector_contDiff m j (D j I) A i 3)
        (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val)) x q hq hz)
    obtain ⟨b,hb,hbi⟩ := hright
    obtain ⟨k,hk,hki⟩ := ih (j+1) (child I i.val) b (by omega) hbi
    refine ⟨k,by omega,?_⟩
    simpa only [terminalPrefix,hchosen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hki

def activeLeaves (L : ℕ) (f : ℕ → X → ℝ) (x : X) : Finset ℕ := by
  classical
  exact (Finset.range (L+1)).filter (fun p => ∃ q : Fin 4,iteratedFDeriv ℝ q.val (f p) x≠0)

theorem selected_overlap (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E)
    (leaf : ℕ → ℕ → List ℕ → X → ℝ) (hleaf : ∀ p j I,ContDiff ℝ 3 (leaf p j I))
    (L bound d j : ℕ) (I : List ℕ) (x : X)
    (hb : ∀ j I,(activeLeaves L (fun p => leaf p j I) x).card≤bound) :
    (activeLeaves L (fun p => selectFamily m D A (leaf p) d j I) x).card≤bound := by
  classical
  apply (Finset.card_le_card (show activeLeaves L (fun p => selectFamily m D A (leaf p) d j I) x ⊆
    activeLeaves L (fun p => leaf p (j+d) (terminalPrefix m D A d j I x)) x from ?_)).trans
    (hb (j+d) (terminalPrefix m D A d j I x))
  intro p hp
  obtain ⟨hp,q,hq⟩ := Finset.mem_filter.mp hp
  obtain ⟨k,hk,hki⟩ := selectFamily_jet_at_terminal m D A (leaf p) (hleaf p) d j I x q.val (by omega) hq
  exact Finset.mem_filter.mpr ⟨hp,⟨⟨k,by omega⟩,hki⟩⟩

end Bilevel.ChiLiftedCarrier
