import Bilevel.ChiCarrierFineLedger

/-! A common actual ancestor path controls every nonzero joint jet of every
fine piece. The three-piece overlap survives all ancestor/frame/radial maps. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def activeChild (m j : ℕ) (D : Node E) (x : Blocks m E) : Fin (D.n+1) := by
  classical
  exact if h : ∃ i : Fin (D.n+1),∃ q : Fin 4,iteratedFDeriv ℝ q.val (jointSelector m j D i) x≠0
    then Classical.choose h else 0

theorem activeChild_eq (m j : ℕ) (D : Node E) (x : Blocks m E) (i : Fin (D.n+1))
    (q : ℕ) (hq : q≤3) (hi : iteratedFDeriv ℝ q (jointSelector m j D i) x≠0) :
    activeChild m j D x=i := by
  classical
  have he : ∃ l : Fin (D.n+1),∃ k : Fin 4,iteratedFDeriv ℝ k.val (jointSelector m j D l) x≠0 :=
    ⟨i,⟨q,by omega⟩,hi⟩
  rw [activeChild,dif_pos he]
  obtain ⟨k,hk⟩ := Classical.choose_spec he
  exact jointSelector_jets_unique m j D _ i x k.val q (by omega) hq hk hi

def terminalPrefix (m : ℕ) (D : Geometry E) : ℕ → ℕ → List ℕ → Blocks m E → List ℕ
  | 0,_,I,_ => I
  | d+1,j,I,x => terminalPrefix m D d (j+1) (child I (activeChild m j (D j I) x).val) x

theorem selectFamily_nonzero_child (m : ℕ) (D : Geometry E)
    (leaf : ℕ → List ℕ → Blocks m E → ℝ) (hleaf : ∀ j I,ContDiff ℝ 3 (leaf j I))
    (d j : ℕ) (I : List ℕ) (x : Blocks m E) (q : ℕ) (hq : q≤3)
    (hn : iteratedFDeriv ℝ q (selectFamily m D leaf (d+1) j I) x≠0) :
    ∃ i : Fin ((D j I).n+1),iteratedFDeriv ℝ q (fun y => jointSelector m j (D j I) i y*
      selectFamily m D leaf d (j+1) (child I i.val) y) x≠0 := by
  by_contra! hzero
  apply hn
  change iteratedFDeriv ℝ q (fun y => ∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i y*
      selectFamily m D leaf d (j+1) (child I i.val) y) x=0
  rw [iteratedFDeriv_sum (fun i _ => ((jointSelector_contDiff m j (D j I) i 3).mul
    (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val))).of_le
      (show (q:WithTop ℕ∞)≤3 by exact_mod_cast hq))]
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => hzero i)

/-- The path depends only on the actual selectors and the query, and is
shared by all candidate leaves and all derivative orders up to three. -/
theorem selectFamily_jet_at_terminal (m : ℕ) (D : Geometry E)
    (leaf : ℕ → List ℕ → Blocks m E → ℝ) (hleaf : ∀ j I,ContDiff ℝ 3 (leaf j I))
    (d j : ℕ) (I : List ℕ) (x : Blocks m E) (q : ℕ) (hq : q≤3)
    (hn : iteratedFDeriv ℝ q (selectFamily m D leaf d j I) x≠0) :
    ∃ k≤q,iteratedFDeriv ℝ k (leaf (j+d) (terminalPrefix m D d j I x)) x≠0 := by
  induction d generalizing j I q with
  | zero => exact ⟨q,le_rfl,hn⟩
  | succ d ih =>
    obtain ⟨i,hi⟩ := selectFamily_nonzero_child m D leaf hleaf d j I x q hq hn
    obtain ⟨a,ha,hai⟩ := selected_product_jet_selector m j (D j I) i
      (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val)) x q hq hi
    have hchosen := activeChild_eq m j (D j I) x i a (by omega) hai
    have hright : ∃ b≤q,iteratedFDeriv ℝ b (selectFamily m D leaf d (j+1) (child I i.val)) x≠0 := by
      by_contra! hz
      exact hi (ZeroChainResidualBounds.jet_mul_zero_right (jointSelector_contDiff m j (D j I) i 3)
        (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val)) x q hq hz)
    obtain ⟨b,hb,hbi⟩ := hright
    obtain ⟨k,hk,hki⟩ := ih (j+1) (child I i.val) b (by omega) hbi
    refine ⟨k,by omega,?_⟩
    simpa only [terminalPrefix,hchosen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hki

theorem jointFinePiece_jet_latent (m j : ℕ) (D : Node E) (c θ : ℝ) (p : ℕ)
    (x : Blocks m E) (q : ℕ) (hq : q≤3)
    (hn : iteratedFDeriv ℝ q (jointFinePiece m j D c θ p) x≠0) :
    ∃ k≤q,iteratedFDeriv ℝ k (ChiFine.piece D.n (levels θ) (resolution c 1 θ) p)
      (D.width⁻¹ • D.coordinates (block m j x))≠0 := by
  by_contra! hzero
  apply hn
  have hf := ChiFine.piece_contDiff D.n (levels θ) (resolution c 1 θ) p
  have hg := ZeroChainResidualScaled.scaled_contDiff hf (D.ell*D.width^2) D.width
  have hin := (D.coordinates_contDiff 3).comp (block (E:=E) m j).contDiff
  exact flat_jet_comp hin hg x q hq (fun k hk => by
    simp only [Function.comp_apply]
    rw [ZeroChainFlatteningAnnulusScaled.scaled_jet_zero_of_zero hf (D.ell*D.width^2) D.width
      (D.coordinates (block m j x)) k (by omega) (hzero k hk),norm_zero])

def selectedActivePieces (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (c θ : ℝ) (x : Blocks m E) : Finset ℕ := by
  classical
  exact (Finset.range (levels θ+1)).filter (fun p => ∃ q : Fin 4,
    iteratedFDeriv ℝ q.val (selectedFinePiece m D d j I c θ p) x≠0)

theorem selectedActivePieces_subset (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (c θ : ℝ) (x : Blocks m E) :
    let N := D (j+d) (terminalPrefix m D d j I x)
    selectedActivePieces m D d j I c θ x ⊆
      ChiFine.activePieces N.n (levels θ) (resolution c 1 θ)
        (N.width⁻¹ • N.coordinates (block m (j+d) x)) := by
  classical
  dsimp only
  intro p hp
  obtain ⟨hp,q,hq⟩ := Finset.mem_filter.mp hp
  obtain ⟨k,hk,hki⟩ := selectFamily_jet_at_terminal m D
    (fun j I => jointFinePiece m j (D j I) c θ p)
    (fun j I => jointFinePiece_contDiff m j (D j I) c θ p) d j I x q.val (by omega) hq
  obtain ⟨s,hs,hsi⟩ := jointFinePiece_jet_latent m (j+d) (D (j+d) (terminalPrefix m D d j I x))
    c θ p x k (by omega) hki
  exact Finset.mem_filter.mpr ⟨hp,⟨⟨s,by omega⟩,hsi⟩⟩

/-- The actual joint selected family has at most three active fine pieces,
including nonzero mixed jets, with no additional depth or stage factor. -/
theorem actual_selected_piece_overlap (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (c θ : ℝ) (hc : 0<c) (hθ : 1≤θ) (x : Blocks m E) :
    (selectedActivePieces m D d j I c θ x).card≤3 := by
  classical
  apply (Finset.card_le_card (selectedActivePieces_subset m D d j I c θ x)).trans
  apply ChiFine.at_most_three_active_pieces
  · intro p _
    exact resolution_pos c 1 θ hc (by norm_num) hθ p
  · intro p q hpq hq
    exact resolutions_separated c 1 θ hc.le (by norm_num) hθ p q hpq hq

end Bilevel.ChiCarrier
