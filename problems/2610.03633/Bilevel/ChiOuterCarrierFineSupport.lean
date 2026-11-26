import Bilevel.ChiOuterCarrierFineLedger

/-! The actual one-sided outer selection preserves the common fine-piece
path and the at-most-three nonzero joint jets. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def activeOuter (m : ℕ) (M : Node E) (z : Joint E (Blocks m F)) : Fin (M.n+1) := by
  classical
  exact if h : ∃ i : Fin (M.n+1),∃ q : Fin 4,iteratedFDeriv ℝ q.val (jointOuterSelector m M i) z≠0
    then Classical.choose h else 0

omit [CompleteSpace F] in
theorem activeOuter_eq (m : ℕ) (M : Node E) (z : Joint E (Blocks m F)) (i : Fin (M.n+1))
    (q : ℕ) (hq : q≤3) (hi : iteratedFDeriv ℝ q (jointOuterSelector m M i) z≠0) :
    activeOuter m M z=i := by
  classical
  have he : ∃ l : Fin (M.n+1),∃ k : Fin 4,iteratedFDeriv ℝ k.val (jointOuterSelector m M l) z≠0 :=
    ⟨i,⟨q,by omega⟩,hi⟩
  rw [activeOuter,dif_pos he]
  obtain ⟨k,hk⟩ := Classical.choose_spec he
  exact jointOuterSelector_jets_unique m M _ i z k.val q (by omega) hq hk hi

omit [CompleteSpace F] in
theorem outerSelected_nonzero_child (m : ℕ) (M : Node E)
    (f : Fin (M.n+1) → Blocks m F → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (z : Joint E (Blocks m F)) (q : ℕ) (hq : q≤3)
    (hn : iteratedFDeriv ℝ q (outerSelected m M f) z≠0) :
    ∃ i : Fin (M.n+1),iteratedFDeriv ℝ q (fun y : Joint E (Blocks m F) =>
      jointOuterSelector m M i y*f i y.snd) z≠0 := by
  by_contra! hz
  apply hn
  change iteratedFDeriv ℝ q (fun y : Joint E (Blocks m F) => ∑ i : Fin (M.n+1),
    jointOuterSelector m M i y*(f i ∘ innerProjection m) y) z=0
  rw [iteratedFDeriv_sum (fun i _ => ((jointOuterSelector_contDiff m M i).mul
    ((hf i).comp (innerProjection (E:=E) (F:=F) m).contDiff)).of_le
      (show (q:WithTop ℕ∞)≤3 by exact_mod_cast hq))]
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => hz i)

omit [CompleteSpace F] in
theorem outerSelected_jet_at_child (m : ℕ) (M : Node E)
    (f : Fin (M.n+1) → Blocks m F → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (z : Joint E (Blocks m F)) (q : ℕ) (hq : q≤3)
    (hn : iteratedFDeriv ℝ q (outerSelected m M f) z≠0) :
    ∃ k≤q,iteratedFDeriv ℝ k (f (activeOuter m M z)) z.snd≠0 := by
  obtain ⟨i,hi⟩ := outerSelected_nonzero_child m M f hf z q hq hn
  obtain ⟨a,ha,hai⟩ := outerSelected_term_selector m M i (hf i) z q hq hi
  have hchosen := activeOuter_eq m M z i a (by omega) hai
  have hright : ∃ b≤q,iteratedFDeriv ℝ b (f i ∘ innerProjection m) z≠0 := by
    by_contra! hz
    exact hi (ZeroChainResidualBounds.jet_mul_zero_right (jointOuterSelector_contDiff m M i)
      ((hf i).comp (innerProjection (E:=E) (F:=F) m).contDiff) z q hq hz)
  obtain ⟨b,hb,hbi⟩ := hright
  have hlatent : ∃ k≤b,iteratedFDeriv ℝ k (f i) z.snd≠0 := by
    by_contra! hz
    apply hbi
    exact flat_jet_comp (innerProjection (E:=E) (F:=F) m).contDiff (hf i) z b (by omega)
      (fun k hk => by change ‖iteratedFDeriv ℝ k (f i) z.snd‖=0;rw [hz k hk,norm_zero])
  obtain ⟨k,hk,hki⟩ := hlatent
  exact ⟨k,by omega,by rwa [hchosen]⟩

def outerActivePieces (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (z : Joint E (Blocks m F)) : Finset ℕ := by
  classical
  exact (Finset.range (levels θ+1)).filter (fun p => ∃ q : Fin 4,
    iteratedFDeriv ℝ q.val (outerFinePiece m M D d c θ p) z≠0)

theorem outerActivePieces_subset (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (z : Joint E (Blocks m F)) :
    outerActivePieces m M D d c θ z⊆selectedActivePieces m D d 0 [(activeOuter m M z).val] c θ z.snd := by
  classical
  intro p hp
  obtain ⟨hp,q,hq⟩ := Finset.mem_filter.mp hp
  obtain ⟨k,hk,hki⟩ := outerSelected_jet_at_child m M
    (fun i => selectedFinePiece m D d 0 [i.val] c θ p)
    (fun i => selectedFinePiece_contDiff m D d 0 [i.val] c θ p) z q.val (by omega) hq
  exact Finset.mem_filter.mpr ⟨hp,⟨⟨k,by omega⟩,hki⟩⟩

theorem actual_outer_piece_overlap (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hθ : 1≤θ) (z : Joint E (Blocks m F)) :
    (outerActivePieces m M D d c θ z).card≤3 :=
  (Finset.card_le_card (outerActivePieces_subset m M D d c θ z)).trans
    (actual_selected_piece_overlap m D d 0 _ c θ hc hθ z.snd)

end Bilevel.ChiOuter
