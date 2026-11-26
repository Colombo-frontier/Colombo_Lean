import Bilevel.EndpointTransportOuterFine

/-! The same macro branch carries every nonzero fine jet through order
three. Consequently actual outer-selected physical pieces retain overlap 3. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ZeroChainSchedule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def activeMacro (M : Node E) (P : X →L[ℝ] E) (x : X) : Fin (M.n+1) := by
  classical
  exact if h : ∃ i : Fin (M.n+1),∃ q : Fin 4,iteratedFDeriv ℝ q.val (macroSelector M P i) x≠0
    then Classical.choose h else 0

theorem activeMacro_eq (M : Node E) (P : X →L[ℝ] E) (x : X) (i : Fin (M.n+1))
    (q : ℕ) (hq : q≤3) (hi : iteratedFDeriv ℝ q (macroSelector M P i) x≠0) : activeMacro M P x=i := by
  classical
  have he : ∃ l : Fin (M.n+1),∃ k : Fin 4,iteratedFDeriv ℝ k.val (macroSelector M P l) x≠0 :=
    ⟨i,⟨q,by omega⟩,hi⟩
  rw [activeMacro,dif_pos he]
  obtain ⟨k,hk⟩ := Classical.choose_spec he
  exact macroSelector_jets_unique M P _ i x k.val q (by omega) hq hk hi

theorem macroSelected_jet_at_child (M : Node E) (P : X →L[ℝ] E)
    (f : Fin (M.n+1) → X → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (x : X) (q : ℕ) (hq : q≤3) (hn : iteratedFDeriv ℝ q (macroSelected M P f) x≠0) :
    ∃ k≤q,iteratedFDeriv ℝ k (f (activeMacro M P x)) x≠0 := by
  have hchild : ∃ i : Fin (M.n+1),iteratedFDeriv ℝ q (fun y => macroSelector M P i y*f i y) x≠0 := by
    by_contra! hz
    apply hn
    change iteratedFDeriv ℝ q (fun y => ∑ i : Fin (M.n+1),macroSelector M P i y*f i y) x=0
    rw [iteratedFDeriv_sum (fun i _ => ((macroSelector_contDiff M P i).mul (hf i)).of_le
      (show (q:WithTop ℕ∞)≤3 by exact_mod_cast hq))]
    simp only [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i _ => hz i)
  obtain ⟨i,hi⟩ := hchild
  have hleft : ∃ a≤q,iteratedFDeriv ℝ a (macroSelector M P i) x≠0 := by
    by_contra! hz
    exact hi (ZeroChainResidualBounds.jet_mul_zero_left (macroSelector_contDiff M P i) (hf i) x q hq hz)
  obtain ⟨a,ha,hai⟩ := hleft
  have hchosen := activeMacro_eq M P x i a (by omega) hai
  have hright : ∃ b≤q,iteratedFDeriv ℝ b (f i) x≠0 := by
    by_contra! hz
    exact hi (ZeroChainResidualBounds.jet_mul_zero_right (macroSelector_contDiff M P i) (hf i) x q hq hz)
  obtain ⟨b,hb,hbi⟩ := hright
  exact ⟨b,hb,by rwa [hchosen]⟩

theorem macro_selected_overlap (M : Node E) (P : X →L[ℝ] E) (L : ℕ)
    (f : ℕ → Fin (M.n+1) → X → ℝ) (hf : ∀ p i,ContDiff ℝ 3 (f p i))
    (x : X) (K : ℕ) (hK : ∀ i,(ChiLiftedCarrier.activeLeaves L (fun p => f p i) x).card≤K) :
    (ChiLiftedCarrier.activeLeaves L (fun p => macroSelected M P (f p)) x).card≤K := by
  classical
  apply le_trans (Finset.card_le_card (show ChiLiftedCarrier.activeLeaves L (fun p => macroSelected M P (f p)) x⊆
    ChiLiftedCarrier.activeLeaves L (fun p => f p (activeMacro M P x)) x from ?_)) (hK _)
  intro p hp
  obtain ⟨hp,q,hq⟩ := Finset.mem_filter.mp hp
  obtain ⟨k,hk,hki⟩ := macroSelected_jet_at_child M P (f p) (hf p) x q.val (by omega) hq
  exact Finset.mem_filter.mpr ⟨hp,⟨⟨k,by omega⟩,hki⟩⟩

theorem outer_physical_fine_overlap {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d : ℕ) (x : X) :
    (ChiLiftedCarrier.activeLeaves (levels P.θ) (fun p => outerPhysicalFinePiece m Q M macroP G A B P p d) x).card≤3 :=
  macro_selected_overlap M macroP (levels P.θ)
    (fun p i => selectedPhysicalFinePiece m G A B Q P p d 0 [i.val])
    (fun p i => selectedPhysicalFinePiece_contDiff m G A B Q P p d 0 [i.val]) x 3
    (fun i => selected_physical_fine_overlap m G A B Q P d 0 [i.val] x)

end Bilevel.EndpointTransportResponse
