import Bilevel.ChiOuterCarrierSelectors
import Bilevel.ChiCarrierSelectedLedger
import Bilevel.ChiCarrierFineLedger

/-! Joint outer selection using the actual one-sided macro selectors.
The transfer preserves both the carrier and separated fine envelopes. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerSelected (m : ℕ) (M : Node E) (f : Fin (M.n+1) → Blocks m F → ℝ)
    (z : Joint E (Blocks m F)) : ℝ := ∑ i : Fin (M.n+1),jointOuterSelector m M i z*f i z.snd

omit [CompleteSpace F] in
theorem outerSelected_contDiff (m : ℕ) (M : Node E) (f : Fin (M.n+1) → Blocks m F → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) : ContDiff ℝ 3 (outerSelected m M f) :=
  ContDiff.sum (fun i _ => (jointOuterSelector_contDiff m M i).mul
    ((hf i).comp (innerProjection (E:=E) (F:=F) m).contDiff))

omit [CompleteSpace F] in
theorem outerSelected_term_selector (m : ℕ) (M : Node E) (i : Fin (M.n+1))
    {f : Blocks m F → ℝ} (hf : ContDiff ℝ 3 f) (z : Joint E (Blocks m F))
    (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (fun y : Joint E (Blocks m F) => jointOuterSelector m M i y*f y.snd) z≠0) :
    ∃ q≤k,iteratedFDeriv ℝ q (jointOuterSelector m M i) z≠0 := by
  by_contra! hz
  exact hn (ZeroChainResidualBounds.jet_mul_zero_left (jointOuterSelector_contDiff m M i)
    (hf.comp (innerProjection (E:=E) (F:=F) m).contDiff) z k hk hz)

omit [CompleteSpace F] in
theorem outerSelected_sum_bound (m : ℕ) (M : Node E) (f : Fin (M.n+1) → Blocks m F → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) (z : Joint E (Blocks m F)) (k : ℕ) (hk : k≤3)
    (B : ℝ) (hB : 0≤B)
    (hb : ∀ i,‖iteratedFDeriv ℝ k (fun y : Joint E (Blocks m F) => jointOuterSelector m M i y*f i y.snd) z‖≤B) :
    ‖iteratedFDeriv ℝ k (outerSelected m M f) z‖≤B := by
  change ‖iteratedFDeriv ℝ k (fun y : Joint E (Blocks m F) =>
    ∑ i : Fin (M.n+1),jointOuterSelector m M i y*(f i ∘ innerProjection m) y) z‖≤B
  rw [iteratedFDeriv_sum (fun i _ => ((jointOuterSelector_contDiff m M i).mul
    ((hf i).comp (innerProjection (E:=E) (F:=F) m).contDiff)).of_le
      (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  apply norm_sum_le_of_exclusive _ B hB hb
  intro i l hil hi
  by_contra hl
  obtain ⟨a,ha,hai⟩ := outerSelected_term_selector m M i (hf i) z k hk hi
  obtain ⟨b,hb,hbl⟩ := outerSelected_term_selector m M l (hf l) z k hk hl
  exact hil (jointOuterSelector_jets_unique m M i l z a b (by omega) (by omega) hai hbl)

theorem constructed_outer_carrier_step : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (m : ℕ) (M : Node E),0<M.width → M.width≤M.radius →
      ∀ (f : Fin (M.n+1) → Blocks m F → ℝ),(∀ i,ContDiff ℝ 3 (f i)) →
      ∀ (B N ℓ h : ℝ),0≤B → 1≤N → 0≤ℓ → 0<h → h*Real.sqrt N≤M.width →
      ∀ (z : Joint E (Blocks m F)) (k : ℕ),k≤3 →
      (∀ i q,q≤k → ‖iteratedFDeriv ℝ q (f i) z.snd‖≤B*ledgerScale N ℓ h q) →
      ‖iteratedFDeriv ℝ k (outerSelected m M f) z‖≤Cs*B*ledgerScale N ℓ h k := by
  obtain ⟨C,hC,hs⟩ := constructed_outer_selector_jets
  have hC0 : 0≤C := by linarith
  refine ⟨8*C,by linarith,fun E F _ _ _ _ _ _ m M hh hhR f hf B N ℓ h hB hN hℓ hh0 hwidth z k hk hb => ?_⟩
  have hscale := ledgerScale_nonneg (N:=N) (by linarith) hℓ hh0.le k
  apply outerSelected_sum_bound m M f hf z k hk _ (by positivity)
  intro i
  exact coarser_product_ledger (jointOuterSelector_contDiff m M i)
    ((hf i).comp (innerProjection (E:=E) (F:=F) m).contDiff)
    C B N ℓ h M.width hC0 hB hN hℓ hh0 hh hwidth z k hk
    (fun q hq => hs E F M hh hhR m i z q (by omega))
    (fun q hq => (contraction_jet_bound (innerProjection (E:=E) (F:=F) m)
      (innerProjection_norm_le m) (hf i) z q (by omega)).trans (hb i q hq))

theorem constructed_outer_fine_step : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (m : ℕ) (M : Node E),0<M.width → M.width≤M.radius →
      ∀ (f : Fin (M.n+1) → Blocks m F → ℝ),(∀ i,ContDiff ℝ 3 (f i)) →
      ∀ (B a V δ : ℝ),0≤B → 0≤a → 0≤V → 0<δ → δ≤M.width → a≤V*M.width →
      ∀ (z : Joint E (Blocks m F)) (k : ℕ),k≤3 →
      (∀ i q,q≤k → ‖iteratedFDeriv ℝ q (f i) z.snd‖≤B*fineScale a V δ q) →
      ‖iteratedFDeriv ℝ k (outerSelected m M f) z‖≤Cs*B*fineScale a V δ k := by
  obtain ⟨C,hC,hs⟩ := constructed_outer_selector_jets
  have hC0 : 0≤C := by linarith
  refine ⟨8*C,by linarith,fun E F _ _ _ _ _ _ m M hh hhR f hf B a V δ hB ha hV hδ hδM haM z k hk hb => ?_⟩
  have hscale := fineScale_nonneg ha hV hδ.le k
  apply outerSelected_sum_bound m M f hf z k hk _ (by positivity)
  intro i
  exact coarser_fine_product (jointOuterSelector_contDiff m M i)
    ((hf i).comp (innerProjection (E:=E) (F:=F) m).contDiff)
    C B a V δ M.width hC0 hB ha hV hδ hh hδM haM z k hk
    (fun q hq => hs E F M hh hhR m i z q (by omega))
    (fun q hq => (contraction_jet_bound (innerProjection (E:=E) (F:=F) m)
      (innerProjection_norm_le m) (hf i) z q (by omega)).trans (hb i q hq))

end Bilevel.ChiOuter
