import Bilevel.EndpointTransportVirtualRelevantData
import Bilevel.EndpointTransportVirtualInverseGerm

/-! Observable physical prefix certificates. Ordinary arrays are required
only at ancestor levels k<J; arbitrary unused terminal arrays are accepted.
A proof-only completion fills those unused arrays before applying frozen
analytic lemmas, then global relevant-data invariance removes the filler. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiTreeProgress ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def completeOrdinaryColumns {D : ℕ} (G : Geometry (Block D)) (J : ℕ)
    (C : ∀ k I,Fin ((G k I).n+1) → Block D) (k : ℕ) (I : List ℕ) :
    Fin ((G k I).n+1) → Block D :=
  if k<J then C k I else fun a => (G k I).frame (basis a)

theorem completeOrdinaryColumns_below {D : ℕ} (G : Geometry (Block D)) (J : ℕ)
    (C : ∀ k I,Fin ((G k I).n+1) → Block D) (k : ℕ) (I : List ℕ) (hk : k<J) :
    completeOrdinaryColumns G J C k I=C k I := by simp only [completeOrdinaryColumns,if_pos hk]

structure ObservablePhysicalPrefixCertificate {J n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D) : Prop where
  geometry : PhysicalPrefixGeometry Q G P W Z r
  macro_prefix : ∀ a : Fin (M.n+1),a.val<rM → macroColumns a=M.frame (basis a)
  ordinary_prefix : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a)
  source_mono : ∀ A,r J A≤sourceCount J A
  source_prefix : ∀ A,∀ a : Fin ((G J A).n+1),a.val<sourceCount J A →
    S J A a=endpointFrame Q (G J A).frame 0 (basis a)
  target_prefix : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A →
    T J A a=endpointFrame Q (G J A).frame (Fin.last (n+1)) (basis a)
  source_known : ∀ A,∀ a : Fin ((G J A).n+1),a.val<sourceCount J A → Q 0 ((G J A).frame (basis a))∈Z 0
  frontier : ∀ i : Fin (M.n+1),i.val≤rM → FrontierAdvance G r sourceCount J 0 [i.val]
  ordinary_margin : ∀ k A,∀ hk : k<J,∀ a : Fin ((G k A).n+1),r k A≤a.val →
    (G k A).radius*‖(W ⟨k,hk⟩).orthogonalProjection ((G k A).frame (basis a))‖≤(G k A).width/8

omit [CompleteSpace E] in
theorem ObservablePhysicalPrefixCertificate.complete {J n D : ℕ} {Q : Rotations n D} {M : Node E}
    {G : Geometry (Block D)} {P : ChiFine.Parameters}
    {W : Fin J → Submodule ℝ (Block D)} {Z : Index n → Submodule ℝ (Block D)}
    {rM : ℕ} {r sourceCount : ℕ → List ℕ → ℕ} {macroColumns : Fin (M.n+1) → E}
    {columns : ∀ k I,Fin ((G k I).n+1) → Block D}
    {S T : ∀ k I,Fin ((G k I).n+1) → Physical n D}
    (h : ObservablePhysicalPrefixCertificate Q M G P W Z rM r sourceCount macroColumns columns S T) :
    PhysicalPrefixCertificate Q M G P W Z rM r sourceCount macroColumns
      (completeOrdinaryColumns G J columns) S T := by
  refine ⟨h.geometry,h.macro_prefix,?_,h.source_mono,h.source_prefix,h.target_prefix,h.source_known,
    h.frontier,h.ordinary_margin⟩
  intro k A a ha
  by_cases hk : k<J
  · rw [completeOrdinaryColumns_below G J columns k A hk]
    exact h.ordinary_prefix k A hk a ha
  · simp only [completeOrdinaryColumns,if_neg hk]

end Bilevel.EndpointTransportResponse
