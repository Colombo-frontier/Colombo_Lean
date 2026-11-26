import Bilevel.EndpointTransportVirtualInverseEquality
import Bilevel.EndpointTransportHierarchyInverse
import Bilevel.EndpointTransportHierarchyBlind

/-! The constructed physical inverse lies in the actual disclosed-data
germ. Every support and blind-tail premise is discharged from the prebatch
known spaces, their column projections, and reachable prefix advancement. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiTreeProgress ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure PhysicalPrefixCertificate {J n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D) : Prop where
  geometry : PhysicalPrefixGeometry Q G P W Z r
  macro_prefix : ∀ a : Fin (M.n+1),a.val<rM → macroColumns a=M.frame (basis a)
  ordinary_prefix : ∀ k A,∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a)
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
theorem PhysicalPrefixCertificate.frontierKnown {J n D : ℕ} {Q : Rotations n D} {M : Node E}
    {G : Geometry (Block D)} {P : ChiFine.Parameters}
    {W : Fin J → Submodule ℝ (Block D)} {Z : Index n → Submodule ℝ (Block D)}
    {rM : ℕ} {r sourceCount : ℕ → List ℕ → ℕ} {macroColumns : Fin (M.n+1) → E}
    {columns : ∀ k I,Fin ((G k I).n+1) → Block D}
    {S T : ∀ k I,Fin ((G k I).n+1) → Physical n D}
    (h : PhysicalPrefixCertificate Q M G P W Z rM r sourceCount macroColumns columns S T)
    (i : Fin (M.n+1)) (hi : i.val≤rM) :
    FrontierKnown G r (Submodule.comap (Q 0).toLinearMap (Z 0)) J 0 [i.val] := by
  apply (h.frontier i hi).frontierKnown
  rw [Nat.zero_add]
  exact h.source_known

theorem physicalHierarchy_inverse_core_germ {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (hR : ∀ i : Fin J,0<R (i.val+1))
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D) (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (h : PhysicalPrefixCertificate Q M G P W Z rM r sourceCount macroColumns columns S T)
    (hmw : 0<M.width) (hmR : 0<M.radius) (κ : NNReal) (hκ : κ<1)
    (hH : ∀ z,‖iteratedFDeriv ℝ 2
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn) z‖≤(κ:ℝ))
    (hF : LipschitzWith κ (gradient (physicalExtension (U:=Blocks J (Block D)) (D:=D)
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn))))
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16)
    (x : HybridOuter E (Blocks J (Block D)) D)
    (y : HybridVariables (Blocks J (Block D)) (Normals s) n D) (hy : y∈physicalNormalKnown W Z s)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates x.fst.fst a|≤M.width/8) :
    let z := jointSolution hF hκ x y
    physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn =ᶠ[
      𝓝 (pack (pack x.fst.fst z.fst) z.snd)]
      prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
        rM r sourceCount macroColumns columns S T := by
  let z := jointSolution hF hκ x y
  have hz : z∈physicalNormalKnown W Z s :=
    physicalHierarchy_inverse_mem Q M G P coarseIndex radialIndex fineIndex ρ R dn hR W Z r h.geometry
      κ hκ hH hF rM x hmw hmb h.frontierKnown y hy
  have hzt : z.fst∈physicalTangentKnown W Z := ((mem_jointKnown _ _ z).mp hz).1
  have hz' := (mem_physicalTangentKnown W Z z.fst).mp hzt
  have hradius (k : ℕ) (A : List ℕ) (hk : k≤J) : 0<(G k A).radius := by
    by_cases he : k=J
    · simpa only [he] using h.geometry.radius_pos A
    · exact (h.geometry.ancestors k A (by omega)).radius_pos
  apply physicalHierarchyExtension_eventuallyEq_prefix Q M G P coarseIndex radialIndex fineIndex ρ R dn
    rM r sourceCount macroColumns columns S T h.macro_prefix h.ordinary_prefix hmw
    (fun k A hk => h.geometry.level_width_pos k A hk) h.geometry.parent_pos h.geometry.width_le_parent
    h.geometry.fine_ell h.geometry.fine_width h.source_mono h.source_prefix h.target_prefix
    h.geometry.future h.frontier hmR hradius δ hδ hδM hδG (pack (pack x.fst.fst z.fst) z.snd) hmb
  · intro k A hk a ha
    have hc := (G k A).coordinate_projection_bound (hradius k A (by omega)) (W ⟨k,hk⟩)
      ⟨z.fst.fst ⟨k,hk⟩,hz'.1 _⟩ a
    have hp := h.ordinary_margin k A hk a ha
    change |(G k A).coordinates (block J k z.fst.fst) a|≤(G k A).width/8
    simpa only [block,dif_pos hk,PiLp.proj_apply] using hc.trans hp
  · intro A
    exact h.geometry.target_blind_at_point A z.fst hzt

end Bilevel.EndpointTransportResponse
