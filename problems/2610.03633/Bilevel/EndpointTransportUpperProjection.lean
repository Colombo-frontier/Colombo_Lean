import Bilevel.EndpointTransportUpperReply
import Bilevel.EndpointTransportVirtualInverseGerm

/-! The same actual prebatch projection certificate supplies the full upper
reply at the original query, with no inverse or source-column advance. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalUpper_gradient_eq_prefix_of_projection {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (P : ChiFine.Parameters) (hJ : 0<J)
    (ρ R : ℝ) (b : Normals s)
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D) (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (h : PhysicalPrefixCertificate Q M G P W Z rM r sourceCount macroColumns columns S T)
    (hmw : 0<M.width) (hmR : 0<M.radius)
    (hmfuture : ∀ i : Fin (M.n+1),rM ≤ i.val → r 0 [i.val]≤(G 0 [i.val]).n)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16)
    (x : HybridOuter E (Blocks J (Block D)) D)
    (y : HybridVariables (Blocks J (Block D)) (Normals s) n D) (hy : y∈physicalNormalKnown W Z s)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates x.fst.fst a|≤M.width/8) :
    gradient (physicalUpper (U:=Blocks J (Block D)) (D:=D) (physicalUpperBase J Q M ν G J ρ R) b) (pack x y)=
    gradient (physicalUpper (U:=Blocks J (Block D)) (D:=D)
      (prefixPhysicalUpperBase J M ν G J ρ R rM r macroColumns columns T) b) (pack x y) := by
  have hyt : y.fst∈physicalTangentKnown W Z := ((mem_jointKnown _ _ y).mp hy).1
  have hy' := (mem_physicalTangentKnown W Z y.fst).mp hyt
  have hradius (k : ℕ) (A : List ℕ) (hk : k≤J) : 0<(G k A).radius := by
    by_cases he : k=J
    · simpa only [he] using h.geometry.radius_pos A
    · exact (h.geometry.ancestors k A (by omega)).radius_pos
  apply physicalUpper_gradient_eq_prefix Q M ν G J hJ ρ R rM r macroColumns columns T
    h.macro_prefix h.ordinary_prefix hmw (fun A => h.geometry.level_width_pos 0 A (by omega))
    (fun k A hk => h.geometry.parent_pos k A (by omega))
    (fun k A hk => h.geometry.width_le_parent k A (by omega)) h.target_prefix hmfuture
    (h.geometry.future 0 hJ) b (pack x y) hmb ?_ ?_ hmR hradius δ hδ hδM hδG
  · intro k A hk a ha
    have hc := (G k A).coordinate_projection_bound (hradius k A (by omega)) (W ⟨k,hk⟩)
      ⟨y.fst.fst ⟨k,hk⟩,hy'.1 _⟩ a
    have hp := h.ordinary_margin k A hk a ha
    change |(G k A).coordinates (block J k y.fst.fst) a|≤(G k A).width/8
    simpa only [block,dif_pos hk,PiLp.proj_apply] using hc.trans hp
  · intro A
    exact h.geometry.target_blind_at_point A y.fst hyt

end Bilevel.EndpointTransportResponse
