import Bilevel.EndpointTransportVirtualValues
import Bilevel.ChiUniformBlindNeighborhood

/-! Uniform open physical blind neighborhoods, including countably many
totalized terminal nodes and the full physical radial compression. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def physicalFullProjection {J n D s : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : PhysicalBase E J n D →L[ℝ] F) : Full (PhysicalBase E J n D) s →L[ℝ] F :=
  L.comp jointFstLinear

omit [CompleteSpace E] in
theorem physicalFullProjection_norm_le {J n D s : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : PhysicalBase E J n D →L[ℝ] F) (hL : ‖L‖≤1) :
    ‖physicalFullProjection (s:=s) L‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖L z.fst‖≤1*‖z‖
  rw [one_mul]
  exact (L.le_opNorm z.fst).trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans
    (WithLp.norm_fst_le (PhysicalBase E J n D) z))

theorem physical_eventually_blind_uniform {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (G : Geometry (Block D)) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (hmR : 0<M.radius) (hR : ∀ k A,k≤J → 0<(G k A).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16)
    (z : Full (PhysicalBase E J n D) s)
    (hm : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates z.fst.fst a|≤M.width/8)
    (ho : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block J k z.fst.snd.fst) a|≤(G k A).width/8)
    (ht : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      |(physicalCoordinates Q (G J A) z.fst.snd.snd).snd a|≤(G J A).width/8) :
    ∀ᶠ y in 𝓝 z,
      (∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates y.fst.fst a|≤M.width/4) ∧
      (∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
        |(G k A).coordinates (block J k y.fst.snd.fst) a|≤(G k A).width/4) ∧
      (∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
        |(physicalCoordinates Q (G J A) y.fst.snd.snd).snd a|≤3*(G J A).width/16) := by
  have hmacro := eventually_blind_uniform (fun _ : Unit => M) (fun _ => hmR)
    (fun _ => physicalFullProjection (s:=s) (baseMacroProjection (E:=E) J n D))
    (fun _ => physicalFullProjection_norm_le _ (baseMacroProjection_norm_le J n D))
    (fun _ => rM) (fun _ => M.width/4) δ hδ z (by
      intro _ a ha
      change |M.coordinates z.fst.fst a|≤M.width/4-δ
      have hb := hm a ha
      linarith)
  have hop (k : ℕ) : ‖(block (E:=Block D) J k).comp (baseOrdinaryProjection (E:=E) J n D)‖≤1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact (mul_le_mul (block_norm_le (E:=Block D) J k) (baseOrdinaryProjection_norm_le (E:=E) J n D)
      (norm_nonneg (baseOrdinaryProjection (E:=E) J n D)) zero_le_one).trans_eq (one_mul _)
  have hordinary := eventually_blind_uniform
    (fun i : Fin J × List ℕ => G i.1.val i.2) (fun i => hR _ _ (by have := i.1.isLt;omega))
    (fun i => physicalFullProjection (s:=s) ((block (E:=Block D) J i.1.val).comp (baseOrdinaryProjection (E:=E) J n D)))
    (fun i => physicalFullProjection_norm_le _ (hop i.1.val))
    (fun i => r i.1.val i.2) (fun i => (G i.1.val i.2).width/4) δ hδ z (by
      intro i a ha
      change |(G i.1.val i.2).coordinates (block J i.1.val z.fst.snd.fst) a|≤(G i.1.val i.2).width/4-δ
      have hb := ho i.1.val i.2 i.1.isLt a ha
      have hd := hδG i.1.val i.2 (by have := i.1.isLt;omega)
      linarith)
  have htarget := eventually_blind_uniform (fun A => targetNode Q (G J A))
    (fun A => mul_pos (gamma_positive n) (hR J A le_rfl))
    (fun _ => physicalFullProjection (s:=s) (basePhysicalProjection (E:=E) J n D))
    (fun _ => physicalFullProjection_norm_le _ (basePhysicalProjection_norm_le J n D))
    (fun A => r J A) (fun A => 3*(G J A).width/16) δ hδ z (by
      intro A a ha
      change |(physicalCoordinates Q (G J A) z.fst.snd.snd).snd a|≤3*(G J A).width/16-δ
      have hb := ht A a ha
      have hd := hδG J A le_rfl
      linarith)
  filter_upwards [hmacro,hordinary,htarget] with y hym hyo hyt
  refine ⟨hym (),?_,hyt⟩
  intro k A hk a ha
  exact hyo (⟨k,hk⟩,A) a ha

end Bilevel.EndpointTransportResponse
