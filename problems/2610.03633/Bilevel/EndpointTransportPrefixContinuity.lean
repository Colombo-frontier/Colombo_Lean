import Bilevel.EndpointTransportQuadraticGerm
import Bilevel.ChiVirtualUpperContinuity
import Bilevel.ParametricGradientMeasurable

/-! Joint continuity of the actual disclosed endpoint-prefix scalar.
Macro, physical payload, both receivers and public bowl are retained.
The evaluated formula is independent of the unrevealed transport rotations. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev QuadraticPrefixData {D : ℕ} (M : Node E) (G : Geometry (Block D)) (n : ℕ) :=
  (Fin (M.n+1) → E) ×
    ((∀ i : Fin (M.n+1),Fin ((G 0 [i.val]).n+1) → Physical n D) ×
     (∀ i : Fin (M.n+1),Fin ((G 0 [i.val]).n+1) → Physical n D))

theorem prefixPhysicalPayload_continuous {n D : ℕ} (N : Node (Block D)) (r : ℕ) :
    Continuous (fun p : ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D =>
      prefixPhysicalPayload N r p.1.1 p.1.2 p.2) :=
  (ChiSplitChain.payload_contDiff N.n 1 N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius).continuous.comp
    (physicalPrefixCoordinates_continuous N r)

theorem prefixQuadraticCore_rotations_irrelevant {n D : ℕ} (Q Q' : Rotations n D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ)
    (r : Fin (M.n+1) → ℕ) (data : QuadraticPrefixData M G n) :
    prefixQuadraticCore Q M ν G ρ R rM r data.1 data.2.1 data.2.2 =
      prefixQuadraticCore Q' M ν G ρ R rM r data.1 data.2.1 data.2.2 := rfl

theorem prefixQuadraticCore_continuous {n D : ℕ} (Q : Rotations n D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ)
    (r : Fin (M.n+1) → ℕ) :
    Continuous (fun p : QuadraticPrefixData M G n × Joint E (Physical n D) =>
      prefixQuadraticCore Q M ν G ρ R rM r p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let Z := QuadraticPrefixData M G n × Joint E (Physical n D)
  have hm : Continuous (fun p : Z => (p.1.1,p.2.fst)) :=
    continuous_fst.fst.prodMk ((jointFstLinear (A:=E) (B:=Physical n D)).continuous.comp continuous_snd)
  have hp : Continuous (fun p : Z => p.2.snd) :=
    (jointSndLinear (A:=E) (B:=Physical n D)).continuous.comp continuous_snd
  have hs (i : Fin (M.n+1)) : Continuous (fun p : Z => p.1.2.1 i) :=
    (continuous_apply i).comp continuous_fst.snd.fst
  have ht (i : Fin (M.n+1)) : Continuous (fun p : Z => p.1.2.2 i) :=
    (continuous_apply i).comp continuous_fst.snd.snd
  have hmacro : Continuous (fun p : Z => prefixPhysicalMacro Q M ν (fun i => G 0 [i.val]) rM r
      p.1.1 p.1.2.2 p.2) := by
    unfold prefixPhysicalMacro
    apply ((virtualMacroValue_continuous M ν rM).comp hm).add
    apply continuous_finset_sum
    intro i _
    exact ((virtualOuterResidual_continuous M rM i).comp hm).mul
      (((virtualRelease_continuous (targetNode Q (G 0 [i.val])) (r i)).comp
        ((ht i).prodMk hp)).sub continuous_const)
  have hsum : Continuous (fun p : Z => ∑ i : Fin (M.n+1),
      virtualOuterSelector M rM p.1.1 i p.2.fst*
        (prefixPhysicalPayload (G 0 [i.val]) (r i) (p.1.2.1 i) (p.1.2.2 i) p.2.snd-
          payload (G 0 [i.val]).n (G 0 [i.val]).ell (G 0 [i.val]).width (G 0 [i.val]).receiver
            (G 0 [i.val]).nu (G 0 [i.val]).force (G 0 [i.val]).parentWidth (G 0 [i.val]).tailRadius 0)) := by
    apply continuous_finset_sum
    intro i _
    exact ((virtualOuterSelector_continuous M rM i).comp hm).mul
      (((prefixPhysicalPayload_continuous (G 0 [i.val]) (r i)).comp
        (((hs i).prodMk (ht i)).prodMk hp)).sub continuous_const)
  exact (hmacro.add hsum).add
    ((full_bowl_contDiff (E:=Physical n D) (ρ/EndpointTransportMatrix.gamma n^2)
      (EndpointTransportMatrix.gamma n*R) 1).continuous.comp hp)

def statePrefixQuadraticCore {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ)
    (data : ℕ × QuadraticPrefixData M G n) : Joint E (Physical n D) → ℝ :=
  prefixQuadraticCore Q M ν G ρ R (rM data.1) (r data.1) data.2.1 data.2.2.1 data.2.2.2

theorem statePrefixQuadraticCore_continuous {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ) :
    Continuous (fun p : (ℕ × QuadraticPrefixData M G n) × Joint E (Physical n D) =>
      statePrefixQuadraticCore Q M ν G ρ R rM r p.1 p.2) := by
  have h : Continuous (fun p : ℕ × (QuadraticPrefixData M G n × Joint E (Physical n D)) =>
      prefixQuadraticCore Q M ν G ρ R (rM p.1) (r p.1) p.2.1.1 p.2.1.2.1 p.2.1.2.2 p.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun q => prefixQuadraticCore_continuous Q M ν G ρ R (rM q) (r q))
  have hm : Continuous (fun p : (ℕ × QuadraticPrefixData M G n) × Joint E (Physical n D) =>
      (p.1.1,(p.1.2,p.2))) :=
    continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)
  have hout := h.comp hm
  convert hout using 1

end Bilevel.EndpointTransportResponse
