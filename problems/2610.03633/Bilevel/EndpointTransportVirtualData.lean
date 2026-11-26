import Bilevel.EndpointTransportVirtualFormula
import Bilevel.ChiVirtualContinuity

/-! Data topology for the explicit physical hierarchy. Source and target
arrays have independent prefix counts; no hidden rotations are inputs. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation
  EndpointTransportMatrix
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev EndpointColumnData {D : ℕ} (G : Geometry (Block D)) (n : ℕ) :=
  ∀ j I,Fin ((G j I).n+1) → Physical n D

abbrev PhysicalColumnData {D : ℕ} (G : Geometry (Block D)) (n : ℕ) :=
  ColumnData G × (EndpointColumnData G n × EndpointColumnData G n)

theorem prefixPhysicalCoordinatesAt_continuous {n D : ℕ} (N : Node (Block D)) (rs rt : ℕ) :
    Continuous (fun p : ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D =>
      prefixPhysicalCoordinatesAt N rs rt p.1.1 p.1.2 p.2) := by
  have hs := (readout_continuous (E:=Physical n D) N.n rs (gamma n*N.radius)).comp
    (continuous_fst.fst.prodMk continuous_snd : Continuous (fun p :
      ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D => (p.1.1,p.2)))
  have ht := (readout_continuous (E:=Physical n D) N.n rt (gamma n*N.radius)).comp
    (continuous_fst.snd.prodMk continuous_snd : Continuous (fun p :
      ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D => (p.1.2,p.2)))
  exact (packLinear (X:=Space N.n) (Y:=Space N.n)).continuous.comp ((hs.const_smul (2:ℝ)).prodMk ht)

theorem prefixPhysicalPayloadAt_continuous {n D : ℕ} (N : Node (Block D)) (rs rt : ℕ) :
    Continuous (fun p : ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D =>
      prefixPhysicalPayloadAt N rs rt p.1.1 p.1.2 p.2) :=
  (ChiSplitChain.payload_contDiff N.n 3 N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius).continuous.comp
    (prefixPhysicalCoordinatesAt_continuous N rs rt)

theorem prefixPhysicalRelease_continuous {n D : ℕ} (N : Node (Block D)) (rt : ℕ) :
    Continuous (fun p : (Fin (N.n+1) → Physical n D) × Physical n D =>
      prefixPhysicalRelease N rt p.1 p.2) := by
  apply (releaseGate_contDiff (k:=3)).continuous.comp
  exact (((EuclideanSpace.proj (𝕜:=ℝ) (Fin.last N.n)).continuous.comp
    (readout_continuous (E:=Physical n D) N.n rt (gamma n*N.radius))).div_const N.parentWidth)

theorem physicalOrdinaryData_continuous {m n D : ℕ} (G : Geometry (Block D)) (j : ℕ) (I : List ℕ) :
    Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      (p.1.1 j I,block m j p.2.fst)) := by
  have hc : Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D => p.1.1 j I) :=
    (continuous_apply I).comp ((continuous_apply j).comp continuous_fst.fst)
  have hx := (block (E:=Block D) m j).continuous.comp
    ((jointFstLinear (A:=Blocks m (Block D)) (B:=Physical n D)).continuous.comp
      (continuous_snd : Continuous (Prod.snd : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D → _)))
  exact hc.prodMk hx

theorem physicalEndpointData_continuous {m n D : ℕ} (G : Geometry (Block D)) (j : ℕ) (I : List ℕ) :
    Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      ((p.1.2.1 j I,p.1.2.2 j I),p.2.snd)) := by
  have hs : Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D => p.1.2.1 j I) :=
    (continuous_apply I).comp ((continuous_apply j).comp continuous_fst.snd.fst)
  have ht : Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D => p.1.2.2 j I) :=
    (continuous_apply I).comp ((continuous_apply j).comp continuous_fst.snd.snd)
  have hx := (jointSndLinear (A:=Blocks m (Block D)) (B:=Physical n D)).continuous.comp
    (continuous_snd : Continuous (Prod.snd : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D → _))
  exact (hs.prodMk ht).prodMk hx

theorem physicalPaddedData_continuous {m n D : ℕ} (G : Geometry (Block D)) :
    Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      (p.1.1,padded p.2.fst)) := by
  apply continuous_fst.fst.prodMk
  apply continuous_pi
  intro j
  exact (physicalOrdinaryData_continuous (m:=m) G j []).snd

end Bilevel.EndpointTransportResponse
