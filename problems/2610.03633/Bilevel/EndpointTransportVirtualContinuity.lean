import Bilevel.EndpointTransportVirtualData

/-! Joint continuity of the explicit physical recursive carriers in all
disclosed arrays and the physical query, without Gram validity assumptions. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 250000

theorem virtualPhysicalCarrier_continuous {m n D : ℕ} (G : Geometry (Block D))
    (r rs : ℕ → List ℕ → ℕ) (d j : ℕ) (I : List ℕ) (t : ℕ) :
    Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      virtualPhysicalCarrier G r rs p.1.1 p.1.2.1 p.1.2.2 d j I t p.2) := by
  induction d generalizing j I t with
  | zero =>
    cases t with
    | zero =>
      exact ((prefixPhysicalPayloadAt_continuous (G j I) (rs j I) (r j I)).comp
        (physicalEndpointData_continuous (m:=m) (n:=n) G j I)).sub continuous_const
    | succ t => exact continuous_const
  | succ d ih =>
    cases t with
    | zero =>
      dsimp only [virtualPhysicalCarrier]
      split_ifs with hd
      · apply Continuous.add
        · have hh := (virtualH_continuous (G j I) (r j I)).comp
            (physicalOrdinaryData_continuous (m:=m) (n:=n) G j I)
          exact hh
        · apply continuous_finset_sum
          intro i _
          have hr := (virtualResidual_continuous (G j I) (r j I) i).comp
            (physicalOrdinaryData_continuous (m:=m) (n:=n) G j I)
          apply hr.mul
          apply Continuous.sub _ continuous_const
          have hd := (physicalEndpointData_continuous (m:=m) (n:=n) G (j+1) (child I i.val)).fst.snd.prodMk
            (physicalEndpointData_continuous (m:=m) (n:=n) G (j+1) (child I i.val)).snd
          have hh := (prefixPhysicalRelease_continuous (G (j+1) (child I i.val)) (r (j+1) (child I i.val))).comp hd
          exact hh
      · have hh := (virtualCarrier_continuous G r (d+1) j I 0).comp
          (physicalPaddedData_continuous (m:=m) (n:=n) G)
        exact hh
    | succ t =>
      dsimp only [virtualPhysicalCarrier]
      apply continuous_finset_sum
      intro i _
      have hh := (virtualSelector_continuous (G j I) (r j I) i).comp
        (physicalOrdinaryData_continuous (m:=m) (n:=n) G j I)
      exact hh.mul (ih (j+1) (child I i.val) t)

theorem virtualPhysicalSelect_continuous {m n D : ℕ} (G : Geometry (Block D))
    (r : ℕ → List ℕ → ℕ)
    (leaf : PhysicalColumnData G n → ℕ → List ℕ → Physical n D → ℝ)
    (hl : ∀ j I,Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      leaf p.1 j I p.2.snd)) (d j : ℕ) (I : List ℕ) :
    Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      virtualPhysicalSelect G r p.1.1 (leaf p.1) d j I p.2) := by
  induction d generalizing j I with
  | zero => exact hl j I
  | succ d ih =>
    dsimp only [virtualPhysicalSelect]
    apply continuous_finset_sum
    intro i _
    exact ((virtualSelector_continuous (G j I) (r j I) i).comp
      (physicalOrdinaryData_continuous (m:=m) (n:=n) G j I)).mul (ih (j+1) (child I i.val))

theorem virtualPhysicalFrontier_continuous {m n D : ℕ} (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (r rs : ℕ → List ℕ → ℕ) (d j : ℕ) (I : List ℕ) :
    Continuous (fun p : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      virtualPhysicalFrontier G P r rs p.1.1 p.1.2.1 p.1.2.2 d j I p.2) := by
  unfold virtualPhysicalFrontier
  refine virtualPhysicalSelect_continuous G r (fun data k A Y =>
    ChiSplitFine.frontier (G k A).n P.ℓ P.β
      (prefixPhysicalCoordinatesAt (G k A) (rs k A) (r k A) (data.2.1 k A) (data.2.2 k A) Y)) ?_ d j I
  intro k A
  have hd := (prefixPhysicalCoordinatesAt_continuous (G k A) (rs k A) (r k A)).comp
    (physicalEndpointData_continuous (m:=m) (n:=n) G k A)
  have hh := (ChiSplitFine.frontier_contDiff (G k A).n P.ℓ P.β).continuous.comp hd
  exact hh

theorem virtualPhysicalFinePiece_continuous {m n D : ℕ} (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (r rs : ℕ → List ℕ → ℕ) (p d j : ℕ) (I : List ℕ) :
    Continuous (fun z : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      virtualPhysicalFinePiece G P r rs z.1.1 z.1.2.1 z.1.2.2 p d j I z.2) := by
  unfold virtualPhysicalFinePiece
  refine virtualPhysicalSelect_continuous G r (fun data k A Y =>
    ChiSplitFine.pieces P (G k A).n p
      (prefixPhysicalCoordinatesAt (G k A) (rs k A) (r k A) (data.2.1 k A) (data.2.2 k A) Y)) ?_ d j I
  intro k A
  have hd := (prefixPhysicalCoordinatesAt_continuous (G k A) (rs k A) (r k A)).comp
    (physicalEndpointData_continuous (m:=m) (n:=n) G k A)
  have hh := (ChiSplitFine.pieces_contDiff P (G k A).n p).continuous.comp hd
  exact hh

theorem virtualPhysicalCoarseCarrier_continuous {m n D : ℕ} (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (r rs : ℕ → List ℕ → ℕ) (d j : ℕ) (I : List ℕ) (t : ℕ) :
    Continuous (fun z : PhysicalColumnData G n × HybridTangent (Blocks m (Block D)) n D =>
      virtualPhysicalCoarseCarrier G P r rs z.1.1 z.1.2.1 z.1.2.2 d j I t z.2) := by
  unfold virtualPhysicalCoarseCarrier
  apply (virtualPhysicalCarrier_continuous G r rs d j I t).sub
  split_ifs
  · exact virtualPhysicalFrontier_continuous G P r rs d j I
  · exact continuous_const

end Bilevel.EndpointTransportResponse
