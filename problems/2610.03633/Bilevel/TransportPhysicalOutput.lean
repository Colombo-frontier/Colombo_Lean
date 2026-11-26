import Bilevel.TransportPhysicalQuery
import Bilevel.ChiHierarchyIndex

/-! A frame-specific arbitrary terminal output. Macro and ordinary
ancestors observe their corresponding outer block; the deepest auxiliary
frame has zero output because its true frame belongs to the network. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiCarrier PrimitiveGeometry PartialLegendre EndpointTransportResponse TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 500000

def physicalFrameOutput {J D : ℕ} {counts : ℕ → ℕ} (i : FrameIndex counts J)
    (x : PhysicalOutput J D) : Block D :=
  match i with
  | Sum.inl _ => x.fst.fst
  | Sum.inr node => block J node.1.val x.fst.snd

theorem physicalFrameOutput_measurable {J D : ℕ} {counts : ℕ → ℕ}
    [MeasurableSpace (PhysicalOutput J D)] [BorelSpace (PhysicalOutput J D)]
    (i : FrameIndex counts J) : Measurable (physicalFrameOutput (D:=D) i) := by
  rcases i with _|node
  · exact physicalAuxiliaryOutput_measurable
  · let F : PhysicalOutput J D →L[ℝ] Joint (Block D) (Blocks J (Block D)) := jointFstLinear
    let G : Joint (Block D) (Blocks J (Block D)) →L[ℝ] Blocks J (Block D) := jointSndLinear
    have h := (block J node.1.val).continuous.comp ((G.comp F).continuous)
    exact h.measurable

theorem physicalFrameOutput_macro {J D : ℕ} {counts : ℕ → ℕ} (x : PhysicalOutput J D) :
    physicalFrameOutput (counts:=counts) (Sum.inl ()) x=x.fst.fst := rfl

theorem physicalFrameOutput_node {J D : ℕ} {counts : ℕ → ℕ} (i : ChiHierarchyIndex.Node counts J)
    (x : PhysicalOutput J D) : physicalFrameOutput (Sum.inr i) x=block J i.1.val x.fst.snd := rfl

variable {C S Q O : Type*} [MeasurableSpace C] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] {J D T : ℕ}
  [MeasurableSpace (PhysicalOutput J D)] [BorelSpace (PhysicalOutput J D)]

def physicalObserverOutput (counts : ℕ → ℕ)
    (P : BorelAdaptive.Program S Q O (PhysicalOutput J D))
    (i : Fin (Fintype.card (FrameIndex counts J)))
    (st : CommonState C S (Fintype.card (FrameIndex counts J)) T D) : Block D :=
  physicalFrameOutput ((enumerate counts J).symm i) (P.output st.2.1)

theorem physicalObserverOutput_measurable (counts : ℕ → ℕ)
    (P : BorelAdaptive.Program S Q O (PhysicalOutput J D))
    (i : Fin (Fintype.card (FrameIndex counts J))) :
    Measurable (physicalObserverOutput (C:=C) (T:=T) counts P i) := by
  have hs : Measurable (fun st : CommonState C S (Fintype.card (FrameIndex counts J)) T D => st.2.1) :=
    measurable_fst.comp measurable_snd
  have h := (physicalFrameOutput_measurable ((enumerate counts J).symm i)).comp
    (P.output_measurable.comp hs)
  exact h

end Bilevel.TransportHierarchy
