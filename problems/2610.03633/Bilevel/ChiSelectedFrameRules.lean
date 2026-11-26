import Bilevel.ChiSelectedFrameChannel
import Bilevel.SourceFrameActions

/-! The source execution compiled at one selected hierarchy frame. Its
immutable context contains the other columns and draw stream; the selected
frame is accessed only through the new-column argument of finish. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive EuclideanGaussian TransportControllerMachine

abbrev FrameMemory (counts : ℕ → ℕ) (J D : ℕ) (S : Type u) [MeasurableSpace S] :=
  Memory.of ((FiniteColumns counts J (Space D) × (ℕ → Bool)) × (S × Store counts J (Space D)))

variable {S : Type u} {Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]

def frameRequest (counts : ℕ → ℕ) (J D : ℕ) (i : FrameIndex counts J)
    (A : Program S Q O Y) (t : ℕ) (h : FrameMemory counts J D S) : Bool :=
  decide (A.halt h.2.1=false ∧ h.1.2 t=true ∧ requested counts J h.2.2.1 i)

theorem frameRequest_measurable (counts : ℕ → ℕ) (J D : ℕ) (i : FrameIndex counts J)
    (A : Program S Q O Y) (t : ℕ) : Measurable (frameRequest counts J D i A t) := by
  have hn : Measurable (fun p : Bool × (Bool × ℕ) =>
      decide (p.1=false ∧ p.2.1=true ∧ requested counts J p.2.2 i)) := measurable_of_countable _
  have ha : Measurable (fun h : FrameMemory counts J D S => (A.halt h.2.1,(h.1.2 t,h.2.2.1))) :=
    (A.halt_measurable.comp (measurable_fst.comp measurable_snd)).prodMk
    (((measurable_pi_apply t).comp (measurable_snd.comp measurable_fst)).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  exact hn.comp ha

def frameFinish (counts : ℕ → ℕ) (J D : ℕ) (i : FrameIndex counts J)
    (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (t : ℕ) (p : FrameMemory counts J D S × Space D) : FrameMemory counts J D S :=
  if A.halt p.1.2.1 then p.1 else
    let answer := partialResponse counts J i evaluate p.1.1.1 (A.query p.1.2.1,p.1.2.2) (p.1.1.2 t) p.2
    (p.1.1,(A.update (p.1.2.1,answer.1),answer.2))

theorem frameFinish_measurable (counts : ℕ → ℕ) (J D : ℕ) (i : FrameIndex counts J)
    (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2)) (t : ℕ) :
    Measurable (frameFinish counts J D i A evaluate t) := by
  let T := FrameMemory counts J D S × Space D
  have hc : Measurable (fun p : T => p.1.1) := measurable_fst.comp measurable_fst
  have hs : Measurable (fun p : T => p.1.2.1) := measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hd : Measurable (fun p : T => p.1.2.2) := measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hb : Measurable (fun p : T => p.1.1.2 t) :=
    (measurable_pi_apply t).comp (measurable_snd.comp hc)
  have ha : Measurable (fun p : T => partialResponse counts J i evaluate p.1.1.1
      (A.query p.1.2.1,p.1.2.2) (p.1.1.2 t) p.2) :=
    (partialResponse_measurable counts J i evaluate he).comp
      (((measurable_fst.comp hc).prodMk (((A.query_measurable.comp hs).prodMk hd).prodMk hb)).prodMk measurable_snd)
  have hh : MeasurableSet {p : T | A.halt p.1.2.1=true} :=
    (A.halt_measurable.comp hs) (measurableSet_singleton true)
  exact measurable_fst.ite hh (hc.prodMk
    ((A.update_measurable.comp (hs.prodMk (measurable_fst.comp ha))).prodMk (measurable_snd.comp ha)))

def frameRules (counts : ℕ → ℕ) (J D : ℕ) (i : FrameIndex counts J)
    (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (first second : Q × Store counts J (Space D) → Space D)
    (hf : Measurable first) (hs : Measurable second)
    (output : Y → Space D) (ho : Measurable output) :
    SourceFrameActions.Rules (FrameMemory counts J D S) D (chainSize i+1) where
  first _ h := first (A.query h.2.1,h.2.2)
  first_measurable _ := hf.comp
    ((A.query_measurable.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  second _ h := second (A.query h.2.1,h.2.2)
  second_measurable _ := hs.comp
    ((A.query_measurable.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  request := frameRequest counts J D i A
  request_measurable := frameRequest_measurable counts J D i A
  column _ h := columnIndex counts J h.2.2.1 i
  column_measurable _ := (measurable_of_countable (fun q => columnIndex counts J q i)).comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd))
  finish := frameFinish counts J D i A evaluate
  finish_measurable := frameFinish_measurable counts J D i A evaluate he
  output h := output (A.output h.2.1)
  output_measurable := ho.comp (A.output_measurable.comp (measurable_fst.comp measurable_snd))

end Bilevel.ChiHierarchyExecution
