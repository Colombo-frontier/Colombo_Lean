import Bilevel.ChiHierarchyExecution

/-! The actual hierarchy reply, isolated at one selected frame. All other
frame data may be independent context. The selected frame contributes only
one requested next-column vector, and zero when no reveal is requested. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex

variable {E Q O : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [MeasurableSpace Q] [MeasurableSpace O]

open Classical in
def withoutFrame {counts : ℕ → ℕ} {J : ℕ} (i : FrameIndex counts J)
    (C : FiniteColumns counts J E) : FiniteColumns counts J E := Function.update C i 0

open Classical in
def channel (counts : ℕ → ℕ) (J q : ℕ) (b : Bool) (i : FrameIndex counts J)
    (C : FiniteColumns counts J E) (y : E) : Replies counts J E :=
  Function.update (revealReply counts J q b C) i y

omit [MeasurableSpace E] in
theorem channel_actual (counts : ℕ → ℕ) (J q : ℕ) (b : Bool) (i : FrameIndex counts J)
    (C U : FiniteColumns counts J E) (hC : ∀ j, j ≠ i → C j = U j) :
    channel counts J q b i C (revealReply counts J q b U i) = revealReply counts J q b U := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    exact Function.update_self _ _ _
  · rw [channel,Function.update_of_ne hj,revealReply_eq,revealReply_eq,hC j hj]

omit [MeasurableSpace E] in
theorem withoutFrame_other {counts : ℕ → ℕ} {J : ℕ} (i j : FrameIndex counts J)
    (C : FiniteColumns counts J E) (hj : j ≠ i) : withoutFrame i C j = C j :=
  Function.update_of_ne hj _ _

theorem channel_measurable (counts : ℕ → ℕ) (J : ℕ) (i : FrameIndex counts J) :
    Measurable (fun p : (FiniteColumns counts J E × (ℕ × Bool)) × E =>
      channel counts J p.1.2.1 p.1.2.2 i p.1.1 p.2) := by
  classical
  apply measurable_pi_lambda
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [channel,Function.update_self] using
      (measurable_snd : Measurable (fun p : (FiniteColumns counts J E × (ℕ × Bool)) × E => p.2))
  · simpa only [channel,Function.update_of_ne hj] using
      ((measurable_pi_apply j).comp (revealReply_joint_measurable counts J)).comp
        (measurable_fst : Measurable (fun p : (FiniteColumns counts J E × (ℕ × Bool)) × E => p.1))

def partialResponse (counts : ℕ → ℕ) (J : ℕ) (i : FrameIndex counts J)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (C : FiniteColumns counts J E) (p : Q × Store counts J E) (b : Bool) (y : E) : O × Store counts J E :=
  let next := ChiHierarchyIndex.update counts J p.2 b (channel counts J p.2.1 b i C y)
  (evaluate p.1 p.2 next b,next)

omit [MeasurableSpace E] [MeasurableSpace Q] [MeasurableSpace O] in
theorem partialResponse_actual (counts : ℕ → ℕ) (J : ℕ) (i : FrameIndex counts J)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (C U : FiniteColumns counts J E) (hC : ∀ j, j ≠ i → C j = U j)
    (p : Q × Store counts J E) (b : Bool) :
    partialResponse counts J i evaluate C p b (revealReply counts J p.2.1 b U i) =
      response counts J evaluate U p b := by
  simp only [partialResponse,channel_actual counts J p.2.1 b i C U hC,response]

theorem partialResponse_measurable (counts : ℕ → ℕ) (J : ℕ) (i : FrameIndex counts J)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J E × (Store counts J E × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Measurable (fun p : (FiniteColumns counts J E × ((Q × Store counts J E) × Bool)) × E =>
      partialResponse counts J i evaluate p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let T := (FiniteColumns counts J E × ((Q × Store counts J E) × Bool)) × E
  have hC : Measurable (fun p : T => p.1.1) := measurable_fst.comp measurable_fst
  have ho : Measurable (fun p : T => p.1.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hb : Measurable (fun p : T => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hq : Measurable (fun p : T => p.1.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hy : Measurable (fun p : T => channel counts J p.1.2.1.2.1 p.1.2.2 i p.1.1 p.2) :=
    (channel_measurable counts J i).comp ((hC.prodMk ((measurable_fst.comp ho).prodMk hb)).prodMk measurable_snd)
  have hn : Measurable (fun p : T => ChiHierarchyIndex.update counts J p.1.2.1.2 p.1.2.2
      (channel counts J p.1.2.1.2.1 p.1.2.2 i p.1.1 p.2)) :=
    (ChiHierarchyIndex.update_measurable counts J).comp (ho.prodMk (hb.prodMk hy))
  exact (he.comp (hq.prodMk (ho.prodMk (hn.prodMk hb)))).prodMk hn

end Bilevel.ChiHierarchyExecution
