import NCConcave16991.MixedHaarFrameRangeGrowth

/-! # A total measurable mixed forward/inverse frame request interpreter -/

noncomputable section

namespace NCConcave16991.MixedHaar

open Set MeasureTheory

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prefixSpan tailIsometry tailOrthogonal householderOrthogonal frameHead frameTail
  Haar.orthogonalLinearIsometryEquiv

abbrev FrameRequest (k : ℕ) := Space k ⊕ Space k

def frameStep {k : ℕ} (s : FrameState k) (q : FrameRequest k) (g : Space k) : FrameState k × Space k :=
  q.elim (fun a ↦ (frameForwardUpdate s a g,frameForwardCandidate s a g))
    (fun b ↦ (frameUpdate s b g,frameCandidate s b g))

def frameRequestForward {k : ℕ} (q : FrameRequest k) : Space k := q.elim id (fun _ ↦ 0)
def frameRequestInverse {k : ℕ} (q : FrameRequest k) : Space k := q.elim (fun _ ↦ 0) id
def frameIsForward {k : ℕ} (q : FrameRequest k) : Bool := q.elim (fun _ ↦ true) (fun _ ↦ false)

theorem frameStep_measurable {k : ℕ} :
    Measurable (fun p : FrameState k × (FrameRequest k × Space k) ↦ frameStep p.1 p.2.1 p.2.2) := by
  classical
  have hq : Measurable (fun p : FrameState k × (FrameRequest k × Space k) ↦ p.2.1) := measurable_fst.comp measurable_snd
  have ha : Measurable (frameRequestForward (k := k)) := measurable_id.sumElim measurable_const
  have hb : Measurable (frameRequestInverse (k := k)) := measurable_const.sumElim measurable_id
  have hi : Measurable (frameIsForward (k := k)) := measurable_const.sumElim measurable_const
  have hf := (frameForwardUpdate_measurable.comp (measurable_fst.prodMk
    ((ha.comp hq).prodMk (measurable_snd.comp measurable_snd)))).prodMk
      (frameForwardCandidate_measurable.comp (measurable_fst.prodMk
        ((ha.comp hq).prodMk (measurable_snd.comp measurable_snd))))
  have hg := (frameUpdate_measurable.comp (measurable_fst.prodMk
    ((hb.comp hq).prodMk (measurable_snd.comp measurable_snd)))).prodMk
      (frameCandidate_measurable.comp (measurable_fst.prodMk
        ((hb.comp hq).prodMk (measurable_snd.comp measurable_snd))))
  have ht : Measurable (fun _ : FrameState k × (FrameRequest k × Space k) ↦ true) := measurable_const
  have hset : MeasurableSet {p : FrameState k × (FrameRequest k × Space k) | frameIsForward p.2.1 = true} :=
    measurableSet_eq_fun (hi.comp hq) ht
  have hh : Measurable (fun p : FrameState k × (FrameRequest k × Space k) ↦
      if frameIsForward p.2.1 = true then
        (frameForwardUpdate p.1 (frameRequestForward p.2.1) p.2.2,
          frameForwardCandidate p.1 (frameRequestForward p.2.1) p.2.2)
      else (frameUpdate p.1 (frameRequestInverse p.2.1) p.2.2,
          frameCandidate p.1 (frameRequestInverse p.2.1) p.2.2)) := Measurable.ite hset hf hg
  convert hh using 1
  funext p
  cases p.2.1 <;> rfl

def frameStepCompletion {k : ℕ} (s : FrameState k) (q : FrameRequest k) (p : Space k × FrameTape k) :
    (FrameState k × Space k) × Haar.OrthogonalGroup k :=
  (frameStep s q p.1,frameComplete (frameStep s q p.1).1 p.2)

attribute [local irreducible] frameStep frameStepCompletion frameComplete

theorem frameStepCompletion_measurable {k : ℕ} :
    Measurable (fun p : FrameState k × (FrameRequest k × (Space k × FrameTape k)) ↦ frameStepCompletion p.1 p.2.1 p.2.2) := by
  have hd : Measurable (fun p : FrameState k × (FrameRequest k × (Space k × FrameTape k)) ↦ frameStep p.1 p.2.1 p.2.2.1) :=
    frameStep_measurable.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  convert hd.prodMk (frameComplete_measurable.comp ((measurable_fst.comp hd).prodMk
    (measurable_snd.comp (measurable_snd.comp measurable_snd)))) using 1
  funext p
  unfold frameStepCompletion
  rfl

def frameStepBirth {k : ℕ} (q : FrameRequest k) (g : Space k) : Space k := q.elim id (fun _ ↦ g)

def FrameStepLegal {k : ℕ} (s : FrameState k) (q : FrameRequest k) (g : Space k) : Prop :=
  q.elim (fun _ ↦ True) (fun b ↦ s.1.val < k → frameTail s.1 s.2.2 b ≠ 0 → frameTail s.1 s.2.1 g ≠ 0)

theorem frameStep_domain_le {k : ℕ} (s : FrameState k) (q : FrameRequest k) (g : Space k)
    (hlegal : FrameStepLegal s q g) :
    frameDomain (frameStep s q g).1 ≤ frameDomain s ⊔ Submodule.span ℝ ({frameStepBirth q g} : Set (Space k)) := by
  cases q with
  | inl a =>
      simp only [frameStep,Sum.elim_inl,frameStepBirth]
      exact frameForwardUpdate_domain_le s a g
  | inr b =>
      simp only [frameStep,Sum.elim_inr,frameStepBirth]
      change frameDomain (frameUpdate s b g) ≤ frameDomain s ⊔ Submodule.span ℝ ({g} : Set (Space k))
      unfold frameUpdate frameUpdateAt
      split_ifs with hr hq
      · exact le_sup_left
      · exact frameUpdateActiveAt_domain_le_old_sup_gaussian s.1 hr s.2.1 s.2.2 b g hq (hlegal hr hq)
      · exact le_sup_left

theorem frameStep_reply_of_forward {k : ℕ} (s : FrameState k) (a g : Space k) :
    (frameStep s (.inl a) g).2 = frameForwardCandidate s a g := by simp only [frameStep,Sum.elim_inl]

theorem frameStep_reply_of_inverse {k : ℕ} (s : FrameState k) (b g : Space k) :
    (frameStep s (.inr b) g).2 = frameCandidate s b g := by simp only [frameStep,Sum.elim_inr]

end NCConcave16991.MixedHaar
