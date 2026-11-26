import NCConcave16991.MixedHaarFrameCompletionLaw
import NCConcave16991.MixedHaarFrameUpdateGeometry

/-! # The actual fixed-state inverse reveal has the static completion joint law -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

attribute [local irreducible] frameTail frameHead frameComplete frameCandidate
  prefixSpan tailIsometry tailOrthogonal Haar.orthogonalLinearIsometryEquiv

variable {k : ℕ}

def frameInverseStaticStep (s : FrameState k) (x : Space k) (Q : Haar.OrthogonalGroup k) : FrameState k :=
  frameUpdate s x (Haar.orthogonalLinearIsometryEquiv Q⁻¹ x)

theorem frameInverseJoint_measurable (s : FrameState k) (x : Space k) :
    Measurable (fun p : Space k × FrameTape k ↦
      (frameUpdate s x p.1,frameComplete (frameUpdate s x p.1) p.2)) := by
  have hn : Measurable (fun p : Space k × FrameTape k ↦ frameUpdate s x p.1) :=
    frameUpdate_measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
  exact hn.prodMk (frameComplete_measurable.comp (hn.prodMk measurable_snd))

theorem frameInverseStaticStep_measurable (s : FrameState k) (x : Space k) :
    Measurable (frameInverseStaticStep s x) := by
  have ha : Measurable (fun Q : Haar.OrthogonalGroup k ↦ Haar.orthogonalLinearIsometryEquiv Q⁻¹ x) :=
    (Haar.continuous_orthogonalLinearIsometryEquiv_apply x).measurable.comp measurable_inv
  unfold frameInverseStaticStep
  exact frameUpdate_measurable.comp (measurable_const.prodMk (measurable_const.prodMk ha))

theorem frameUpdate_recover_updated_ae (s : FrameState k) (x : Space k) :
    ∀ᵐ p : Space k × FrameTape k ∂(stdGaussian (Space k)).prod (frameTapeLaw k),
      frameInverseStaticStep s x (frameComplete (frameUpdate s x p.1) p.2) = frameUpdate s x p.1 := by
  by_cases hr : s.1.val < k
  · by_cases hq : frameTail s.1 s.2.2 x = 0
    · exact Filter.Eventually.of_forall (fun p ↦ by
        unfold frameInverseStaticStep
        rw [frameUpdate_eq_self_of_tail_zero s x _ hq,frameUpdate_eq_self_of_tail_zero s x _ hq])
    · have hn := frameTail_ne_zero_ae s.1 s.2.1 (firstTailVector s.1 hr) (firstTailVector_unit s.1 hr)
      have hp : MeasurePreserving (Prod.fst : Space k × FrameTape k → Space k)
          ((stdGaussian (Space k)).prod (frameTapeLaw k)) (stdGaussian (Space k)) := measurePreserving_fst
      filter_upwards [hp.quasiMeasurePreserving.ae hn] with p hh
      unfold frameInverseStaticStep
      rw [frameUpdate_inverse s x p.1 p.2 hr hq hh]
      exact frameUpdate_candidate_invariant s x p.1
  · exact Filter.Eventually.of_forall (fun p ↦ by
      unfold frameInverseStaticStep frameUpdate frameUpdateAt
      rw [dif_neg hr,dif_neg hr])

/-- Gaussian lazy inverse completion and the original static completion have the
same joint law, including the entire updated public frame. -/
theorem frameInverse_local_jointLaw (s : FrameState k) (x : Space k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p ↦ (frameUpdate s x p.1,frameComplete (frameUpdate s x p.1) p.2)) =
      (frameCompletionLaw s).map (fun Q ↦ (frameInverseStaticStep s x Q,Q)) := by
  let μ := (stdGaussian (Space k)).prod (frameTapeLaw k)
  let complete := fun p : Space k × FrameTape k ↦ frameComplete (frameUpdate s x p.1) p.2
  let observe := fun Q : Haar.OrthogonalGroup k ↦ (frameInverseStaticStep s x Q,Q)
  have ho : Measurable observe := (frameInverseStaticStep_measurable s x).prodMk measurable_id
  have hg := frameComplete_update_preserving s x
  have heq : (fun p : Space k × FrameTape k ↦ (frameUpdate s x p.1,complete p)) =ᵐ[μ]
      observe ∘ complete := by
    filter_upwards [frameUpdate_recover_updated_ae s x] with p hp
    exact Prod.ext hp.symm rfl
  rw [Measure.map_congr heq]
  have hm := Measure.map_map (μ := μ) ho hg.measurable
  rw [← hm,hg.map_eq]

/-- A request-free step keeps the actual old completion and its public frame. -/
theorem frameNone_local_jointLaw (s : FrameState k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p : Space k × FrameTape k ↦ (s,frameComplete s p.2)) =
      (frameCompletionLaw s).map (fun Q ↦ (s,Q)) := by
  have hg := (frameComplete_preserving s).comp
    (measurePreserving_snd : MeasurePreserving (Prod.snd : Space k × FrameTape k → FrameTape k)
      ((stdGaussian (Space k)).prod (frameTapeLaw k)) (frameTapeLaw k))
  have ho : Measurable (fun Q : Haar.OrthogonalGroup k ↦ (s,Q)) := measurable_const.prodMk measurable_id
  have hm := Measure.map_map (μ := (stdGaussian (Space k)).prod (frameTapeLaw k)) ho hg.measurable
  have he : (fun p : Space k × FrameTape k ↦ (s,frameComplete s p.2)) =
      (fun Q : Haar.OrthogonalGroup k ↦ (s,Q)) ∘ (frameComplete s ∘ Prod.snd) := rfl
  rw [he,← hm,hg.map_eq]

/-- The same identity with the actual all-rank source tape on both sides, ready
for the finite adaptive completion recursion. -/
theorem frameInverse_local_jointLaw_tape (s : FrameState k) (x : Space k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p ↦ (frameUpdate s x p.1,frameComplete (frameUpdate s x p.1) p.2)) =
      (frameTapeLaw k).map (fun z ↦
        (frameInverseStaticStep s x (frameComplete s z),frameComplete s z)) := by
  rw [frameInverse_local_jointLaw]
  have hc := frameComplete_preserving s
  have ho := (frameInverseStaticStep_measurable s x).prodMk measurable_id
  have hm := Measure.map_map (μ := frameTapeLaw k) ho hc.measurable
  rw [hc.map_eq] at hm
  simpa only [Function.comp_def,id_eq] using hm

theorem frameNone_local_jointLaw_tape (s : FrameState k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p : Space k × FrameTape k ↦ (s,frameComplete s p.2)) =
      (frameTapeLaw k).map (fun z ↦ (s,frameComplete s z)) := by
  rw [frameNone_local_jointLaw]
  have hc := frameComplete_preserving s
  have ho : Measurable (fun Q : Haar.OrthogonalGroup k ↦ (s,Q)) := measurable_const.prodMk measurable_id
  have hm := Measure.map_map (μ := frameTapeLaw k) ho hc.measurable
  rw [hc.map_eq] at hm
  simpa only [Function.comp_def,id_eq] using hm

end NCConcave16991.MixedHaar
