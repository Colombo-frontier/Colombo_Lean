import NCConcave16991.MixedHaarFrameProbability
import NCConcave16991.MixedHaarFrameFactorization
import NCConcave16991.MixedHaarSphereFrameKernel

/-! # A Gaussian inverse reveal preserves the exact full-frame completion law -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000

attribute [local irreducible] frameTail frameHead prefixSpan tailIsometry tailOrthogonal
  sphereSelector householderOrthogonal Haar.orthogonalLinearIsometryEquiv

variable {k : ℕ}

theorem frameComplete_active_preserving (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x : Space k) (hq : frameTail r G x ≠ 0) :
    MeasurePreserving
      (fun p : Space k × FrameTape k ↦ frameComplete (frameUpdateActiveAt r hr F G x p.1) p.2)
      ((stdGaussian (Space k)).prod (frameTapeLaw k)) (frameCompletionLaw (r,F,G)) := by
  let e₀ := firstTailVector r hr
  let e := normalize (frameTail r G x)
  let sample := fun g : Space k ↦ normalize (frameTail r F g)
  have hs : Measurable sample := normalize_measurable.comp (frameTail_fixed_measurable r F)
  have hlaw : (stdGaussian (Space k)).map sample =
      (Haar.haarLaw (k - r.val)).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e₀) :=
    frameTail_normalized_law r F e₀ (firstTailVector_unit r hr)
  have hkernel := sphereFrameKernel_preserving (stdGaussian (Space k)) e₀ (firstTailVector_unit r hr)
    e sample hs hlaw (successorPointHom r hr) (successorPointHom_continuous r hr)
    (successorPointHom_surjective r hr)
  let physical := fun Q : Haar.OrthogonalGroup (k - r.val) ↦ G * tailOrthogonal r Q * F⁻¹
  have hp : MeasurePreserving physical (Haar.haarLaw (k - r.val)) (frameCompletionLaw (r,F,G)) := by
    refine ⟨?_,rfl⟩
    exact ((continuous_const.fun_mul (tailOrthogonal_continuous r)).fun_mul continuous_const).measurable
  have hsource := (MeasurePreserving.id (stdGaussian (Space k))).prod
    (frameTape_eval_preserving (nextRank r hr))
  have h := hp.comp (hkernel.comp hsource)
  convert h using 1
  funext p
  rw [frameComplete_active_factorization]
  simp only [Function.comp_def,physical,sphereFrameKernel,Prod.map,id_eq,sphereSelector,
    e₀,e,sample,successorPointHom]
  rfl

theorem frameComplete_update_preserving (s : FrameState k) (x : Space k) :
    MeasurePreserving
      (fun p : Space k × FrameTape k ↦ frameComplete (frameUpdate s x p.1) p.2)
      ((stdGaussian (Space k)).prod (frameTapeLaw k)) (frameCompletionLaw s) := by
  by_cases hr : s.1.val < k
  · by_cases hq : frameTail s.1 s.2.2 x = 0
    · have he : (fun p : Space k × FrameTape k ↦ frameComplete (frameUpdate s x p.1) p.2) =
          (frameComplete s) ∘ Prod.snd := by
        funext p
        simp only [frameUpdate,frameUpdateAt,dif_pos hr,if_pos hq,Function.comp_def]
      rw [he]
      exact (frameComplete_preserving s).comp measurePreserving_snd
    · have he : (fun p : Space k × FrameTape k ↦ frameComplete (frameUpdate s x p.1) p.2) =
          (fun p ↦ frameComplete (frameUpdateActiveAt s.1 hr s.2.1 s.2.2 x p.1) p.2) := by
        funext p
        simp only [frameUpdate,frameUpdateAt,dif_pos hr,if_neg hq]
      rw [he]
      exact frameComplete_active_preserving s.1 hr s.2.1 s.2.2 x hq
  · have he : (fun p : Space k × FrameTape k ↦ frameComplete (frameUpdate s x p.1) p.2) =
        (frameComplete s) ∘ Prod.snd := by
      funext p
      simp only [frameUpdate,frameUpdateAt,dif_neg hr,Function.comp_def]
    rw [he]
    exact (frameComplete_preserving s).comp measurePreserving_snd

end NCConcave16991.MixedHaar
