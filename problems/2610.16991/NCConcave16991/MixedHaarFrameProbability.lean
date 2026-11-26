import NCConcave16991.MixedHaarFrameCandidate
import NCConcave16991.MixedHaarGaussianProjection
import NCConcave16991.MixedHaarCanonicalProbability

/-! # Actual Gaussian and Haar marginals for a fixed full-frame state -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 20000

attribute [local irreducible] frameTail prefixSpan tailIsometry tailOrthogonal frameComplete
  Haar.orthogonalLinearIsometryEquiv

variable {k : ℕ}

theorem frameTape_eval_preserving (r : Fin (k + 1)) :
    MeasurePreserving (fun z : FrameTape k ↦ z r) (frameTapeLaw k) (Haar.haarLaw (k - r.val)) :=
  measurePreserving_eval (fun r : Fin (k + 1) ↦ Haar.haarLaw (k - r.val)) r

def frameCompletionLaw (s : FrameState k) : Measure (Haar.OrthogonalGroup k) :=
  (Haar.haarLaw (k - s.1.val)).map (fun Q ↦ s.2.2 * tailOrthogonal s.1 Q * s.2.1⁻¹)

theorem frameComplete_preserving (s : FrameState k) :
    MeasurePreserving (frameComplete s) (frameTapeLaw k) (frameCompletionLaw s) := by
  have hm : Measurable (fun Q : Haar.OrthogonalGroup (k - s.1.val) ↦
      s.2.2 * tailOrthogonal s.1 Q * s.2.1⁻¹) :=
    ((continuous_const.fun_mul (tailOrthogonal_continuous s.1)).fun_mul continuous_const).measurable
  have hp : MeasurePreserving (fun Q : Haar.OrthogonalGroup (k - s.1.val) ↦
      s.2.2 * tailOrthogonal s.1 Q * s.2.1⁻¹) (Haar.haarLaw (k - s.1.val)) (frameCompletionLaw s) := ⟨hm,rfl⟩
  unfold frameComplete
  exact hp.comp (frameTape_eval_preserving s.1)

theorem frameTail_fixed_measurable (r : Fin (k + 1)) (F : Haar.OrthogonalGroup k) :
    Measurable (frameTail r F) := by
  simpa only [Function.comp_def, id_eq] using (frameTail_continuous r).measurable.comp
    (measurable_const.prodMk (measurable_id : Measurable (id : Space k → Space k)))

theorem frameTail_stdGaussian_law (r : Fin (k + 1)) (F : Haar.OrthogonalGroup k) :
    (stdGaussian (Space k)).map (frameTail r F) = stdGaussian (Space (k - r.val)) := by
  let V := (tailIsometry r).symm
  let P := (prefixSpan r)ᗮ.orthogonalProjectionOnto
  let R := Haar.orthogonalLinearIsometryEquiv F⁻¹
  have hV := V.continuous.measurable
  have hP := P.continuous.measurable
  have hR := R.continuous.measurable
  have hf : frameTail r F = V ∘ P ∘ R := by
    funext g
    rw [frameTail]
    rfl
  rw [hf,← Measure.map_map hV (hP.comp hR),← Measure.map_map hP hR,
    stdGaussian_map R,stdGaussian_map_orthogonalProjectionOnto,stdGaussian_map V]

theorem frameTail_stdGaussian_preserving (r : Fin (k + 1)) (F : Haar.OrthogonalGroup k) :
    MeasurePreserving (frameTail r F) (stdGaussian (Space k)) (stdGaussian (Space (k - r.val))) :=
  ⟨frameTail_fixed_measurable r F,frameTail_stdGaussian_law r F⟩

theorem frameTail_ne_zero_ae (r : Fin (k + 1)) (F : Haar.OrthogonalGroup k)
    (e : Space (k - r.val)) (he : ‖e‖ = 1) :
    ∀ᵐ g ∂stdGaussian (Space k), frameTail r F g ≠ 0 :=
  (frameTail_stdGaussian_preserving r F).quasiMeasurePreserving.ae (stdGaussian_ne_zero_ae e he)

theorem frameTail_normalized_law (r : Fin (k + 1)) (F : Haar.OrthogonalGroup k)
    (e : Space (k - r.val)) (he : ‖e‖ = 1) :
    (stdGaussian (Space k)).map (fun g ↦ normalize (frameTail r F g)) =
      (Haar.haarLaw (k - r.val)).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e) := by
  have h := Measure.map_map (μ := stdGaussian (Space k))
    (normalize_measurable (E := Space (k - r.val))) (frameTail_fixed_measurable r F)
  rw [frameTail_stdGaussian_law] at h
  calc
    _ = (stdGaussian (Space (k - r.val))).map normalize := by
      simpa only [Function.comp_def] using h.symm
    _ = _ := normalized_stdGaussian_eq_haarAction e he

end NCConcave16991.MixedHaar
