import NCBall.KernelMoments
import NCBall.InfiniteReplacement

/-! # Moment and orthogonality identities from independent resampling -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace NCBall

variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ν : Measure Ω} {μ : Measure Ξ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
  {R : Ω × Ξ → Ω}

omit [CompleteSpace E] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] in
theorem integral_refresh (hR : MeasurePreserving R (ν.prod μ) ν) {f : Ω → E}
    (hf : AEStronglyMeasurable f ν) :
    (∫ w, f w ∂ν) = ∫ wz, f (R wz) ∂ν.prod μ := by
  have hf' : AEStronglyMeasurable f ((ν.prod μ).map R) := hR.map_eq.symm ▸ hf
  have hi := integral_map hR.aemeasurable hf'
  rwa [hR.map_eq] at hi

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] in
theorem memLp_refresh_iff (hR : MeasurePreserving R (ν.prod μ) ν) {f : Ω → E}
    (hf : AEStronglyMeasurable f ν) :
    MemLp f 2 ν ↔ MemLp (fun wz => f (R wz)) 2 (ν.prod μ) := by
  have hf' : AEStronglyMeasurable f ((ν.prod μ).map R) := hR.map_eq.symm ▸ hf
  have hi := memLp_map_measure_iff (p := 2) hf' hR.aemeasurable
  rwa [hR.map_eq] at hi

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem resampled_oracle_memLp [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hR : MeasurePreserving R (ν.prod μ) ν) (g : Ω → E) (hg : Measurable g)
    (G : Ω → Ξ → E) (hG : Measurable (fun wz : Ω × Ξ => G wz.1 wz.2))
    (hr : ∀ w z, g (R (w, z)) = G w z)
    (hG2 : ∀ w, MemLp (G w) 2 μ) {V : ℝ}
    (hV : ∀ w, (∫ z, ‖G w z‖ ^ 2 ∂μ) ≤ V ^ 2) : MemLp g 2 ν := by
  apply (memLp_refresh_iff hR hg.aestronglyMeasurable).2
  simpa only [hr] using kernel_memLp_two (ν := ν) G hG hG2 hV

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem resampled_oracle_second_moment [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hR : MeasurePreserving R (ν.prod μ) ν) (g : Ω → E) (hg : Measurable g)
    (G : Ω → Ξ → E) (hG : Measurable (fun wz : Ω × Ξ => G wz.1 wz.2))
    (hr : ∀ w z, g (R (w, z)) = G w z)
    (hG2 : ∀ w, MemLp (G w) 2 μ) {V : ℝ}
    (hV : ∀ w, (∫ z, ‖G w z‖ ^ 2 ∂μ) ≤ V ^ 2) :
    (∫ w, ‖g w‖ ^ 2 ∂ν) ≤ V ^ 2 := by
  rw [integral_refresh hR (hg.norm.pow_const 2).aestronglyMeasurable]
  simpa only [hr] using kernel_second_moment (ν := ν) G hG hG2 hV

theorem resampled_noise_orthogonal (hR : MeasurePreserving R (ν.prod μ) ν)
    (e h : Ω → E) (he : MemLp e 2 ν) (hh : MemLp h 2 ν)
    (H : Ω → Ξ → E) (hH : ∀ w, Integrable (H w) μ)
    (hzero : ∀ w, (∫ z, H w z ∂μ) = 0)
    (hre : ∀ w z, e (R (w, z)) = H w z)
    (hrh : ∀ w z, h (R (w, z)) = h w) :
    (∫ w, ⟪h w, e w⟫_ℝ ∂ν) = 0 := by
  have hi := integrable_inner_of_memLp hh he
  have hip : Integrable (fun wz : Ω × Ξ => ⟪h wz.1, H wz.1 wz.2⟫_ℝ) (ν.prod μ) := by
    simpa only [Function.comp_apply, hre, hrh] using
      integrable_inner_of_memLp (hh.comp_measurePreserving hR) (he.comp_measurePreserving hR)
  rw [integral_refresh hR hi.aestronglyMeasurable]
  simp only [hre, hrh]
  rw [integral_prod _ hip]
  simp only [integral_inner (hH _), hzero, inner_zero_right, integral_zero]

theorem resampled_inner_unbiased (hR : MeasurePreserving R (ν.prod μ) ν)
    (g a h : Ω → E) (hg : MemLp g 2 ν) (ha : MemLp a 2 ν) (hh : MemLp h 2 ν)
    (G : Ω → Ξ → E) (hG : ∀ w, MemLp (G w) 2 μ)
    (hmean : ∀ w, (∫ z, G w z ∂μ) = a w)
    (hrg : ∀ w z, g (R (w, z)) = G w z)
    (hra : ∀ w z, a (R (w, z)) = a w)
    (hrh : ∀ w z, h (R (w, z)) = h w) :
    (∫ w, ⟪g w, h w⟫_ℝ ∂ν) = ∫ w, ⟪a w, h w⟫_ℝ ∂ν := by
  have hz := resampled_noise_orthogonal hR (fun w => g w - a w) h (hg.sub ha) hh
    (fun w z => G w z - a w)
    (fun w => ((hG w).sub (memLp_const _)).integrable (by norm_num))
    (fun w => centered_kernel_mean_zero (G w) (hG w) (a w) (hmean w))
    (fun w z => by dsimp only; rw [hrg, hra]) hrh
  simp_rw [inner_sub_right, ← real_inner_comm (h _)] at hz
  rw [integral_sub (integrable_inner_of_memLp hg hh) (integrable_inner_of_memLp ha hh)] at hz
  exact sub_eq_zero.mp hz

end NCBall
