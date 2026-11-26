import MatchingBounds1005.SequentialPosterior

/-!
# Noncentered adaptive Gaussian posterior updates

The remaining prior mean in the unobserved complement is retained. This is
the signal term in the manuscript's static-tensor posterior.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.ShiftedPosterior
open GaussianVector AdaptiveGaussian GaussianFitter PosteriorGaussian SequentialPosterior

attribute [local irreducible] projection fitter rowResponse Submodule.span Submodule.orthogonalProjection Submodule.orthogonal

theorem projection_latent_any {d : ℕ} (V K : Submodule ℝ (Vec d)) (hVK : V ≤ K)
    (m : Vec d) (σ : ℝ) (z : Vec d) :
    projection K (m + σ • projection Vᗮ z) =
      projection K m + σ • projection Vᗮ (projection K z) := by
  rw [map_add, map_smul, projection_orthogonal_eq_sub V z,
    projection_orthogonal_eq_sub V (projection K z), map_sub,
    projection_large_small V K hVK, projection_small_large V K hVK]

theorem latent_resample_any {d : ℕ} (V K : Submodule ℝ (Vec d)) (hVK : V ≤ K)
    (m : Vec d) (σ : ℝ) (z w : Vec d) :
    m + σ • projection Vᗮ (resample K (z, w)) =
      projection K (m + σ • projection Vᗮ z) + projection Kᗮ m +
        σ • projection Kᗮ w := by
  have hQ : projection Vᗮ (projection Kᗮ w) = projection Kᗮ w :=
    projection_large_small Kᗮ Vᗮ (Submodule.orthogonal_le hVK) w
  rw [resample, map_add, smul_add, hQ, projection_latent_any V K hVK,
    projection_orthogonal_eq_sub K m]
  abel

theorem shifted_posterior_joint {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}
    (ν : Measure Ω) [SFinite ν] (V : Ω → Submodule ℝ (Vec d))
    (hV : Measurable (fun p : Ω × Vec d => projection (V p.1) p.2))
    (rows : Ω → Fin T → Vec d) (hrows : ∀ i, Measurable (fun h => rows h i))
    (hVK : ∀ h, V h ≤ Submodule.span ℝ (Set.range (rows h)))
    (m : Ω → Vec d) (hm : Measurable m) (σ : ℝ) :
    (ν.prod ((standardGaussian d).prod (standardGaussian d))).map
      (fun p => ((p.1, rowResponse (rows p.1) (m p.1 + σ • projection (V p.1)ᗮ p.2.1)),
        fitter (rows p.1)
          (rowResponse (rows p.1) (m p.1 + σ • projection (V p.1)ᗮ p.2.1)) +
          projection (Submodule.span ℝ (Set.range (rows p.1)))ᗮ (m p.1) +
          σ • projection (Submodule.span ℝ (Set.range (rows p.1)))ᗮ p.2.2)) =
      (ν.prod (standardGaussian d)).map
        (fun p => ((p.1, rowResponse (rows p.1) (m p.1 + σ • projection (V p.1)ᗮ p.2)),
          m p.1 + σ • projection (V p.1)ᗮ p.2)) := by
  let K := fun h => Submodule.span ℝ (Set.range (rows h))
  let state := fun h z => m h + σ • projection (V h)ᗮ z
  let obs := fun h z => (h, rowResponse (rows h) (state h z))
  have hs : Measurable (Function.uncurry state) :=
    (hm.comp measurable_fst).add (measurable_const.smul (measurable_complement V hV))
  have ho : Measurable (Function.uncurry obs) :=
    measurable_fst.prodMk ((measurable_rowResponse_family rows hrows).comp
      (measurable_fst.prodMk hs))
  have hop : ∀ h z, obs h (projection (K h) z) = obs h z := by
    intro h z
    have hp : projection (K h) (state h (projection (K h) z)) =
        projection (K h) (state h z) := by
      rw [show state h (projection (K h) z) = m h + σ • projection (V h)ᗮ (projection (K h) z) from rfl,
        show state h z = m h + σ • projection (V h)ᗮ z from rfl,
        projection_latent_any (V h) (K h) (hVK h),
        projection_latent_any (V h) (K h) (hVK h),
        projection_small_large (K h) (K h) le_rfl]
    change (h, rowResponse (rows h) (state h (projection (K h) z))) =
      (h, rowResponse (rows h) (state h z))
    apply congrArg (fun y : Fin T → ℝ => (h, y))
    calc
      rowResponse (rows h) (state h (projection (K h) z)) =
          rowResponse (rows h) (projection (K h) (state h (projection (K h) z))) :=
        (response_projection (rows h) _).symm
      _ = rowResponse (rows h) (projection (K h) (state h z)) := congrArg _ hp
      _ = rowResponse (rows h) (state h z) := response_projection (rows h) _
  have heq := observed_state_resample ν K (measurable_spanProjection rows hrows)
    obs state ho hs hop
  have hstate (h : Ω) (p : Vec d × Vec d) : state h (resample (K h) p) =
      fitter (rows h) (rowResponse (rows h) (state h p.1)) + projection (K h)ᗮ (m h) +
        σ • projection (K h)ᗮ p.2 := by
    rw [fitter_response_projection]
    exact latent_resample_any (V h) (K h) (hVK h) (m h) σ p.1 p.2
  simpa only [hstate, obs, state, K] using heq


set_option maxHeartbeats 200000 in
theorem shifted_step_factorization {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}
    (ν : Measure Ω) [SFinite ν] (V : Ω → Submodule ℝ (Vec d))
    (hV : Measurable (fun p : Ω × Vec d => projection (V p.1) p.2))
    (rows : Ω → Fin T → Vec d) (hrows : ∀ i, Measurable (fun h => rows h i))
    (hVK : ∀ h, V h ≤ Submodule.span ℝ (Set.range (rows h)))
    (m : Ω → Vec d) (hm : Measurable m) (σ : ℝ) :
    let state := fun h z => m h + σ • projection (V h)ᗮ z
    let observe := fun p : Ω × Vec d => (p.1, rowResponse (rows p.1) (state p.1 p.2))
    (ν.prod (standardGaussian d)).map (fun p => (observe p, state p.1 p.2)) =
      (((ν.prod (standardGaussian d)).map observe).prod (standardGaussian d)).map
        (fun p => (p.1, fitter (rows p.1.1) p.1.2 +
          projection (Submodule.span ℝ (Set.range (rows p.1.1)))ᗮ (m p.1.1) +
          σ • projection (Submodule.span ℝ (Set.range (rows p.1.1)))ᗮ p.2)) := by
  dsimp only
  let K := fun h => Submodule.span ℝ (Set.range (rows h))
  let state := fun h z => m h + σ • projection (V h)ᗮ z
  let observe := fun p : Ω × Vec d => (p.1, rowResponse (rows p.1) (state p.1 p.2))
  let g := fun p : (Ω × (Fin T → ℝ)) × Vec d =>
    (p.1, fitter (rows p.1.1) p.1.2 + projection (K p.1.1)ᗮ (m p.1.1) +
      σ • projection (K p.1.1)ᗮ p.2)
  have hs : Measurable (Function.uncurry state) :=
    (hm.comp measurable_fst).add (measurable_const.smul (measurable_complement V hV))
  have ho : Measurable observe :=
    measurable_fst.prodMk ((measurable_rowResponse_family rows hrows).comp
      (measurable_fst.prodMk hs))
  have hfit : Measurable (fun h : Ω × (Fin T → ℝ) => fitter (rows h.1) h.2) :=
    measurable_fitter (fun h : Ω × (Fin T → ℝ) => rows h.1) (fun h => h.2)
      (fun i => (hrows i).comp measurable_fst)
      (fun i => (measurable_pi_apply i).comp measurable_snd)
  have hK : Measurable (fun p : Ω × Vec d => projection (K p.1)ᗮ p.2) :=
    measurable_complement K (measurable_spanProjection rows hrows)
  have hmean : Measurable (fun h : Ω => projection (K h)ᗮ (m h)) :=
    let hh : Measurable (fun h : Ω => (h, m h)) := measurable_id.prodMk hm
    have hh2 := hK.comp hh
    hh2
  have hnew : Measurable (fun p : (Ω × (Fin T → ℝ)) × Vec d => projection (K p.1.1)ᗮ p.2) :=
    let hh : Measurable (fun p : (Ω × (Fin T → ℝ)) × Vec d => (p.1.1, p.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have hh2 := hK.comp hh
    hh2
  have hg : Measurable g := measurable_fst.prodMk
    (((hfit.comp measurable_fst).add (hmean.comp (measurable_fst.comp measurable_fst))).add
      (measurable_const.smul hnew))
  have hleft : Measurable (fun p : Ω × (Vec d × Vec d) =>
      g (observe (p.1, p.2.1), p.2.2)) := by
    apply hg.comp
    exact (ho.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have heq := (shifted_posterior_joint ν V hV rows hrows hVK m hm σ).symm
  change (ν.prod (standardGaussian d)).map (fun p => (observe p, state p.1 p.2)) = _
  calc
    (ν.prod (standardGaussian d)).map (fun p => (observe p, state p.1 p.2)) =
        (ν.prod ((standardGaussian d).prod (standardGaussian d))).map
          (fun p => g (observe (p.1, p.2.1), p.2.2)) := heq
    _ = ((ν.prod (standardGaussian d)).prod (standardGaussian d)).map
        (fun p => g (observe p.1, p.2)) := by
      rw [← Measure.prodAssoc_prod, Measure.map_map hleft MeasurableEquiv.prodAssoc.measurable]
      rfl
    _ = _ := (map_prod_right (ν.prod (standardGaussian d)) (standardGaussian d)
      observe ho g hg).symm

end MatchingBounds1005.ShiftedPosterior



