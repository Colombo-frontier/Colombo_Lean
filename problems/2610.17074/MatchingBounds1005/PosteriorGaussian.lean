import MatchingBounds1005.AdaptiveGaussian
import MatchingBounds1005.GaussianFitter

/-!
# Actual Gaussian posterior updates as joint-law identities

The history law is explicitly independent of the fresh latent Gaussian seed.
Theorems transport its actual joint law, rather than assuming a regular
conditional Gaussian distribution for an arbitrary history. Raw finite row
observations and their measurable minimum-norm fitter are retained exactly.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.PosteriorGaussian
open GaussianVector AdaptiveGaussian GaussianFitter

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem fitter_response_projection {T : ℕ} (rows : Fin T → Vec d) (x : Vec d) :
    fitter rows (rowResponse rows x) = projection (Submodule.span ℝ (Set.range rows)) x :=
  fitter_rowResponse rows x

theorem response_projection {T : ℕ} (rows : Fin T → Vec d) (x : Vec d) :
    rowResponse rows (projection (Submodule.span ℝ (Set.range rows)) x) =
      rowResponse rows x := rowResponse_projection rows x

theorem projection_small_large (V K : Submodule ℝ (Vec d)) (hVK : V ≤ K) (x : Vec d) :
    projection V (projection K x) = projection V x :=
  congrArg Subtype.val (Submodule.orthogonalProjection_orthogonalProjection_of_le hVK x)

theorem projection_large_small (V K : Submodule ℝ (Vec d)) (hVK : V ≤ K) (x : Vec d) :
    projection K (projection V x) = projection V x :=
  Submodule.orthogonalProjection_eq_self_iff.mpr (hVK (V.orthogonalProjection x).property)

theorem projection_of_mem (K : Submodule ℝ (Vec d)) (x : Vec d) (hx : x ∈ K) :
    projection K x = x := Submodule.orthogonalProjection_eq_self_iff.mpr hx

attribute [local irreducible] projection

/-- Any measurable observation determined by the exposed projection keeps
its exact joint law with an arbitrary measurable latent state after fresh
orthogonal residual resampling. -/
theorem observed_state_resample (ν : Measure Ω) [SFinite ν]
    (K : Ω → Submodule ℝ (Vec d))
    (hK : Measurable (fun p : Ω × Vec d => projection (K p.1) p.2))
    {H S : Type*} [MeasurableSpace H] [MeasurableSpace S]
    (obs : Ω → Vec d → H) (state : Ω → Vec d → S)
    (ho : Measurable (Function.uncurry obs)) (hs : Measurable (Function.uncurry state))
    (hop : ∀ h z, obs h (projection (K h) z) = obs h z) :
    (ν.prod ((standardGaussian d).prod (standardGaussian d))).map
      (fun p => (obs p.1 p.2.1, state p.1 (resample (K p.1) p.2))) =
      (ν.prod (standardGaussian d)).map (fun p => (obs p.1 p.2, state p.1 p.2)) := by
  let f : Ω × (Vec d × Vec d) → H × S :=
    fun p => (obs p.1 p.2.1, state p.1 p.2.2)
  have hm1 : Measurable (fun p : Ω × (Vec d × Vec d) => (p.1, p.2.1)) := by fun_prop
  have hm2 : Measurable (fun p : Ω × (Vec d × Vec d) => (p.1, p.2.2)) := by fun_prop
  have hf : Measurable f := (ho.comp hm1).prodMk (hs.comp hm2)
  have hleft : Measurable (fun p : Ω × (Vec d × Vec d) =>
      (p.1, projection (K p.1) p.2.1, resample (K p.1) p.2)) :=
    measurable_fst.prodMk ((hK.comp hm1).prodMk (measurable_resample_family K hK))
  have hright : Measurable (fun p : Ω × Vec d =>
      (p.1, projection (K p.1) p.2, p.2)) :=
    measurable_fst.prodMk (hK.prodMk measurable_snd)
  have heq := congrArg (fun μ : Measure (Ω × (Vec d × Vec d)) => μ.map f)
    (joint_resample_family ν K hK)
  dsimp only at heq
  rw [Measure.map_map hf hleft, Measure.map_map hf hright] at heq
  simpa only [f, Function.comp_def, hop] using heq

theorem measurable_rowResponse_family {T : ℕ} (rows : Ω → Fin T → Vec d)
    (hrows : ∀ i, Measurable (fun h => rows h i)) :
    Measurable (fun p : Ω × Vec d => rowResponse (rows p.1) p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((hrows i).comp measurable_fst).inner measurable_snd

theorem affine_resample_fitter {T : ℕ} (rows : Fin T → Vec d)
    (m : Vec d) (σ : ℝ) (z w : Vec d) :
    fitter rows (rowResponse rows (m + σ • z)) +
        projection (Submodule.span ℝ (Set.range rows))ᗮ m +
        σ • projection (Submodule.span ℝ (Set.range rows))ᗮ w =
      m + σ • resample (Submodule.span ℝ (Set.range rows)) (z, w) := by
  rw [fitter_response_projection, map_add, map_smul,
    projection_orthogonal_eq_sub _ m, resample, smul_add]
  abel

/-- Actual affine Gaussian posterior identity for measurable finite rows.
The posterior center is the minimum-norm fit plus the prior mean in the
unobserved orthogonal complement. All ranks, including zero, are covered. -/
theorem affine_posterior_joint (ν : Measure Ω) [SFinite ν] {T : ℕ}
    (rows : Ω → Fin T → Vec d) (hrows : ∀ i, Measurable (fun h => rows h i))
    (m : Ω → Vec d) (hm : Measurable m) (σ : ℝ) :
    (ν.prod ((standardGaussian d).prod (standardGaussian d))).map
      (fun p => ((p.1, rowResponse (rows p.1) (m p.1 + σ • p.2.1)),
        fitter (rows p.1) (rowResponse (rows p.1) (m p.1 + σ • p.2.1)) +
          projection (Submodule.span ℝ (Set.range (rows p.1)))ᗮ (m p.1) +
          σ • projection (Submodule.span ℝ (Set.range (rows p.1)))ᗮ p.2.2)) =
      (ν.prod (standardGaussian d)).map
        (fun p => ((p.1, rowResponse (rows p.1) (m p.1 + σ • p.2)), m p.1 + σ • p.2)) := by
  let K := fun h => Submodule.span ℝ (Set.range (rows h))
  let obs := fun h z => (h, rowResponse (rows h) (m h + σ • z))
  let state := fun h z => m h + σ • z
  have hs : Measurable (Function.uncurry state) :=
    (hm.comp measurable_fst).add (measurable_const.smul measurable_snd)
  have ho : Measurable (Function.uncurry obs) :=
    measurable_fst.prodMk ((measurable_rowResponse_family rows hrows).comp
      (measurable_fst.prodMk hs))
  have hop : ∀ h z, obs h (projection (K h) z) = obs h z := by
    intro h z
    change (h, rowResponse (rows h) (m h + σ • projection (K h) z)) =
      (h, rowResponse (rows h) (m h + σ • z))
    apply congrArg (fun y : Fin T → ℝ => (h, y))
    funext i
    have hi := congrFun (response_projection (rows h) z) i
    change ⟪rows h i, projection (K h) z⟫_ℝ = ⟪rows h i, z⟫_ℝ at hi
    change ⟪rows h i, m h + σ • projection (K h) z⟫_ℝ =
      ⟪rows h i, m h + σ • z⟫_ℝ
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right, hi]
  have heq := observed_state_resample ν K (measurable_spanProjection rows hrows)
    obs state ho hs hop
  have hstate (h : Ω) (p : Vec d × Vec d) : m h + σ • resample (K h) p =
      fitter (rows h) (rowResponse (rows h) (m h + σ • p.1)) +
        projection (K h)ᗮ (m h) + σ • projection (K h)ᗮ p.2 :=
    (affine_resample_fitter (rows h) (m h) σ p.1 p.2).symm
  simpa only [obs, state, hstate, K] using heq

/-- The nested exposure condition makes projection of the current latent
state commute with projection of its fresh Gaussian seed. -/
theorem projection_latent (V K : Submodule ℝ (Vec d)) (hVK : V ≤ K)
    (m : Vec d) (hm : m ∈ V) (σ : ℝ) (z : Vec d) :
    projection K (m + σ • projection Vᗮ z) =
      m + σ • projection Vᗮ (projection K z) := by
  rw [map_add, map_smul, projection_of_mem K m (hVK hm),
    projection_orthogonal_eq_sub V z, projection_orthogonal_eq_sub V (projection K z),
    map_sub, projection_large_small V K hVK, projection_small_large V K hVK]

theorem latent_resample (V K : Submodule ℝ (Vec d)) (hVK : V ≤ K)
    (m : Vec d) (hm : m ∈ V) (σ : ℝ) (z w : Vec d) :
    m + σ • projection Vᗮ (resample K (z, w)) =
      projection K (m + σ • projection Vᗮ z) + σ • projection Kᗮ w := by
  have hQ : projection Vᗮ (projection Kᗮ w) = projection Kᗮ w :=
    projection_large_small Kᗮ Vᗮ (Submodule.orthogonal_le hVK) w
  rw [resample, map_add, smul_add, hQ, projection_latent V K hVK m hm]
  abel

/-- The induction step for an actual latent Gaussian representation.
The old exposed span `V` is contained in the new row span, and the old
fitted mean lies in `V`. After retaining the exact raw responses, the latent
vector has the joint law of its new minimum-norm fit plus a fresh independent
Gaussian projected onto the new unobserved complement. -/
theorem latent_posterior_joint (ν : Measure Ω) [SFinite ν] {T : ℕ}
    (V : Ω → Submodule ℝ (Vec d))
    (hV : Measurable (fun p : Ω × Vec d => projection (V p.1) p.2))
    (rows : Ω → Fin T → Vec d) (hrows : ∀ i, Measurable (fun h => rows h i))
    (hVK : ∀ h, V h ≤ Submodule.span ℝ (Set.range (rows h)))
    (m : Ω → Vec d) (hm : Measurable m) (hmV : ∀ h, m h ∈ V h) (σ : ℝ) :
    (ν.prod ((standardGaussian d).prod (standardGaussian d))).map
      (fun p => ((p.1, rowResponse (rows p.1) (m p.1 + σ • projection (V p.1)ᗮ p.2.1)),
        fitter (rows p.1)
          (rowResponse (rows p.1) (m p.1 + σ • projection (V p.1)ᗮ p.2.1)) +
          σ • projection (Submodule.span ℝ (Set.range (rows p.1)))ᗮ p.2.2)) =
      (ν.prod (standardGaussian d)).map
        (fun p => ((p.1, rowResponse (rows p.1) (m p.1 + σ • projection (V p.1)ᗮ p.2)),
          m p.1 + σ • projection (V p.1)ᗮ p.2)) := by
  let K := fun h => Submodule.span ℝ (Set.range (rows h))
  let state := fun h z => m h + σ • projection (V h)ᗮ z
  let obs := fun h z => (h, rowResponse (rows h) (state h z))
  have hVo : Measurable (fun p : Ω × Vec d => projection (V p.1)ᗮ p.2) := by
    have heq : (fun p : Ω × Vec d => projection (V p.1)ᗮ p.2) =
        fun p => p.2 - projection (V p.1) p.2 := by
      funext p
      exact projection_orthogonal_eq_sub (V p.1) p.2
    rw [heq]
    exact measurable_snd.sub hV
  have hs : Measurable (Function.uncurry state) :=
    (hm.comp measurable_fst).add (measurable_const.smul hVo)
  have ho : Measurable (Function.uncurry obs) :=
    measurable_fst.prodMk ((measurable_rowResponse_family rows hrows).comp
      (measurable_fst.prodMk hs))
  have hop : ∀ h z, obs h (projection (K h) z) = obs h z := by
    intro h z
    change (h, rowResponse (rows h) (state h (projection (K h) z))) =
      (h, rowResponse (rows h) (state h z))
    have hp : state h (projection (K h) z) = projection (K h) (state h z) :=
      (projection_latent (V h) (K h) (hVK h) (m h) (hmV h) σ z).symm
    rw [hp, response_projection]
  have heq := observed_state_resample ν K (measurable_spanProjection rows hrows)
    obs state ho hs hop
  have hstate (h : Ω) (p : Vec d × Vec d) : state h (resample (K h) p) =
      fitter (rows h) (rowResponse (rows h) (state h p.1)) + σ • projection (K h)ᗮ p.2 := by
    rw [fitter_response_projection]
    exact latent_resample (V h) (K h) (hVK h) (m h) (hmV h) σ p.1 p.2
  simpa only [hstate, obs, state, K] using heq

end MatchingBounds1005.PosteriorGaussian
