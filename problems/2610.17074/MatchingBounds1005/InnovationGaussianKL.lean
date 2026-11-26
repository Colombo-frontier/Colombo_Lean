import MatchingBounds1005.LinearGaussianKL
import MatchingBounds1005.PosteriorGaussian
import MatchingBounds1005.InnovationEnergy

/-!
# Exact KL of a censored Gaussian innovation

The observation map is the actual new linear query composed with the
unobserved orthogonal projection. Its observable mean subspace is proved to
be the innovation space. Shared fitted answers cancel by an actual
translation of both measures; neither full rank nor a pseudoinverse is used.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.InnovationGaussianKL
open GaussianVector GaussianComparison LinearGaussianKL AdaptiveGaussian PosteriorGaussian

theorem projection_increment {d : ℕ} {V W : Submodule ℝ (Vec d)} (hVW : V ≤ W) (x : Vec d) :
    projection (W ⊓ Vᗮ) x = projection W x - projection V x :=
  InnovationEnergy.proj_increment hVW x

theorem projection_zero_iff {d : ℕ} (K : Submodule ℝ (Vec d)) (x : Vec d) :
    projection K x = 0 ↔ x ∈ Kᗮ := by
  constructor
  · intro h
    exact Submodule.orthogonalProjection_eq_zero_iff.mp (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (Submodule.orthogonalProjection_eq_zero_iff.mpr h)

theorem projection_mem {d : ℕ} (K : Submodule ℝ (Vec d)) (x : Vec d) : projection K x ∈ K :=
  (K.orthogonalProjection x).property

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasurableSpace F] [BorelSpace F]

/-- Common affine offsets preserve the already proved exact singular KL. -/
theorem affine_linearObservation_klDiv (B : Vec d →L[ℝ] F) (c : F) (m m' : Vec d)
    {σ : ℝ} (hσ : σ ≠ 0) :
    klDiv ((standardGaussian d).map (fun z => c + B (m + σ • z)))
      ((standardGaussian d).map (fun z => c + B (m' + σ • z))) =
      ENNReal.ofReal (‖(LinearMap.ker B)ᗮ.orthogonalProjection (m - m')‖ ^ 2 /
        (2 * σ ^ 2)) := by
  letI : IsProbabilityMeasure ((standardGaussian d).map (fun z => B (m + σ • z))) :=
    isProbabilityMeasure_map (show Measurable (fun z : Vec d => B (m + σ • z)) from by fun_prop).aemeasurable
  letI : IsProbabilityMeasure ((standardGaussian d).map (fun z => B (m' + σ • z))) :=
    isProbabilityMeasure_map (show Measurable (fun z : Vec d => B (m' + σ • z)) from by fun_prop).aemeasurable
  have ht : MeasurableEmbedding (fun x : F => c + x) :=
    (Homeomorph.addLeft c).toMeasurableEquiv.measurableEmbedding
  have hlaw (a : Vec d) : (standardGaussian d).map (fun z => c + B (a + σ • z)) =
      ((standardGaussian d).map (fun z => B (a + σ • z))).map (fun x => c + x) := by
    rw [Measure.map_map ht.measurable (by fun_prop)]
    rfl
  have hfinite : klDiv ((standardGaussian d).map (fun z => B (m + σ • z)))
      ((standardGaussian d).map (fun z => B (m' + σ • z))) ≠ ∞ := by
    rw [linearObservation_klDiv B m m' hσ]
    exact ENNReal.ofReal_ne_top
  rw [hlaw m, hlaw m', klDiv_map_embedding ht
    (klDiv_ne_top_iff.mp hfinite).1 (klDiv_ne_top_iff.mp hfinite).2,
    linearObservation_klDiv B m m' hσ]

def innovationMap (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d)) : Vec d →L[ℝ] F :=
  L.comp (projection Vᗮ)

def innovationSpace (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d)) : Submodule ℝ (Vec d) :=
  (V ⊔ (LinearMap.ker L)ᗮ) ⊓ Vᗮ

attribute [local irreducible] projection

theorem ker_innovationMap (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d)) :
    LinearMap.ker (innovationMap L V) = (innovationSpace L V)ᗮ := by
  let W : Submodule ℝ (Vec d) := V ⊔ (LinearMap.ker L)ᗮ
  have hVW : V ≤ W := le_sup_left
  have hWo : Wᗮ = Vᗮ ⊓ LinearMap.ker L := by
    change (V ⊔ (LinearMap.ker L)ᗮ)ᗮ = Vᗮ ⊓ LinearMap.ker L
    rw [← Submodule.inf_orthogonal, Submodule.orthogonal_orthogonal]
  apply Submodule.ext
  intro x
  have hp : projection W (projection Vᗮ x) = projection (innovationSpace L V) x := by
    rw [projection_orthogonal_eq_sub, map_sub, projection_large_small V W hVW,
      show innovationSpace L V = W ⊓ Vᗮ from rfl, projection_increment hVW]
  change L (projection Vᗮ x) = 0 ↔ x ∈ (innovationSpace L V)ᗮ
  calc
    L (projection Vᗮ x) = 0 ↔ projection Vᗮ x ∈ LinearMap.ker L := Iff.rfl
    _ ↔ projection Vᗮ x ∈ Wᗮ := by
      rw [hWo]
      constructor
      · intro h
        exact ⟨projection_mem Vᗮ x, h⟩
      · exact fun h => h.2
    _ ↔ projection W (projection Vᗮ x) = 0 := (projection_zero_iff W _).symm
    _ ↔ projection (innovationSpace L V) x = 0 := by rw [hp]
    _ ↔ x ∈ (innovationSpace L V)ᗮ := projection_zero_iff _ _

theorem orthogonal_ker_innovationMap (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d)) :
    (LinearMap.ker (innovationMap L V))ᗮ = innovationSpace L V := by
  rw [ker_innovationMap, Submodule.orthogonal_orthogonal]

/-- Exact single-channel innovation KL, including repeated and zero queries.
The mean in all old directions is retained verbatim in the shared fitter. -/
theorem innovation_klDiv (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (fitted s₀ s₁ : Vec d) {σ : ℝ} (hσ : σ ≠ 0) :
    klDiv ((standardGaussian d).map
      (fun z => L (fitted + projection Vᗮ (s₀ + σ • z))))
      ((standardGaussian d).map
        (fun z => L (fitted + projection Vᗮ (s₁ + σ • z)))) =
      ENNReal.ofReal (‖(innovationSpace L V).orthogonalProjection (s₀ - s₁)‖ ^ 2 /
        (2 * σ ^ 2)) := by
  have h := affine_linearObservation_klDiv (innovationMap L V) (L fitted) s₀ s₁ hσ
  have hp := Submodule.eq_orthogonalProjection_of_eq_submodule
    (orthogonal_ker_innovationMap L V) (s₀ - s₁)
  have hn := congrArg norm hp
  change ‖(LinearMap.ker (innovationMap L V))ᗮ.orthogonalProjection (s₀ - s₁)‖ =
    ‖(innovationSpace L V).orthogonalProjection (s₀ - s₁)‖ at hn
  rw [hn] at h
  simpa only [innovationMap, ContinuousLinearMap.comp_apply, map_add] using h

/-- Censoring exactly the hidden innovation gives the manuscript's positive
quadratic conditional KL cost. -/
theorem censored_innovation_klDiv (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (fitted visible hidden : Vec d) {σ : ℝ} (hσ : σ ≠ 0) :
    klDiv ((standardGaussian d).map
      (fun z => L (fitted + projection Vᗮ (visible + σ • z))))
      ((standardGaussian d).map
        (fun z => L (fitted + projection Vᗮ ((visible + hidden) + σ • z)))) =
      ENNReal.ofReal (‖(innovationSpace L V).orthogonalProjection hidden‖ ^ 2 /
        (2 * σ ^ 2)) := by
  rw [innovation_klDiv L V fitted visible (visible + hidden) hσ,
    show visible - (visible + hidden) = -hidden from by abel, map_neg, norm_neg]

/-- A query-independent finite conditional KL bound, sufficient for the
verified likelihood-integrability and adaptive chain-rule theorems. -/
theorem censored_innovation_klDiv_le (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (fitted visible hidden : Vec d) {σ : ℝ} (hσ : σ ≠ 0) :
    klDiv ((standardGaussian d).map
      (fun z => L (fitted + projection Vᗮ (visible + σ • z))))
      ((standardGaussian d).map
        (fun z => L (fitted + projection Vᗮ ((visible + hidden) + σ • z)))) ≤
      ENNReal.ofReal (‖hidden‖ ^ 2 / (2 * σ ^ 2)) := by
  rw [censored_innovation_klDiv L V fitted visible hidden hσ]
  apply ENNReal.ofReal_le_ofReal
  have hp : ‖(innovationSpace L V).orthogonalProjection hidden‖ ≤ ‖hidden‖ :=
    ((innovationSpace L V).orthogonalProjection.le_opNorm hidden).trans
      ((mul_le_mul_of_nonneg_right (innovationSpace L V).orthogonalProjection_norm_le
        (norm_nonneg hidden)).trans_eq (one_mul _))
  exact div_le_div_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp) (by positivity)

/-- The explicit minimum-norm update fits the newly generated raw answers
and retains the entire old fitted projection. This proves feasibility of
innovation-generated reference answers, including rank-deficient queries. -/
theorem reference_fitter_consistency {T : ℕ} (rows : Fin T → Vec d)
    (V : Submodule ℝ (Vec d)) (hV : V ≤ Submodule.span ℝ (Set.range rows))
    (m : Vec d) (hm : m ∈ V) (residual : Vec d) :
    let θ := m + projection Vᗮ residual
    let mnew := GaussianFitter.fitter rows (GaussianFitter.rowResponse rows θ)
    projection V mnew = m ∧ GaussianFitter.rowResponse rows mnew = GaussianFitter.rowResponse rows θ := by
  dsimp only
  constructor
  · rw [fitter_response_projection, projection_small_large V _ hV, map_add,
      projection_of_mem V m hm,
      (projection_zero_iff V _).mpr (projection_mem Vᗮ residual), add_zero]
  · exact GaussianFitter.fitter_exact rows _

/-- A fully exposed old measurement is replayed exactly by every reference
innovation realization, independent of the visible mean and noise seed. -/
theorem old_measurement_replay (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (hrow : (LinearMap.ker L)ᗮ ≤ V) (m residual : Vec d) :
    L (m + projection Vᗮ residual) = L m := by
  have hk : Vᗮ ≤ LinearMap.ker L := by
    simpa only [Submodule.orthogonal_orthogonal] using Submodule.orthogonal_le hrow
  have hz : L (projection Vᗮ residual) = 0 := hk (projection_mem Vᗮ residual)
  rw [map_add, hz, add_zero]

end MatchingBounds1005.InnovationGaussianKL
