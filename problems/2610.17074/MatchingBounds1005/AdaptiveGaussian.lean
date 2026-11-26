import MatchingBounds1005.GaussianVector
import RandomizedFO2003.MeasurableSpanProjection
import Mathlib.Probability.Independence.Basic

/-!
# Gaussian residual resampling

These identities concern actual pushforward measures. First a fixed
orthogonal split is proved from characteristic functions. The parameterized
version retains the history as an explicit variable independent of the fresh
Gaussian seed. It does not postulate a posterior for an arbitrary history.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.AdaptiveGaussian
open GaussianVector

def projection {d : ℕ} (K : Submodule ℝ (Vec d)) : Vec d →L[ℝ] Vec d :=
  K.subtypeL.comp K.orthogonalProjection

theorem projection_inner {d : ℕ} (K : Submodule ℝ (Vec d)) (x y : Vec d) :
    ⟪projection K x, y⟫_ℝ = ⟪x, projection K y⟫_ℝ :=
  K.inner_orthogonalProjection_left_eq_right x y

def resample {d : ℕ} (K : Submodule ℝ (Vec d)) (z : Vec d × Vec d) : Vec d :=
  projection K z.1 + projection Kᗮ z.2

theorem resample_continuous {d : ℕ} (K : Submodule ℝ (Vec d)) :
    Continuous (resample K) :=
  ((projection K).continuous.comp continuous_fst).add
    ((projection Kᗮ).continuous.comp continuous_snd)

@[simp] theorem projection_resample {d : ℕ} (K : Submodule ℝ (Vec d))
    (z : Vec d × Vec d) : projection K (resample K z) = projection K z.1 := by
  simp [resample, projection]

@[simp] theorem orthogonal_projection_resample {d : ℕ}
    (K : Submodule ℝ (Vec d)) (z : Vec d × Vec d) :
    projection Kᗮ (resample K z) = projection Kᗮ z.2 := by
  simp [resample, projection]

/-- Replacing the unobserved orthogonal component by an independent fresh
Gaussian leaves the complete vector Gaussian. -/
theorem standardGaussian_resample {d : ℕ} (K : Submodule ℝ (Vec d)) :
    ((standardGaussian d).prod (standardGaussian d)).map (resample K) =
      standardGaussian d := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,
    integral_map (resample_continuous K).measurable.aemeasurable
      ((by fun_prop : Continuous (fun x : Vec d =>
        Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I))).measurable.aestronglyMeasurable)]
  have heq (z : Vec d × Vec d) :
      Complex.exp ((⟪resample K z, t⟫_ℝ : ℂ) * Complex.I) =
        Complex.exp ((⟪z.1, projection K t⟫_ℝ : ℂ) * Complex.I) *
          Complex.exp ((⟪z.2, projection Kᗮ t⟫_ℝ : ℂ) * Complex.I) := by
    simp only [resample, inner_add_left, projection_inner, Complex.ofReal_add,
      add_mul, Complex.exp_add]
  simp_rw [heq]
  rw [integral_prod_mul
    (fun x : Vec d => Complex.exp ((⟪x, projection K t⟫_ℝ : ℂ) * Complex.I))
    (fun x : Vec d => Complex.exp ((⟪x, projection Kᗮ t⟫_ℝ : ℂ) * Complex.I)),
    ← charFun_apply, ← charFun_apply,
    standardGaussian_charFun, standardGaussian_charFun, standardGaussian_charFun,
    ← Complex.exp_add]
  congr 1
  have hn : (‖t‖ : ℂ) ^ 2 = (‖projection K t‖ : ℂ) ^ 2 +
      (‖projection Kᗮ t‖ : ℂ) ^ 2 := by
    exact_mod_cast Submodule.norm_sq_eq_add_norm_sq_projection t K
  rw [hn]
  ring

/-- The observed component and complete vector have the same joint law
after independent residual resampling. -/
theorem standardGaussian_joint_resample {d : ℕ} (K : Submodule ℝ (Vec d)) :
    ((standardGaussian d).prod (standardGaussian d)).map
      (fun z => (projection K z.1, resample K z)) =
      (standardGaussian d).map (fun z => (projection K z, z)) := by
  conv_rhs => rw [← standardGaussian_resample K]
  rw [Measure.map_map (by fun_prop) (resample_continuous K).measurable]
  congr 1
  funext z
  simp only [Function.comp_apply, projection_resample]

/-- The two orthogonal components of an actual Gaussian are independent:
their joint law is the product of their actual marginal laws. -/
theorem standardGaussian_orthogonal_split {d : ℕ} (K : Submodule ℝ (Vec d)) :
    (standardGaussian d).map (fun z => (projection K z, projection Kᗮ z)) =
      ((standardGaussian d).map (projection K)).prod
        ((standardGaussian d).map (projection Kᗮ)) := by
  rw [Measure.map_prod_map (standardGaussian d) (standardGaussian d)
    (projection K).continuous.measurable (projection Kᗮ).continuous.measurable]
  conv_lhs => rw [← standardGaussian_resample K]
  rw [Measure.map_map (by fun_prop) (resample_continuous K).measurable]
  congr 1
  funext z
  simp only [Function.comp_apply, projection_resample, orthogonal_projection_resample,
    Prod.map_apply]
  rfl

theorem standardGaussian_projections_independent {d : ℕ} (K : Submodule ℝ (Vec d)) :
    IndepFun (projection K) (projection Kᗮ) (standardGaussian d) :=
  (indepFun_iff_map_prod_eq_prod_map_map
    (projection K).continuous.measurable.aemeasurable
    (projection Kᗮ).continuous.measurable.aemeasurable).mpr
      (standardGaussian_orthogonal_split K)

theorem projection_orthogonal_eq_sub {d : ℕ} (K : Submodule ℝ (Vec d)) (x : Vec d) :
    projection Kᗮ x = x - projection K x :=
  K.orthogonalProjection_orthogonal_val x

section Parameterized
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
attribute [local irreducible] projection

theorem measurable_resample_family (K : Ω → Submodule ℝ (Vec d))
    (hK : Measurable (fun p : Ω × Vec d => projection (K p.1) p.2)) :
    Measurable (fun p : Ω × (Vec d × Vec d) => resample (K p.1) p.2) := by
  have heq : (fun p : Ω × (Vec d × Vec d) => resample (K p.1) p.2) =
      (fun p => projection (K p.1) p.2.1 + (p.2.2 - projection (K p.1) p.2.2)) := by
    funext p
    exact congrArg (fun x => projection (K p.1) p.2.1 + x)
      (projection_orthogonal_eq_sub (K p.1) p.2.2)
  rw [heq]
  have h1 : Measurable (fun p : Ω × (Vec d × Vec d) => (p.1, p.2.1)) := by fun_prop
  have h2 : Measurable (fun p : Ω × (Vec d × Vec d) => (p.1, p.2.2)) := by fun_prop
  have hP : Measurable (fun p : Ω × (Vec d × Vec d) => projection (K p.1) p.2.1) :=
    hK.comp h1
  have hQ : Measurable (fun p : Ω × (Vec d × Vec d) => projection (K p.1) p.2.2) :=
    hK.comp h2
  exact hP.add ((measurable_snd.comp measurable_snd).sub hQ)

/-- A measurable history-dependent orthogonal resampling preserves the
product of an arbitrary history law and an independent standard Gaussian.
The independence is present in the input product measure, not assumed as a
conditional distribution of an arbitrary static parameter. -/
theorem resample_family_preserving (ν : Measure Ω) [SFinite ν]
    (K : Ω → Submodule ℝ (Vec d))
    (hK : Measurable (fun p : Ω × Vec d => projection (K p.1) p.2)) :
    MeasurePreserving
      (fun p : Ω × (Vec d × Vec d) => (p.1, resample (K p.1) p.2))
      (ν.prod ((standardGaussian d).prod (standardGaussian d)))
      (ν.prod (standardGaussian d)) :=
  (MeasurePreserving.id ν).skew_product (measurable_resample_family K hK)
    (ae_of_all ν (fun h => standardGaussian_resample (K h)))

/-- Actual joint-law equality retaining both the history and newly observed
projection. This is a generative residual update, without an RCD axiom. -/
theorem joint_resample_family (ν : Measure Ω) [SFinite ν]
    (K : Ω → Submodule ℝ (Vec d))
    (hK : Measurable (fun p : Ω × Vec d => projection (K p.1) p.2)) :
    (ν.prod ((standardGaussian d).prod (standardGaussian d))).map
      (fun p => (p.1, projection (K p.1) p.2.1, resample (K p.1) p.2)) =
      (ν.prod (standardGaussian d)).map
        (fun p => (p.1, projection (K p.1) p.2, p.2)) := by
  have hm : Measurable (fun p : Ω × Vec d => (p.1, projection (K p.1) p.2, p.2)) :=
    measurable_fst.prodMk (hK.prodMk measurable_snd)
  conv_rhs => rw [← (resample_family_preserving ν K hK).map_eq]
  rw [Measure.map_map hm (resample_family_preserving ν K hK).measurable]
  congr 1
  funext p
  simp only [Function.comp_apply, projection_resample]

/-- Finite measurable row spans satisfy the measurability premise, even
when their rank changes or the rows are linearly dependent. -/
theorem measurable_spanProjection {T : ℕ} (rows : Ω → Fin T → Vec d)
    (hrows : ∀ i, Measurable (fun h => rows h i)) :
    Measurable (fun p : Ω × Vec d =>
      projection (Submodule.span ℝ (Set.range (rows p.1))) p.2) := by
  unfold projection
  exact RandomizedFO2003.measurable_span_projection
    (fun p : Ω × Vec d => rows p.1)
    (fun i => (hrows i).comp measurable_fst) Prod.snd measurable_snd

theorem joint_resample_span (ν : Measure Ω) [SFinite ν] {T : ℕ}
    (rows : Ω → Fin T → Vec d) (hrows : ∀ i, Measurable (fun h => rows h i)) :
    (ν.prod ((standardGaussian d).prod (standardGaussian d))).map
      (fun p => (p.1, projection (Submodule.span ℝ (Set.range (rows p.1))) p.2.1,
        resample (Submodule.span ℝ (Set.range (rows p.1))) p.2)) =
      (ν.prod (standardGaussian d)).map
        (fun p => (p.1, projection (Submodule.span ℝ (Set.range (rows p.1))) p.2, p.2)) :=
  joint_resample_family ν (fun h => Submodule.span ℝ (Set.range (rows h)))
    (measurable_spanProjection rows hrows)

end Parameterized

end MatchingBounds1005.AdaptiveGaussian
