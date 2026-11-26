import MatchingBounds1005.GaussianProduct
import MatchingBounds1005.AnalyticSampling
import MatchingBounds1005.TensorChannelRows

/-! Exact Gaussian seed repacking: a joint latent vector is split into
independent cubic and quartic tensors, then paired with the fixed rotation.
The algorithm's private seed is preserved and remains independent. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations

namespace MatchingBounds1005.GaussianSeedRepacking
open GaussianVector GaussianProduct
variable {Rot Seed : Type*} [MeasurableSpace Rot] [MeasurableSpace Seed]

def repack (a b : ℕ) (z : (Rot × Seed) × Vec (a + b)) :
    (Rot × (Vec a × Vec b)) × Seed := ((z.1.1, splitEquiv a b z.2), z.1.2)

def unpack (a b : ℕ) (z : (Rot × (Vec a × Vec b)) × Seed) :
    (Rot × Seed) × Vec (a + b) := ((z.1.1, z.2), (splitEquiv a b).symm z.1.2)

theorem repack_measurable (a b : ℕ) : Measurable (repack (Rot := Rot) (Seed := Seed) a b) :=
  (measurable_fst.fst.prodMk ((splitEquiv a b).measurable.comp measurable_snd)).prodMk measurable_fst.snd

theorem unpack_measurable (a b : ℕ) : Measurable (unpack (Rot := Rot) (Seed := Seed) a b) :=
  (measurable_fst.fst.prodMk measurable_snd).prodMk
    ((splitEquiv a b).symm.measurable.comp measurable_fst.snd)

@[simp] theorem unpack_repack (a b : ℕ) (z : (Rot × Seed) × Vec (a + b)) :
    unpack a b (repack a b z) = z := by simp [repack, unpack]

@[simp] theorem repack_unpack (a b : ℕ) (z : (Rot × (Vec a × Vec b)) × Seed) :
    repack a b (unpack a b z) = z := by simp [repack, unpack]

def repackEquiv (a b : ℕ) : ((Rot × Seed) × Vec (a + b)) ≃ᵐ ((Rot × (Vec a × Vec b)) × Seed) where
  toFun := repack a b
  invFun := unpack a b
  left_inv := unpack_repack a b
  right_inv := repack_unpack a b
  measurable_toFun := repack_measurable a b
  measurable_invFun := unpack_measurable a b

theorem repack_preserving (a b : ℕ) (νR : Measure Rot) (νS : Measure Seed)
    [SFinite νR] [SFinite νS] :
    MeasurePreserving (repack a b)
      ((νR.prod νS).prod (standardGaussian (a + b)))
      ((νR.prod ((standardGaussian a).prod (standardGaussian b))).prod νS) := by
  let μ := (standardGaussian a).prod (standardGaussian b)
  have hsplit : MeasurePreserving (splitEquiv a b) (standardGaussian (a + b)) μ :=
    ⟨(splitEquiv a b).measurable, standardGaussian_split a b⟩
  have h₀ := (MeasurePreserving.id (νR.prod νS)).prod hsplit
  have h₁ := measurePreserving_prodAssoc νR νS μ
  have h₂ := (MeasurePreserving.id νR).prod (Measure.measurePreserving_swap (μ := νS) (ν := μ))
  have h₃ := (measurePreserving_prodAssoc νR μ νS).symm
  convert h₃.comp (h₂.comp (h₁.comp h₀)) using 1

theorem repack_map (a b : ℕ) (νR : Measure Rot) (νS : Measure Seed)
    [SFinite νR] [SFinite νS] :
    (((νR.prod νS).prod (standardGaussian (a + b))).map (repack a b)) =
      (νR.prod ((standardGaussian a).prod (standardGaussian b))).prod νS :=
  (repack_preserving a b νR νS).map_eq

end MatchingBounds1005.GaussianSeedRepacking

namespace MatchingBounds1005.AnalyticFamily
open GaussianVector GaussianSeedRepacking TensorChannelRows
variable {Seed : Type*} [MeasurableSpace Seed]

/-- The actual joint normalized tensor seed has exactly the already fixed
analytic sampled-family law, independently of the original algorithm seed. -/
theorem analytic_seed_repack_map (p : ℕ) (t : ℝ) (K : ℕ)
    (νS : Measure Seed) [SFinite νS] :
    (((haarLaw (Vec (dimension p t K))).prod νS).prod
      (standardGaussian (jointDim (dimension p t K)))).map
        (repack (cubicDim (dimension p t K)) (quarticDim (dimension p t K))) =
      (sampleLaw p t K).prod νS :=
  repack_map _ _ _ νS

end MatchingBounds1005.AnalyticFamily
