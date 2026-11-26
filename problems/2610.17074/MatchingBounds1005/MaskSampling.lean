import MatchingBounds1005.TensorOracle
import MatchingBounds1005.MaskNormEvent
import MatchingBounds1005.OracleMeasurability
import MatchingBounds1005.IsometricTransfer

/-! Jointly measurable actual rotated, masked, confined instance families. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.TensorGeometry

theorem polynomial_joint_continuous (d k : ℕ) :
    Continuous (fun z : Tensor d k × Vec d => polynomial z.1 z.2) := by
  simp only [polynomial_eq_inner, rankOne]
  apply continuous_fst.inner
  apply (productTensor_continuous d k).comp
  exact continuous_pi (fun _ => continuous_snd)

theorem scaledGaussianTensor_continuous (d k : ℕ) (δ : ℝ) :
    Continuous (scaledGaussianTensor d k δ) :=
  continuous_const.smul (tensorCoordinates d k).symm.continuous

def sampledMask {d : ℕ} (δ₃ δ₄ : ℝ) (z : MaskSeed d) : Vec d → ℝ :=
  mask (scaledGaussianTensor d 3 δ₃ z.1) (scaledGaussianTensor d 4 δ₄ z.2)

theorem sampledMask_joint_continuous (d : ℕ) (δ₃ δ₄ : ℝ) :
    Continuous (fun z : MaskSeed d × Vec d => sampledMask δ₃ δ₄ z.1 z.2) := by
  apply Continuous.add
  · exact continuous_const.mul ((polynomial_joint_continuous d 3).comp
      (((scaledGaussianTensor_continuous d 3 δ₃).comp continuous_fst.fst).prodMk continuous_snd))
  · exact continuous_const.mul ((polynomial_joint_continuous d 4).comp
      (((scaledGaussianTensor_continuous d 4 δ₄).comp continuous_fst.snd).prodMk continuous_snd))

def sampledConfined {Ω : Type*} {d : ℕ} (F : Ω → Vec d → ℝ)
    (δ₃ δ₄ R η : ℝ) (z : Ω × MaskSeed d) : Vec d → ℝ :=
  Confinement.objective (fun y => F z.1 y + sampledMask δ₃ δ₄ z.2 y) R η

theorem sampledConfined_continuous {Ω : Type*} [TopologicalSpace Ω] {d : ℕ}
    (F : Ω → Vec d → ℝ) (hF : Continuous F.uncurry) (δ₃ δ₄ R η : ℝ) :
    Continuous (fun z : (Ω × MaskSeed d) × Vec d => sampledConfined F δ₃ δ₄ R η z.1 z.2) := by
  have hyr : Continuous (fun z : (Ω × MaskSeed d) × Vec d => radial R z.2) :=
    (radial_contDiff R ∞).continuous.comp continuous_snd
  exact ((hF.comp (continuous_fst.fst.prodMk hyr)).add
    ((sampledMask_joint_continuous d δ₃ δ₄).comp (continuous_fst.snd.prodMk hyr))).add
      (continuous_const.mul (continuous_snd.norm.pow 2))

theorem sampledConfined_oracle_measurable {Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] {d : ℕ}
    (F : Ω → Vec d → ℝ) (hF : Continuous F.uncurry) (δ₃ δ₄ R η : ℝ) :
    Measurable (fun z : (Ω × MaskSeed d) × Vec d =>
      Model.oracle (sampledConfined F δ₃ δ₄ R η z.1) z.2) :=
  Model.oracle_measurable_of_continuous (sampledConfined_continuous F hF δ₃ δ₄ R η)

def sampledGood {Ω : Type*} (d : ℕ) : Set (Ω × MaskSeed d) :=
  Prod.snd ⁻¹' MaskNormGood d

theorem sampledGood_measurable {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) :
    MeasurableSet (sampledGood (Ω := Ω) d) :=
  (maskNormGood_measurable d).preimage measurable_snd

theorem sampledGood_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) :
    1 - 4 * Real.exp (-4 * d) ≤ (μ.prod (maskLaw d)).real (sampledGood (Ω := Ω) d) := by
  have he : sampledGood (Ω := Ω) d = Set.univ ×ˢ MaskNormGood d := by ext z; simp [sampledGood]
  rw [he]
  change _ ≤ ((μ.prod (maskLaw d)) (Set.univ ×ˢ MaskNormGood d)).toReal
  rw [Measure.prod_prod, measure_univ, one_mul]
  exact maskNormGood_probability d

theorem sampledGood_positive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (hd : 1 ≤ d) :
    0 < (μ.prod (maskLaw d)).real (sampledGood (Ω := Ω) d) := by
  have h := sampledGood_probability μ d
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hexp : (5 : ℝ) ≤ Real.exp (4 * d) := by
    have hh := Real.add_one_le_exp (4 * (d : ℝ))
    linarith
  have hp : 0 < Real.exp (4 * (d : ℝ)) := Real.exp_pos _
  have hsmall : Real.exp (-4 * d) ≤ 1 / 5 := by
    rw [show -4 * (d : ℝ) = -(4 * d) by ring, Real.exp_neg]
    rw [← one_div]
    exact (div_le_iff₀ hp).mpr (by linarith)
  linarith

end MatchingBounds1005.TensorGeometry
