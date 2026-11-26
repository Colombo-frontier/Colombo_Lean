import Smoothness2601.HardQualitative
import Smoothness2601.SineSamplePotentials

/-! The two fixed losses used by the main lower oracle are jointly smooth,
not merely differentiable potentials for the verified gradient samples. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped ContDiff
namespace Smoothness2601.SineGeometry.Profiles
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (F : Profiles X) {b : Budgets} (S : F.Calibration b)

theorem samplePotential_contDiff (hB : ContDiff ℝ ∞ F.B) (q : ℝ) (coin : Bool) :
    ContDiff ℝ ∞ (F.samplePotential S q coin) := by
  have hfst : ContDiff ℝ ∞ (fun z : Joint X ℝ => z.fst) := (first (X := X)).contDiff
  have hsnd : ContDiff ℝ ∞ (fun z : Joint X ℝ => z.snd) := (second (X := X)).contDiff
  have hsin : ContDiff ℝ ∞ Real.sin := Real.contDiff_sin
  have hdiv : ContDiff ℝ ∞ (fun z : Joint X ℝ => z.snd/S.h) := hsnd.div_const S.h
  unfold samplePotential BernoulliOracle.sampleLoss inactivePotential informativePotential
  fun_prop

end Smoothness2601.SineGeometry.Profiles

namespace Smoothness2601.HardProfiles
open SineGeometry ExtensiveChain
variable {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)
  {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ W.threshold)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (U : Space n →ₗᵢ[ℝ] E)

theorem smooth_sample_losses (q : ℝ) (coin : Bool) :
    ContDiff ℝ ∞ (((profiles U).sourceScaled W.τ_pos hs).samplePotential
      (calibration W hp hβ hs hsδ U) q coin) := by
  apply Profiles.samplePotential_contDiff
  have hB : ContDiff ℝ ∞ (profiles U).B := contDiff_infty.mpr
    (fun k => wrappedB_contDiff radiusConstant U k)
  change ContDiff ℝ ∞ (fun x => (profiles U).B ((s/W.τ)⁻¹ • x))
  fun_prop

end Smoothness2601.HardProfiles
