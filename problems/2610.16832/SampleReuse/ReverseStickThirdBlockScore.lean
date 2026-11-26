import SampleReuse.ReverseStickThirdEnergyBounds
import SampleReuse.ReverseStickThirdBlockEnergies

/-! Uniform third-score control for gates on orthogonal coordinate blocks. -/

open SecondOrder
open scoped BigOperators Classical
namespace SampleReuse
noncomputable section
variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem thirdTrilinear_comp_linear {f : F → ℝ} (hf : ContDiff ℝ 3 f)
    (L : E →L[ℝ] F) (x u v w : E) :
    thirdTrilinear (f ∘ L) x u v w = thirdTrilinear f (L x) (L u) (L v) (L w) := by
  have hh := congrArg (fun A => A ![u, v, w]) (L.iteratedFDeriv_comp_right hf x (le_refl 3))
  have he : (fun i => L (![u, v, w] i)) = ![L u, L v, L w] := by
    ext i
    fin_cases i <;> rfl
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    thirdTrilinear_eq_iterated, he] using hh

theorem blockGate_thirdTrilinear (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 3 (p i))
    (x u v w : HomogeneousBlocks ι E) (i : ι) :
    thirdTrilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x u v w =
      thirdTrilinear (p i) (x i) (u i) (v i) (w i) :=
  thirdTrilinear_comp_linear (hp i) (blockProj i) x u v w

/-- All constants are independent of the finite block index type. -/
theorem blockGate_thirdScore_abs_mean_le
    (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 3 (p i))
    (x u v w : HomogeneousBlocks ι E)
    (hp0 : ∀ i, 0 < p i (x i)) (hp1 : ∀ i, p i (x i) < 1)
    (ell₁ ell₂ ell₃ : ℝ) (hell₁ : 0 ≤ ell₁) (hell₂ : 0 ≤ ell₂) (hell₃ : 0 ≤ ell₃)
    (hF : ∀ i, ‖fderiv ℝ (p i) (x i)‖ ^ 2 ≤ ell₁ ^ 2 * p i (x i) * (1 - p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ^ 2 ≤
      ell₂ ^ 2 * p i (x i) * (1 - p i (x i)))
    (hthird : ∀ i, ‖iteratedFDeriv ℝ 3 (p i) (x i)‖ ≤ ell₃) :
    pmfMean (bernoulliProduct (fun i => p i (x i))
      (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun ω => |bernoulliThirdScore (fun i => p i (x i))
        (fun i => fderiv ℝ (fun y : HomogeneousBlocks ι E => p i (y i)) x u)
        (fun i => fderiv ℝ (fun y : HomogeneousBlocks ι E => p i (y i)) x v)
        (fun i => fderiv ℝ (fun y : HomogeneousBlocks ι E => p i (y i)) x w)
        (fun i => secondBilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x u v)
        (fun i => secondBilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x u w)
        (fun i => secondBilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x v w)
        (fun i => thirdTrilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x u v w) ω|) ≤
      (2 * ell₃ + 6 * ell₁ * ell₂ + 6 * ell₁ ^ 3) * ‖u‖ * ‖v‖ * ‖w‖ := by
  have hp2 (i : ι) : ContDiff ℝ 2 (p i) := (hp i).of_le (by decide)
  have hfirst (t : HomogeneousBlocks ι E) :
      bernoulliFisherEnergy (fun i => p i (x i))
        (fun i => fderiv ℝ (fun y : HomogeneousBlocks ι E => p i (y i)) x t) ≤
        (ell₁ * ‖t‖) ^ 2 := by
    simpa only [mul_pow] using blockGate_fisher_energy p hp2 x hp0 hp1 ell₁ hF t
  have hsecond (t z : HomogeneousBlocks ι E) :
      bernoulliFisherEnergy (fun i => p i (x i))
        (fun i => secondBilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x t z) ≤
        (ell₂ * ‖t‖ * ‖z‖) ^ 2 := by
    simpa only [mul_pow] using blockGate_second_fisher_energy p hp2 x t z hp0 hp1 ell₂ hH
  have hthirdsum :
      (∑ i, |thirdTrilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x u v w|) ≤
        ell₃ * ‖u‖ * ‖v‖ * ‖w‖ := by
    simpa only [blockGate_thirdTrilinear p hp, thirdTrilinear_eq_iterated] using
      blockGate_third_absolute_sum p x u v w hell₃ hthird
  have hh := bernoulliThirdScore_abs_mean_le_of_energies
    (fun i => p i (x i)) _ _ _ _ _ _ _ hp0 hp1
    (ell₁ * ‖u‖) (ell₁ * ‖v‖) (ell₁ * ‖w‖)
    (ell₂ * ‖u‖ * ‖v‖) (ell₂ * ‖u‖ * ‖w‖) (ell₂ * ‖v‖ * ‖w‖)
    (ell₃ * ‖u‖ * ‖v‖ * ‖w‖)
    (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity)
    (hfirst u) (hfirst v) (hfirst w) (hsecond u v) (hsecond u w) (hsecond v w) hthirdsum
  convert hh using 1
  ring

end
end SampleReuse
