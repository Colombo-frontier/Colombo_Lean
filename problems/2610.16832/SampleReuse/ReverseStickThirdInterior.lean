import SampleReuse.ReverseStickThirdBlockScore
import SampleReuse.ReverseStickThirdMixtureBound

/-! Third-order reverse-selector estimate for interior Bernoulli gates. -/

open SecondOrder
open scoped BigOperators Classical
namespace SampleReuse
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

def thirdMixtureBound (v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ : ℝ) : ℝ :=
  v₃ + v₀ * (2 * ell₃ + 6 * ell₁ * ell₂ + 6 * ell₁ ^ 3) +
    3 * v₂ * ell₁ + 6 * v₁ * (ell₂ + ell₁ ^ 2)

theorem blockMixture_third_interior
    (p : ι → E → ℝ) (V : (ι → Bool) → HomogeneousBlocks ι E → ℝ)
    (hp : ∀ i, ContDiff ℝ 3 (p i)) (hV : ∀ ω, ContDiff ℝ 3 (V ω))
    (x : HomogeneousBlocks ι E) (hp0 : ∀ i, 0 < p i (x i)) (hp1 : ∀ i, p i (x i) < 1)
    (v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ : ℝ)
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hell₁ : 0 ≤ ell₁) (hell₂ : 0 ≤ ell₂) (hell₃ : 0 ≤ ell₃)
    (hval : ∀ ω, |V ω x| ≤ v₀)
    (hder : ∀ ω, ‖fderiv ℝ (V ω) x‖ ≤ v₁)
    (hsecond : ∀ ω, ‖fderiv ℝ (fderiv ℝ (V ω)) x‖ ≤ v₂)
    (hthird : ∀ ω, ‖iteratedFDeriv ℝ 3 (V ω) x‖ ≤ v₃)
    (hF : ∀ i, ‖fderiv ℝ (p i) (x i)‖ ^ 2 ≤ ell₁ ^ 2 * p i (x i) * (1 - p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ^ 2 ≤
      ell₂ ^ 2 * p i (x i) * (1 - p i (x i)))
    (hG : ∀ i, ‖iteratedFDeriv ℝ 3 (p i) (x i)‖ ≤ ell₃) :
    ‖iteratedFDeriv ℝ 3
      (bernoulliMixture (fun i (y : HomogeneousBlocks ι E) => p i (y i)) V) x‖ ≤
      thirdMixtureBound v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ := by
  let q := fun i (y : HomogeneousBlocks ι E) => p i (y i)
  have hp2 (i : ι) : ContDiff ℝ 2 (p i) := (hp i).of_le (by decide)
  have hq (i : ι) : ContDiff ℝ 3 (q i) := (hp i).comp (blockProj (E := E) i).contDiff
  have hs (u : HomogeneousBlocks ι E) :
      Real.sqrt (bernoulliFisherEnergy (fun i => p i (x i)) (fun i => fderiv ℝ (q i) x u)) ≤
        ell₁ * ‖u‖ := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    simpa only [mul_pow] using blockGate_fisher_energy p hp2 x hp0 hp1 ell₁ hF u
  have hH' (i : ι) : ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ≤ ell₂ := by
    have hvar : p i (x i) * (1 - p i (x i)) ≤ 1 := by nlinarith [sq_nonneg (p i (x i))]
    have hm := mul_le_mul_of_nonneg_left hvar (sq_nonneg ell₂)
    have hsq : ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ^ 2 ≤ ell₂ ^ 2 := by
      nlinarith [hH i]
    nlinarith
  have hsecondEnergy (u v : HomogeneousBlocks ι E) :
      (∑ i, |secondBilinear (q i) x u v|) ≤ ell₂ * ‖u‖ * ‖v‖ :=
    blockGate_second_energy p hp2 x ell₂ hell₂ hH' u v
  have hS (u : HomogeneousBlocks ι E) :=
    (bernoulliScoreSum_abs_mean_le (fun i => p i (x i))
      (fun i => fderiv ℝ (q i) x u) hp0 hp1).trans (hs u)
  have hK (u v : HomogeneousBlocks ι E) :
      pmfMean (bernoulliProduct (fun i => p i (x i))
        (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun ω => |bernoulliSecondScore (fun i => p i (x i))
          (fun i => fderiv ℝ (q i) x u) (fun i => fderiv ℝ (q i) x v)
          (fun i => secondBilinear (q i) x u v) ω|) ≤
        (2 * (ell₂ + ell₁ ^ 2)) * ‖u‖ * ‖v‖ := by
    apply (bernoulliSecondScore_abs_mean_le _ _ _ _ hp0 hp1).trans
    calc
      _ ≤ 2 * (ell₂ * ‖u‖ * ‖v‖) + 2 * (ell₁ * ‖u‖) * (ell₁ * ‖v‖) := by
        gcongr
        · exact hsecondEnergy u v
        · exact hs u
        · exact hs v
      _ = _ := by ring
  have hh := bernoulliMixture_third_operator_bound q V hq hV x hp0 hp1
    v₀ v₁ v₂ v₃ ell₁ (2 * (ell₂ + ell₁ ^ 2))
    (2 * ell₃ + 6 * ell₁ * ell₂ + 6 * ell₁ ^ 3)
    hv₀ hv₁ hv₂ hv₃ hell₁ (by positivity) (by positivity)
    hval hder hsecond hthird hS hK
    (fun u v w => blockGate_thirdScore_abs_mean_le p hp x u v w hp0 hp1
      ell₁ ell₂ ell₃ hell₁ hell₂ hell₃ hF hH hG)
  convert hh using 1
  unfold thirdMixtureBound
  ring

end
end SampleReuse
