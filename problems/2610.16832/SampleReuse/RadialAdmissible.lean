import SampleReuse.RadialGlobalBounds
import SampleReuse.FiniteAdmissible

open SecondOrder MeasureTheory

namespace SampleReuse
noncomputable section

def radialGradientBudget (b R : ℝ) (B : ℕ → ℝ) : ℝ :=
  B 1+R⁻¹*cutoffRadialConstant 1*B 0+b

def radialSecondBudget (b R : ℝ) (B : ℕ → ℝ) : ℝ :=
  B 2+2*(R⁻¹*cutoffRadialConstant 1)*B 1+(R⁻¹)^2*cutoffRadialConstant 2*B 0+
    b*R*(R⁻¹)^2*wallRadialConstant 2

def radialThirdBudget (b R : ℝ) (B : ℕ → ℝ) : ℝ :=
  B 3+3*(R⁻¹*cutoffRadialConstant 1)*B 2+
    3*((R⁻¹)^2*cutoffRadialConstant 2)*B 1+(R⁻¹)^3*cutoffRadialConstant 3*B 0+
    b*R*(R⁻¹)^3*wallRadialConstant 3

/-- The exact radial scalar loss satisfies every field of the paper's model
once its explicit derivative budgets fit the fixed model parameters. -/
theorem radial_deterministic_admissible {d : ℕ} (P : Parameters)
    {f : Point d → ℝ} (hf : ContDiff ℝ 3 f) (hf0 : f 0 = 0)
    {b R D : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (hD : 0 ≤ D)
    (hflo : ∀ x, -D ≤ f x) (hgap : D ≤ P.gap)
    (B : ℕ → ℝ) (hB : ∀ j, j ≤ 3 → 0 ≤ B j)
    (hjet : ∀ x j, j ≤ 3 → ‖iteratedFDeriv ℝ j f x‖ ≤ B j)
    (hG : radialGradientBudget b R B ≤ P.gradientBound)
    (hL1 : radialSecondBudget b R B ≤ P.gradientLip)
    (hL2 : radialThirdBudget b R B ≤ P.hessianLip) :
    Admissible (PMF.pure ()).toMeasure P (radialGlobalization f b R)
      (fun _ : Unit => radialGlobalization f b R) 0 := by
  let g := radialGlobalization f b R
  have hg3 : ContDiff ℝ 3 g := radialGlobalization_contDiff hf b hR
  have hg2 : ContDiff ℝ 2 g := hg3.of_le (by decide)
  have hsecond : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ P.gradientLip :=
    fun x => (radialGlobalization_second_bound hf hb hR B x hB (hjet x)).trans hL1
  have hthird : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ P.hessianLip :=
    fun x => (radialGlobalization_third_bound hf hb hR B x hB (hjet x)).trans hL2
  apply finite_admissible_of_uniform_bounds (PMF.pure ()) P g (fun _ : Unit => g) 0
    (fun _ => hg2)
  · intro x
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
  · intro x
    have hl := radialGlobalization_lower hb hR hD x (hflo x)
    have hz := radialGlobalization_zero hf0 b hR
    change g 0-g x ≤ P.gap
    dsimp [g]
    rw [hz]
    linarith
  · intro _ x y
    exact gradient_lipschitz_of_second_bound hg2 hsecond y x
  · intro _ x y
    exact fderiv_gradient_lipschitz_of_third_bound hg3 hthird y x
  · intro _ x
    simpa only [sub_self, norm_zero] using P.gradientNoise_pos.le
  · intro _ x
    simpa only [sub_self, norm_zero] using P.hessianNoise_pos.le
  · intro x
    exact (radialGlobalization_gradient_bound hf hb hR B x hB (hjet x)).trans hG

end
end SampleReuse
