import Nonsmooth.RecursiveIncrementIntegral
import Nonsmooth.RecursiveGaussianStepEnergy

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] {r : ℕ}

theorem recursiveGaussian_mean_increment_energy {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (hL : MemLp (fun a : Fin (r + 1) → E => ∑ i, a i) 2 Q)
    (hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i)))
    (u : ∀ n, ResponseHistory (r + 1) n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    (∫ a : Fin (r + 1) → E,
      ‖recursiveSupportMean Q u hu (n + 1) (recursiveSupportResponse u (n + 1) a) -
        recursiveSupportMean Q u hu n (recursiveSupportResponse u n a)‖ ^ 2 ∂Q) ≤
      512 * s ^ 2 * Real.log (Real.exp 1 * ((r + 1 : ℕ) : ℝ)) := by
  have hi := recursiveSupportMean_increment_integral Q hL u hu n
  have hb := recursiveGaussian_step_energy_ae hs Q hQ hrow u hu n
  letI : IsProbabilityMeasure (Q.map (recursiveSupportResponse u n)) :=
    Measure.isProbabilityMeasure_map (recursiveSupportResponse_measurable u hu n).aemeasurable
  rw [hi.2]
  calc
    _ ≤ ∫ _h, 512 * s ^ 2 * Real.log (Real.exp 1 * ((r + 1 : ℕ) : ℝ))
        ∂Q.map (recursiveSupportResponse u n) := integral_mono_ae hi.1 (integrable_const _) hb
    _ = _ := by rw [integral_const, measureReal_univ_eq_one, one_smul]

end
end Nonsmooth
