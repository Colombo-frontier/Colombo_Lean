import Nonsmooth.RecursiveGaussianMeanEnergy
import Nonsmooth.PolicyRecursiveMean
import Nonsmooth.GaussianEnergyOnlyReduction

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianSupportMean_all_step_log_energy {k : ℕ} [Nonempty (Fin k)]
    {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    (∫ a : Fin k → E, ‖gaussianSupportMean p ω (n + 1) a - gaussianSupportMean p ω n a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        512 * Real.log (Real.exp 1 * (k : ℝ)) / (Module.finrank ℝ E : ℝ) := by
  cases k with
  | zero => exact Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0)))
  | succ r =>
    let Q := Measure.pi (fun _ : Fin (r + 1) => gaussianAmbientRowLaw E)
    let s := (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹
    have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))
    have hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q :=
      finiteProductKernel_independent (fun _ : Fin (r + 1) => Kernel.const Unit (gaussianAmbientRowLaw E)) ()
    have hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i)) := by
      intro i
      rw [(finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq]
      exact gaussianAmbientRow_polytope
    let u := policyResponseQuery (k := r + 1) p ω
    have hu : ∀ j, Measurable (u j) := fun j => policyResponseQuery_measurable p hp ω j
    have hb := recursiveGaussian_mean_increment_energy hs Q gaussianAmbientRows_aggregate_memLp
      hQ hrow u hu n
    have he (j : ℕ) : gaussianSupportMean p ω j =ᵐ[Q]
        fun a => recursiveSupportMean Q u hu j (recursiveSupportResponse u j a) :=
      policy_aggregate_mean_ae_recursive Q gaussianAmbientRows_aggregate_integrable p hp ω j
    have henergy : (∫ a, ‖gaussianSupportMean p ω (n + 1) a - gaussianSupportMean p ω n a‖ ^ 2 ∂Q) =
        ∫ a, ‖recursiveSupportMean Q u hu (n + 1) (recursiveSupportResponse u (n + 1) a) -
          recursiveSupportMean Q u hu n (recursiveSupportResponse u n a)‖ ^ 2 ∂Q := by
      apply integral_congr_ae
      filter_upwards [he (n + 1), he n] with a hn hprev
      rw [hn, hprev]
    change (∫ a, ‖gaussianSupportMean p ω (n + 1) a - gaussianSupportMean p ω n a‖ ^ 2 ∂Q) ≤ _
    rw [henergy]
    apply hb.trans_eq
    dsimp only [s]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring

theorem gaussianPosteriorLogEnergyEstimate_proved : GaussianPosteriorLogEnergyEstimate E 512 := by
  intro k hk
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  intro _hd _hkd S mS
  letI : MeasurableSpace S := mS
  intro p hp n
  exact gaussianSupportMean_all_step_log_energy p hp () n

end
end Nonsmooth
