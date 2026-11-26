import Nonsmooth.RecursiveResponseChain
import Nonsmooth.GaussianPolytopeParametricUpdate

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {r : ℕ}

def GaussianRecursiveState (s : ℝ) (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory (r + 1) n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (h : ResponseHistory (r + 1) n) : Prop :=
  iIndepFun (fun i (a : Fin (r + 1) → E) => a i) (recursiveSupportBelief Q u hu n h) ∧
    ∀ i, GaussianPolytopeRow s ((recursiveSupportBelief Q u hu n h).map (fun a => a i))

theorem gaussianRecursiveState_zero (s : ℝ) (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i)))
    (u : ∀ n, ResponseHistory (r + 1) n → E) (hu : ∀ n, Measurable (u n))
    (h : ResponseHistory (r + 1) 0) : GaussianRecursiveState s Q u hu 0 h := ⟨hQ, hrow⟩

theorem gaussianRecursiveState_step {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory (r + 1) n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (h : ResponseHistory (r + 1) n) (hh : GaussianRecursiveState s Q u hu n h) :
    ∀ᵐ g ∂recursiveResponseStep Q u hu n h, GaussianRecursiveState s Q u hu (n + 1) g := by
  rw [recursiveResponseStep_apply, recursiveResponseKernel_apply]
  apply (responseHistoryJoin_fixed_embedding h).ae_map_iff.mpr
  filter_upwards [supportPosteriorUpdate_independent_at (recursiveSupportBelief Q u hu n)
      (u n) (hu n) h hh.1,
    gaussianPolytope_posterior_update_at hs (recursiveSupportBelief Q u hu n)
      (u n) (hu n) h hh.1 hh.2] with y hi hr
  simp only [GaussianRecursiveState, recursiveSupportBelief_succ]
  exact ⟨hi, hr⟩

/-- Any measurable consequence of the concrete geometric row class holds
after any finite adaptive response history. The class itself need not be measurable. -/
theorem recursiveGaussian_measurable_consequence {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i)))
    (u : ∀ n, ResponseHistory (r + 1) n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (P : ResponseHistory (r + 1) n → Prop) (hP : MeasurableSet {h | P h})
    (hlocal : ∀ h, GaussianRecursiveState s Q u hu n h → P h) :
    ∀ᵐ h ∂Q.map (recursiveSupportResponse u n), P h := by
  let h₀ : ResponseHistory (r + 1) 0 := Fin.elim0
  have hzero := gaussianRecursiveState_zero s Q hQ hrow u hu h₀
  have h := kernelChain_measurable_consequence (recursiveResponseStep Q u hu)
    (GaussianRecursiveState s Q u hu) (gaussianRecursiveState_step hs Q u hu)
    h₀ hzero n {h | P h} hP hlocal
  rw [recursiveResponseChain_law] at h
  exact h

/-- The same finite-horizon consequences apply to the actual conditional
distribution under the original prior, not just the recursively chosen version. -/
theorem recursiveGaussian_actual_posterior_consequence {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i)))
    (u : ∀ n, ResponseHistory (r + 1) n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (P : ResponseHistory (r + 1) n → Measure (Fin (r + 1) → E) → Prop)
    (hP : MeasurableSet {h | P h (recursiveSupportBelief Q u hu n h)})
    (hlocal : ∀ h, GaussianRecursiveState s Q u hu n h → P h (recursiveSupportBelief Q u hu n h)) :
    ∀ᵐ h ∂Q.map (recursiveSupportResponse u n),
      P h (condDistrib id (recursiveSupportResponse u n) Q h) := by
  filter_upwards [recursiveGaussian_measurable_consequence hs Q hQ hrow u hu n
    (fun h => P h (recursiveSupportBelief Q u hu n h)) hP hlocal,
    recursiveSupportBelief_ae_condDistrib Q u hu n] with h hh he
  rw [← he]
  exact hh

end
end Nonsmooth
