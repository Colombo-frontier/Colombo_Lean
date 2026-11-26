import SecondOrder.IntegralEnergy
import SecondOrder.SignOrthogonality
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def signLaw (M : ℕ) : Measure (Fin M → Bool) := (PMF.uniformOfFintype (Fin M → Bool)).toMeasure

instance signLaw_probability (M : ℕ) : IsProbabilityMeasure (signLaw M) := by
  unfold signLaw
  infer_instance

theorem integral_signLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {M : ℕ} (f : (Fin M → Bool) → E) : (∫ w, f w ∂signLaw M) = uniformMean f := by
  exact PMF.integral_eq_sum _ _

/-- All non-sign randomness is on Ω. It may have an arbitrary, continuous
distribution. The i-th direction can use this randomness and earlier signs,
but not the new sign at i. Zero directions encode predictable stopping. -/
def mixedInnovation {Ω E : Type*} [AddCommGroup E] [Module ℝ E] {M : ℕ}
    (v : Ω → (i : Fin M) → (Fin i.val → Bool) → E) (i : Fin M)
    (w : Ω × (Fin M → Bool)) : E := signedInnovation (v w.1) i w.2

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Orthogonality now includes arbitrary independent non-sign randomness.
It is derived from the actual fresh-sign experiment by Fubini. -/
theorem mixedInnovation_orthogonal {M : ℕ}
    (v : Ω → (i : Fin M) → (Fin i.val → Bool) → E)
    (hv : ∀ i, Integrable (mixedInnovation v i) (μ.prod (signLaw M)))
    (hv2 : ∀ i, Integrable (fun w => ‖mixedInnovation v i w‖^2) (μ.prod (signLaw M)))
    (i j : Fin M) (hij : i ≠ j) :
    (∫ w, ⟪mixedInnovation v i w,mixedInnovation v j w⟫_ℝ ∂μ.prod (signLaw M)) = 0 := by
  rw [integral_prod _ (integrable_inner_of_second_moments (hv i) (hv j) (hv2 i) (hv2 j))]
  have he (x : Ω) : (∫ w, ⟪mixedInnovation v i (x,w),mixedInnovation v j (x,w)⟫_ℝ ∂signLaw M) = 0 := by
    rw [integral_signLaw]
    exact signedInnovation_orthogonal (v x) i j hij
  simp_rw [he]
  simp

theorem mixed_sign_dyadic_energy (M L q : ℕ)
    (a : Fin M → (Ω × (Fin M → Bool)) → E)
    (v : Ω → (i : Fin M) → (Fin i.val → Bool) → E)
    (ha : ∀ k, Integrable (a k) (μ.prod (signLaw M)))
    (hm : ∀ k, Integrable (mixedInnovation v k) (μ.prod (signLaw M)))
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) (μ.prod (signLaw M)))
    (hm2 : ∀ k, Integrable (fun w => ‖mixedInnovation v k w‖^2) (μ.prod (signLaw M)))
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q) :
    (∫ w, ∑ i : Fin L × Fin M,
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+mixedInnovation v k w)‖^2 ∂μ.prod (signLaw M)) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂μ.prod (signLaw M))+
        (∫ w, ∑ k, ‖mixedInnovation v k w‖^2 ∂μ.prod (signLaw M))) :=
  integral_dyadic_energy M L q a (mixedInnovation v) ha hm ha2 hm2 hs
    (mixedInnovation_orthogonal v hm hm2)

theorem mixed_sign_selected_energy (M L q : ℕ)
    (a : Fin M → (Ω × (Fin M → Bool)) → E)
    (v : Ω → (i : Fin M) → (Fin i.val → Bool) → E)
    (created : (Ω × (Fin M → Bool)) → Fin L × Fin M → Prop)
    (hc : ∀ i, MeasurableSet {w | created w i})
    (ha : ∀ k, Integrable (a k) (μ.prod (signLaw M)))
    (hm : ∀ k, Integrable (mixedInnovation v k) (μ.prod (signLaw M)))
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) (μ.prod (signLaw M)))
    (hm2 : ∀ k, Integrable (fun w => ‖mixedInnovation v k w‖^2) (μ.prod (signLaw M)))
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q) :
    (∫ w, ∑ i : Fin L × Fin M, if created w i then
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+mixedInnovation v k w)‖^2 else 0
      ∂μ.prod (signLaw M)) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂μ.prod (signLaw M))+
        (∫ w, ∑ k, ‖mixedInnovation v k w‖^2 ∂μ.prod (signLaw M))) :=
  integral_selected_dyadic_energy M L q a (mixedInnovation v) created hc ha hm ha2 hm2 hs
    (mixedInnovation_orthogonal v hm hm2)

end
end SecondOrder
