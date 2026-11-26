import SampleReuse.ReverseStickThirdBounds

/-! All four estimates in the manuscript's third-order reverse stick lemma. -/

open SecondOrder
namespace SampleReuse
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance {n : ℕ} : NormedSpace ℝ (HomogeneousBlocks (Fin n) E) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ (HomogeneousBlocks (Fin n) E →L[ℝ] ℝ) := inferInstance

/-- Source Lemma `lem:thirdstick`: arbitrary full-space payloads and disjoint
Hilbert blocks, including gates on the boundary. Explicit constants are at
most 6 in the paper's universal-C formulation and independent of n. -/
theorem reverse_stick_localization {n : ℕ}
    (p : Fin n → E → ℝ) (V : ℕ → HomogeneousBlocks (Fin n) E → ℝ)
    (hp : ∀ i, ContDiff ℝ 3 (p i)) (hV : ∀ k ≤ n, ContDiff ℝ 3 (V k))
    (x : HomogeneousBlocks (Fin n) E)
    (hp0 : ∀ i, 0 ≤ p i (x i)) (hp1 : ∀ i, p i (x i) ≤ 1)
    (v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ : ℝ)
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hell₁ : 0 ≤ ell₁) (hell₂ : 0 ≤ ell₂) (hell₃ : 0 ≤ ell₃)
    (hval : ∀ k ≤ n, |V k x| ≤ v₀)
    (hder : ∀ k ≤ n, ‖fderiv ℝ (V k) x‖ ≤ v₁)
    (hsecond : ∀ k ≤ n, ‖fderiv ℝ (fderiv ℝ (V k)) x‖ ≤ v₂)
    (hthird : ∀ k ≤ n, ‖iteratedFDeriv ℝ 3 (V k) x‖ ≤ v₃)
    (hF : ∀ i, ‖fderiv ℝ (p i) (x i)‖ ^ 2 ≤ ell₁ ^ 2 * p i (x i) * (1 - p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ^ 2 ≤
      ell₂ ^ 2 * p i (x i) * (1 - p i (x i)))
    (hG : ∀ i, ‖iteratedFDeriv ℝ 3 (p i) (x i)‖ ≤ ell₃) :
    ContDiff ℝ 3 (reverseBlockSelector p V) ∧
      |reverseBlockSelector p V x| ≤ v₀ ∧
      ‖fderiv ℝ (reverseBlockSelector p V) x‖ ≤ v₁ + v₀ * ell₁ ∧
      ‖fderiv ℝ (fderiv ℝ (reverseBlockSelector p V)) x‖ ≤
        v₂ + 2 * v₁ * ell₁ + 2 * v₀ * (ell₂ + ell₁ ^ 2) ∧
      ‖iteratedFDeriv ℝ 3 (reverseBlockSelector p V) x‖ ≤
        thirdMixtureBound v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ := by
  have hthree := reverseBlockSelector_third_bound p V hp hV x hp0 hp1
    v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ hv₀ hv₁ hv₂ hv₃ hell₁ hell₂ hell₃
    hval hder hsecond hthird hF hH hG
  have hH' (i : Fin n) : ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ≤ ell₂ := by
    have hvar : p i (x i) * (1 - p i (x i)) ≤ 1 := by nlinarith [sq_nonneg (p i (x i))]
    have hm := mul_le_mul_of_nonneg_left hvar (sq_nonneg ell₂)
    have hsq : ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ^ 2 ≤ ell₂ ^ 2 := by
      nlinarith [hH i]
    nlinarith
  have htwo := reverseSelector_bounds p V
    (fun i => (hp i).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
    (fun k hk => (hV k hk).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
    x hp0 hp1 v₀ v₁ v₂ ell₁ ell₂ hv₀ hv₁ hv₂ hell₁ hell₂ hval
    (by simpa only [norm_gradient_eq_fderiv] using hder)
    (by simpa only [norm_hessian_eq_second_fderiv] using hsecond)
    (by simpa only [norm_gradient_eq_fderiv] using hF)
    (by simpa only [norm_hessian_eq_second_fderiv] using hH')
  exact ⟨hthree.1, htwo.2.1,
    by simpa only [norm_gradient_eq_fderiv] using htwo.2.2.1,
    by simpa only [norm_hessian_eq_second_fderiv] using htwo.2.2.2, hthree.2⟩

end
end SampleReuse
