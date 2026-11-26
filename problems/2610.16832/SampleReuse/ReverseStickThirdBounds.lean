import SampleReuse.ReverseStickThirdInterior
import SampleReuse.ReverseStickThirdRegularization
import SecondOrder.ConservativeSelector

/-! Length-independent third derivative bound for the actual reverse stick selector. -/

open SecondOrder
namespace SampleReuse
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem blockMixture_third_bound
    (p : ι → E → ℝ) (V : (ι → Bool) → HomogeneousBlocks ι E → ℝ)
    (hp : ∀ i, ContDiff ℝ 3 (p i)) (hV : ∀ ω, ContDiff ℝ 3 (V ω))
    (x : HomogeneousBlocks ι E) (hp0 : ∀ i, 0 ≤ p i (x i)) (hp1 : ∀ i, p i (x i) ≤ 1)
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
  have hq (i : ι) : ContDiff ℝ 3 (q i) := (hp i).comp (blockProj (E := E) i).contDiff
  have hp2 (i : ι) : ContDiff ℝ 2 (p i) := (hp i).of_le (by decide)
  have hb (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
      ‖iteratedFDeriv ℝ 3 (regularizedMixture q V δ) x‖ ≤
        thirdMixtureBound v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ := by
    exact blockMixture_third_interior (fun i => regularizedGate δ (p i)) V
      (fun i => regularizedGate_contDiff (hp i) δ) hV x
      (fun i => (regularizedGate_interior hδ0 hδ1 (hp0 i) (hp1 i)).1)
      (fun i => (regularizedGate_interior hδ0 hδ1 (hp0 i) (hp1 i)).2)
      v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ hv₀ hv₁ hv₂ hv₃ hell₁ hell₂ hell₃
      hval hder hsecond hthird
      (fun i => regularizedGate_fisher ((hp i).differentiable (by decide)) hδ0.le hδ1.le (x i) (hF i))
      (fun i => regularizedGate_second_fisher (hp2 i) hδ0.le hδ1.le (x i) (hH i))
      (fun i => regularizedGate_third_bound (hp i) hδ0.le hδ1.le (x i) (hG i))
  have hh := continuous_le_at_zero_of_Ioo (regularizedMixture_continuous_third q V hq hV x) hb
  simpa only [regularizedMixture_zero] using hh

/-- The paper's reverse stick expression, with arbitrary full-space payloads.
The constant does not involve n, the number of gates. Boundary gates 0 and 1
are included, and the derivative is the genuine third Fréchet derivative. -/
theorem reverseBlockSelector_third_bound {n : ℕ}
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
      ‖iteratedFDeriv ℝ 3 (reverseBlockSelector p V) x‖ ≤
        thirdMixtureBound v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ := by
  constructor
  · exact reverseBlockSelector_contDiff p V hp hV
  · rw [reverseBlockSelector_eq_mixture]
    exact blockMixture_third_bound p (fun ω => V (lastSuccess ω)) hp
      (fun ω => hV _ (lastSuccess_le ω)) x hp0 hp1
      v₀ v₁ v₂ v₃ ell₁ ell₂ ell₃ hv₀ hv₁ hv₂ hv₃ hell₁ hell₂ hell₃
      (fun ω => hval _ (lastSuccess_le ω)) (fun ω => hder _ (lastSuccess_le ω))
      (fun ω => hsecond _ (lastSuccess_le ω)) (fun ω => hthird _ (lastSuccess_le ω))
      hF hH hG

end
end SampleReuse
