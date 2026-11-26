import SecondOrder.BlockMixtureInterior
import SecondOrder.LastSuccessSelector

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def reverseBlockSelector {n : ℕ} (p : Fin n → E → ℝ)
    (V : ℕ → HomogeneousBlocks (Fin n) E → ℝ) (x : HomogeneousBlocks (Fin n) E) : ℝ :=
  reverseSelectorValue (fun k => if hk : k < n then p ⟨k,hk⟩ (x ⟨k,hk⟩) else 0)
    (fun k => V k x) n

theorem reverseBlockSelector_eq_mixture {n : ℕ} (p : Fin n → E → ℝ)
    (V : ℕ → HomogeneousBlocks (Fin n) E → ℝ) :
    reverseBlockSelector p V =
      bernoulliMixture (fun i (y : HomogeneousBlocks (Fin n) E) => p i (y i))
        (fun w => V (lastSuccess w)) := by
  funext x
  let b : ℕ → ℝ := fun k => if hk : k<n then p ⟨k,hk⟩ (x ⟨k,hk⟩) else 0
  have hb (i : Fin n) : b i = p i (x i) := by simp [b, i.isLt]
  calc
    _ = lastSuccessAverage b (fun k => V k x) n := (lastSuccessAverage_eq_reverseSelector b _ n).symm
    _ = _ := by
      unfold lastSuccessAverage bernoulliMixture
      apply Finset.sum_congr (by ext w; simp)
      intro w _
      simp only [hb]

end

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The manuscript's actual reverse-product selector estimate at interior gates.
The boundary case is deliberately not included in this theorem. -/
theorem reverseSelector_interior {n : ℕ} (p : Fin n → E → ℝ)
    (V : ℕ → HomogeneousBlocks (Fin n) E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ k ≤ n, ContDiff ℝ 2 (V k))
    (x : HomogeneousBlocks (Fin n) E) (hp0 : ∀ i, 0 < p i (x i)) (hp1 : ∀ i, p i (x i) < 1)
    (v₀ v₁ v₂ ell h : ℝ) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (hell : 0 ≤ ell) (hh : 0 ≤ h)
    (hval : ∀ k ≤ n, |V k x| ≤ v₀) (hder : ∀ k ≤ n, ‖gradient (V k) x‖ ≤ v₁)
    (hsecond : ∀ k ≤ n, ‖fderiv ℝ (gradient (V k)) x‖ ≤ v₂)
    (hF : ∀ i, ‖gradient (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (gradient (p i)) (x i)‖ ≤ h) :
    ContDiff ℝ 2 (reverseBlockSelector p V) ∧ |reverseBlockSelector p V x| ≤ v₀ ∧
      ‖gradient (reverseBlockSelector p V) x‖ ≤ v₁+v₀*ell ∧
      ‖fderiv ℝ (gradient (reverseBlockSelector p V)) x‖ ≤ v₂+2*v₁*ell+2*v₀*(h+ell^2) := by
  rw [reverseBlockSelector_eq_mixture]
  exact blockMixture_interior p (fun w => V (lastSuccess w)) hp
    (fun w => hV _ (lastSuccess_le w)) x hp0 hp1 v₀ v₁ v₂ ell h hv₀ hv₁ hv₂ hell hh
    (fun w => hval _ (lastSuccess_le w)) (fun w => hder _ (lastSuccess_le w))
    (fun w => hsecond _ (lastSuccess_le w)) hF hH

end
end SecondOrder
