import SecondOrder.DependentBlockMixtureBounds
import SecondOrder.LastSuccessSelector

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {n : ℕ} {E : Fin n → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

def dependentReverseSelector (p : (i : Fin n) → E i → ℝ)
    (V : ℕ → PiLp 2 E → ℝ) (x : PiLp 2 E) : ℝ :=
  reverseSelectorValue (fun k => if hk : k < n then p ⟨k,hk⟩ (x ⟨k,hk⟩) else 0)
    (fun k => V k x) n

theorem dependentReverseSelector_eq_mixture (p : (i : Fin n) → E i → ℝ)
    (V : ℕ → PiLp 2 E → ℝ) :
    dependentReverseSelector p V =
      bernoulliMixture (fun i (y : PiLp 2 E) => p i (y i))
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


/-- The reverse-selector lemma for arbitrary finite Hilbert blocks, with the
manuscript's constants, including
boundary gates. All gradients and Hessians are derivatives of the scalar sum. -/
theorem dependentReverseSelector_bounds (p : (i : Fin n) → E i → ℝ)
    (V : ℕ → PiLp 2 E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ k ≤ n, ContDiff ℝ 2 (V k))
    (x : PiLp 2 E) (hp0 : ∀ i, 0 ≤ p i (x i)) (hp1 : ∀ i, p i (x i) ≤ 1)
    (v₀ v₁ v₂ ell h : ℝ) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (hell : 0 ≤ ell) (hh : 0 ≤ h)
    (hval : ∀ k ≤ n, |V k x| ≤ v₀) (hder : ∀ k ≤ n, ‖gradient (V k) x‖ ≤ v₁)
    (hsecond : ∀ k ≤ n, ‖fderiv ℝ (gradient (V k)) x‖ ≤ v₂)
    (hF : ∀ i, ‖gradient (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (gradient (p i)) (x i)‖ ≤ h) :
    ContDiff ℝ 2 (dependentReverseSelector p V) ∧ |dependentReverseSelector p V x| ≤ v₀ ∧
      ‖gradient (dependentReverseSelector p V) x‖ ≤ v₁+v₀*ell ∧
      ‖fderiv ℝ (gradient (dependentReverseSelector p V)) x‖ ≤ v₂+2*v₁*ell+2*v₀*(h+ell^2) := by
  rw [dependentReverseSelector_eq_mixture]
  exact dependentBlockMixture_bounds p (fun w => V (lastSuccess w)) hp
    (fun w => hV _ (lastSuccess_le w)) x hp0 hp1 v₀ v₁ v₂ ell h hv₀ hv₁ hv₂ hell hh
    (fun w => hval _ (lastSuccess_le w)) (fun w => hder _ (lastSuccess_le w))
    (fun w => hsecond _ (lastSuccess_le w)) hF hH

end
end SecondOrder
