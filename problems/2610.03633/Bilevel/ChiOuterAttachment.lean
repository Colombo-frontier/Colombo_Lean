import Bilevel.ChiOuterWrappedSelectors
import Bilevel.ChiOuterMacro
import Bilevel.ChiRecursiveObjective

/-! Actual outer attachment and exact transport to the selected inner
recursive objective. Every public radial penalty remains outside selectors. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def attachment (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ) (x : E) : ℝ :=
  macroValue M.n M.ell M.width ν M.radius M.frame x +
    ∑ i, ((Q i-1)*wrappedResidual M i x + W i*wrappedSelector M i x)

def outerPerturbation (M : Node E) (Q W : Fin (M.n+1) → ℝ) (x : E) : E →L[ℝ] ℝ :=
  ∑ i, ((Q i-1) • fderiv ℝ (wrappedResidual M i) x + W i • fderiv ℝ (wrappedSelector M i) x)

theorem attachment_fderiv (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ)
    (hR : 0 < M.radius) (x : E) :
    fderiv ℝ (attachment M ν Q W) x =
      fderiv ℝ (macroValue M.n M.ell M.width ν M.radius M.frame) x + outerPerturbation M Q W x := by
  have hm := (macro_hasGradientAt M.n M.ell M.width ν M.radius hR M.frame x).hasFDerivAt
  have hd (i : Fin (M.n+1)) :
      HasFDerivAt (fun t => (Q i-1)*wrappedResidual M i t+W i*wrappedSelector M i t)
        ((Q i-1) • fderiv ℝ (wrappedResidual M i) x+W i • fderiv ℝ (wrappedSelector M i) x) x :=
    (((wrappedResidual_contDiff M i 1).differentiable (by norm_num) x).hasFDerivAt.const_mul (Q i-1)).add
      (((wrappedSelector_contDiff M i 1).differentiable (by norm_num) x).hasFDerivAt.const_mul (W i))
  have hs := HasFDerivAt.sum (fun (i : Fin (M.n+1)) (_ : i ∈ Finset.univ) => hd i)
  rw [hm.fderiv]
  exact (hm.add hs).fderiv

theorem wrapped_inactive (M : Node E) (i : Fin (M.n+1)) (x : E)
    (hi : wrappedSelector M i x = 0) : wrappedResidual M i x = 0 ∧
      fderiv ℝ (wrappedSelector M i) x = 0 ∧ fderiv ℝ (wrappedResidual M i) x = 0 := by
  rcases wrappedSelector_jet_cases M i x with h|h
  · exact ⟨h.2.2.1,h.2.1,h.2.2.2⟩
  · have hs : M.selector i x = 0 := h.1.symm.trans hi
    rw [h.2.1,h.2.2.1,h.2.2.2]
    exact ⟨M.residual_zero_of_selector_zero i x hs,M.selector_fderiv_zero i x hs,M.residual_fderiv_zero i x hs⟩

theorem outerPerturbation_eq_active (M : Node E) (Q W : Fin (M.n+1) → ℝ) (x : E)
    (i : Fin (M.n+1)) (hi : wrappedSelector M i x ≠ 0) :
    outerPerturbation M Q W x =
      (Q i-1) • fderiv ℝ (wrappedResidual M i) x + W i • fderiv ℝ (wrappedSelector M i) x := by
  unfold outerPerturbation
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hj : wrappedSelector M j x = 0 := by
      by_contra hj
      exact hji (wrappedSelector_unique M j i x hj hi)
    rw [(wrapped_inactive M j x hj).2.1,(wrapped_inactive M j x hj).2.2]
    simp
  · simp

theorem outerPerturbation_zero (M : Node E) (Q W : Fin (M.n+1) → ℝ) (x : E)
    (hi : ∀ i, wrappedSelector M i x = 0) : outerPerturbation M Q W x = 0 := by
  unfold outerPerturbation
  apply Finset.sum_eq_zero
  intro i _
  rw [(wrapped_inactive M i x (hi i)).2.1,(wrapped_inactive M i x (hi i)).2.2]
  simp

theorem attachment_eq_active (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ) (x : E)
    (i : Fin (M.n+1)) (hi : wrappedSelector M i x ≠ 0) :
    attachment M ν Q W x = macroValue M.n M.ell M.width ν M.radius M.frame x +
      (Q i-1)*wrappedResidual M i x+W i*wrappedSelector M i x := by
  have hs : (∑ j, ((Q j-1)*wrappedResidual M j x+W j*wrappedSelector M j x)) =
      (Q i-1)*wrappedResidual M i x+W i*wrappedSelector M i x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hj : wrappedSelector M j x = 0 := by
        by_contra hj
        exact hji (wrappedSelector_unique M j i x hj hi)
      rw [hj,(wrapped_inactive M j x hj).1]
      ring
    · simp
  unfold attachment
  rw [hs]
  ring

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerObjective (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) (d : ℕ)
    (x : E) (u : ℕ → F) : ℝ :=
  attachment M ν (fun i => (D 0 [i.val]).release (u 0))
    (fun i => payloadValue D d 0 [i.val] u) x + publicValue ρ R d 0 u

theorem outerObjective_eq_child (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (x : E) (u : ℕ → F) (i : Fin (M.n+1)) (hi : wrappedSelector M i x ≠ 0) :
    outerObjective M ν D ρ R d x u =
      (macroValue M.n M.ell M.width ν M.radius M.frame x-wrappedResidual M i x) +
        objective D ρ R d 0 [i.val] (wrappedSelector M i x) (wrappedResidual M i x) u := by
  unfold outerObjective
  rw [attachment_eq_active M ν _ _ x i hi]
  unfold objective
  ring

theorem outerObjective_inner_derivative (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d k : ℕ) (x : E) (u : ℕ → F) (i : Fin (M.n+1)) (hi : wrappedSelector M i x ≠ 0) (v : F) :
    fderiv ℝ (fun t => outerObjective M ν D ρ R d x (Function.update u k t)) v =
      fderiv ℝ (fun t => objective D ρ R d 0 [i.val] (wrappedSelector M i x)
        (wrappedResidual M i x) (Function.update u k t)) v := by
  have he : (fun t => outerObjective M ν D ρ R d x (Function.update u k t)) =
      fun t => (macroValue M.n M.ell M.width ν M.radius M.frame x-wrappedResidual M i x)+
        objective D ρ R d 0 [i.val] (wrappedSelector M i x) (wrappedResidual M i x) (Function.update u k t) :=
    funext (fun _ => outerObjective_eq_child M ν D ρ R d x _ i hi)
  rw [he,fderiv_const_add]

end Bilevel.ChiOuter
