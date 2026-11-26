import Bilevel.ChiOuterAttachment
import Bilevel.ChiRecursiveDescent

/-! Actual outer stop-or-descend. The sole base-gradient premise is supplied
by the independently constructed one-sided macro endgame. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem outerPerturbation_norm_bound (M : Node E) (Q W : Fin (M.n+1) → ℝ) (x : E)
    {Cs Cr δ : ℝ} (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr) (hδ : 0 ≤ δ)
    (hell : 0 ≤ M.ell) (hh : 0 < M.width)
    (i : Fin (M.n+1)) (hi : wrappedSelector M i x ≠ 0)
    (hQ : 0 ≤ Q i ∧ Q i ≤ 1)
    (hs : ‖fderiv ℝ (wrappedSelector M i) x‖ ≤ (Cs/M.width)*Real.sqrt (wrappedSelector M i x))
    (hr : ‖fderiv ℝ (wrappedResidual M i) x‖ ≤ Cr*(M.ell*M.width)*Real.sqrt (wrappedSelector M i x))
    (hW : |W i| ≤ δ*(M.ell*M.width^2)) :
    ‖outerPerturbation M Q W x‖ ≤ (Cr+Cs)*(M.ell*M.width)*((1-Q i)+δ)*Real.sqrt (wrappedSelector M i x) := by
  let s := Real.sqrt (wrappedSelector M i x)
  let g := M.ell*M.width
  have hsub : 0 ≤ 1-Q i := by linarith only [hQ.2]
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hg0 : 0 ≤ g := mul_nonneg hell hh.le
  rw [outerPerturbation_eq_active M Q W x i hi]
  have h₁ : ‖(Q i-1) • fderiv ℝ (wrappedResidual M i) x‖ ≤ (1-Q i)*(Cr*g*s) := by
    rw [norm_smul (Q i-1) (fderiv ℝ (wrappedResidual M i) x),Real.norm_eq_abs,
      abs_of_nonpos (by linarith only [hQ.2])]
    convert mul_le_mul_of_nonneg_left hr hsub using 1
    ring
  have h₂ : ‖W i • fderiv ℝ (wrappedSelector M i) x‖ ≤ Cs*δ*g*s := by
    rw [norm_smul (W i) (fderiv ℝ (wrappedSelector M i) x),Real.norm_eq_abs]
    calc
      _ ≤ (δ*(M.ell*M.width^2))*((Cs/M.width)*s) :=
        mul_le_mul hW hs (norm_nonneg _) (by positivity)
      _ = _ := by dsimp only [g];field_simp;ring
  have hn := norm_add_le ((Q i-1) • fderiv ℝ (wrappedResidual M i) x)
    (W i • fderiv ℝ (wrappedSelector M i) x)
  change ‖(Q i-1) • fderiv ℝ (wrappedResidual M i) x+
    W i • fderiv ℝ (wrappedSelector M i) x‖ ≤ (Cr+Cs)*g*((1-Q i)+δ)*s
  have hextra : 0 ≤ Cr*δ*g*s+Cs*(1-Q i)*g*s := by positivity
  nlinarith only [hn,h₁,h₂,hextra]

theorem attachment_stop_or_descend (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ) (x : E)
    {Cs Cr δ : ℝ} (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ releaseTolerance (Cr+Cs))
    (hell : 0 ≤ M.ell) (hh : 0 < M.width) (hR : 0 < M.radius)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1)
    (hs : ∀ i, ‖fderiv ℝ (wrappedSelector M i) x‖ ≤ (Cs/M.width)*Real.sqrt (wrappedSelector M i x))
    (hr : ∀ i, ‖fderiv ℝ (wrappedResidual M i) x‖ ≤ Cr*(M.ell*M.width)*Real.sqrt (wrappedSelector M i x))
    (hW : ∀ i, |W i| ≤ δ*(M.ell*M.width^2))
    (hmacro : (M.ell*M.width)/2 ≤ ‖fderiv ℝ (macroValue M.n M.ell M.width ν M.radius M.frame) x‖) :
    (M.ell*M.width)/4 ≤ ‖fderiv ℝ (attachment M ν Q W) x‖ ∨
      ∃ i : Fin (M.n+1), descentThreshold (Cr+Cs) < wrappedSelector M i x ∧ Q i < 1 := by
  classical
  have hg : 0 ≤ M.ell*M.width := mul_nonneg hell hh.le
  have hC : 0 ≤ Cr+Cs := add_nonneg hCr hCs
  by_cases hex : ∃ i, wrappedSelector M i x ≠ 0
  · obtain ⟨i,hi⟩ := hex
    have hψ := wrappedSelector_range M i x
    by_cases hstop : wrappedSelector M i x ≤ descentThreshold (Cr+Cs) ∨
        1-releaseTolerance (Cr+Cs) ≤ Q i
    · left
      have hp := outerPerturbation_norm_bound M Q W x hCs hCr hδ hell hh i hi (hQ i) (hs i) (hr i) (hW i)
      have hfactor := small_perturbation_factor hC hδ hδsmall (hQ i).1 (hQ i).2 hψ.1 hψ.2 hstop
      have hpert : ‖outerPerturbation M Q W x‖ ≤ (M.ell*M.width)/4 := by
        have hmul := mul_le_mul_of_nonneg_left hfactor hg
        nlinarith only [hp,hmul]
      have htri := norm_sub_le
        (fderiv ℝ (macroValue M.n M.ell M.width ν M.radius M.frame) x+outerPerturbation M Q W x)
        (outerPerturbation M Q W x)
      rw [add_sub_cancel_right] at htri
      rw [attachment_fderiv M ν Q W hR x]
      nlinarith only [hmacro,htri,hpert]
    · right
      push_neg at hstop
      refine ⟨i,hstop.1,?_⟩
      have ht := (descentThreshold_range hC).2.2
      linarith only [hstop.2,ht]
  · left
    have hi : ∀ i, wrappedSelector M i x = 0 := by simpa using hex
    rw [attachment_fderiv M ν Q W hR x,outerPerturbation_zero M Q W x hi,add_zero]
    linarith only [hmacro,hg]

end Bilevel.ChiOuter
