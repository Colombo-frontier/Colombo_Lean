import Bilevel.PolishedLiteralAttachment
import Bilevel.PolishedLiteralSelectorSquareRoot
import Bilevel.ChiRecursiveDescent

/-! Actual outer stop-or-descend. The sole base-gradient premise is supplied
by the independently constructed one-sided macro endgame. -/
noncomputable section
namespace Bilevel.PolishedLiteral
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

/-- The original selectors are bounded by exp(1).  The numerical control
constant retains this factor rather than treating the profile as capped. -/
def literalControl (C : ℝ) : ℝ := C*(Real.sqrt (Real.exp 1)+1)

theorem literalControl_bounds {C : ℝ} (hC : 0≤C) :
    0≤literalControl C ∧ C≤literalControl C ∧
      C*Real.sqrt (Real.exp 1)≤literalControl C := by
  unfold literalControl
  have hs := Real.sqrt_nonneg (Real.exp 1)
  constructor
  · positivity
  constructor <;> nlinarith [mul_nonneg hC hs]

theorem literal_small_perturbation_factor {C δ Q ψ : ℝ} (hC : 0≤C) (hδ : 0≤δ)
    (hδsmall : δ≤releaseTolerance (literalControl C))
    (hQ0 : 0≤Q) (hQ1 : Q≤1) (hψ1 : ψ≤Real.exp 1)
    (hstop : ψ≤descentThreshold (literalControl C) ∨
      1-releaseTolerance (literalControl C)≤Q) :
    C*((1-Q)+δ)*Real.sqrt ψ≤1/4 := by
  let B := literalControl C
  have hB := (literalControl_bounds hC).1
  have hCB := (literalControl_bounds hC).2.1
  have hCs := (literalControl_bounds hC).2.2
  have hc : 0<B+1 := by dsimp only [B];linarith
  have hdpos : 0<16*(B+1) := by positivity
  have hδ1 : δ≤1 := hδsmall.trans ((div_le_one hdpos).mpr (by linarith))
  have hs0 := Real.sqrt_nonneg ψ
  have hs1 : Real.sqrt ψ≤Real.sqrt (Real.exp 1) := Real.sqrt_le_sqrt hψ1
  have hfac : 0≤(1-Q)+δ := by linarith
  rcases hstop with hstop|hstop
  · have hs : Real.sqrt ψ≤1/(8*(B+1)) := by
      change ψ≤descentThreshold B at hstop
      have hh := Real.sqrt_le_sqrt hstop
      simpa only [descentThreshold,Real.sqrt_sq (show 0≤1/(8*(B+1)) by positivity)] using hh
    have hfac2 : (1-Q)+δ≤2 := by linarith
    have hh : C*((1-Q)+δ)*Real.sqrt ψ≤2*B*(1/(8*(B+1))) := by
      have hbc := mul_le_mul_of_nonneg_right hCB hfac
      have hh' := mul_le_mul (mul_le_mul_of_nonneg_left hfac2 hB) hs hs0 (show 0≤B*2 by positivity)
      have hb' := mul_le_mul_of_nonneg_right hbc hs0
      nlinarith only [hh',hb']
    apply hh.trans
    rw [mul_one_div]
    apply (div_le_iff₀ (show 0<8*(B+1) by positivity)).mpr
    linarith
  · have hsmall : (1-Q)+δ≤2*releaseTolerance B := by linarith
    have ht : 0≤releaseTolerance B := by unfold releaseTolerance;positivity
    have hh : C*((1-Q)+δ)*Real.sqrt ψ≤2*B*releaseTolerance B := by
      have hf := mul_le_mul_of_nonneg_left hsmall hC
      have hs := mul_le_mul hf hs1 hs0 (show 0≤C*(2*releaseTolerance B) by positivity)
      have hb := mul_le_mul_of_nonneg_right hCs (show 0≤2*releaseTolerance B by positivity)
      nlinarith only [hs,hb]
    apply hh.trans
    unfold releaseTolerance
    calc
      _ = (2*B)/(16*(B+1)) := by ring
      _ ≤ 1/4 := (div_le_iff₀ hdpos).mpr (by linarith)

theorem attachment_stop_or_descend (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ) (x : E)
    {Cs Cr δ : ℝ} (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ releaseTolerance (literalControl (Cr+Cs)))
    (hell : 0 ≤ M.ell) (hh : 0 < M.width) (hR : 0 < M.radius)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1)
    (hs : ∀ i, ‖fderiv ℝ (wrappedSelector M i) x‖ ≤ (Cs/M.width)*Real.sqrt (wrappedSelector M i x))
    (hr : ∀ i, ‖fderiv ℝ (wrappedResidual M i) x‖ ≤ Cr*(M.ell*M.width)*Real.sqrt (wrappedSelector M i x))
    (hW : ∀ i, |W i| ≤ δ*(M.ell*M.width^2))
    (hmacro : (M.ell*M.width)/2 ≤ ‖fderiv ℝ (macroValue M.n M.ell M.width ν M.radius M.frame) x‖) :
    (M.ell*M.width)/4 ≤ ‖fderiv ℝ (attachment M ν Q W) x‖ ∨
      ∃ i : Fin (M.n+1), descentThreshold (literalControl (Cr+Cs)) < wrappedSelector M i x ∧ Q i < 1 := by
  classical
  have hg : 0 ≤ M.ell*M.width := mul_nonneg hell hh.le
  have hC : 0 ≤ Cr+Cs := add_nonneg hCr hCs
  by_cases hex : ∃ i, wrappedSelector M i x ≠ 0
  · obtain ⟨i,hi⟩ := hex
    have hψ := wrappedSelector_range M i x
    by_cases hstop : wrappedSelector M i x ≤ descentThreshold (literalControl (Cr+Cs)) ∨
        1-releaseTolerance (literalControl (Cr+Cs)) ≤ Q i
    · left
      have hp := outerPerturbation_norm_bound M Q W x hCs hCr hδ hell hh i hi (hQ i) (hs i) (hr i) (hW i)
      have hfactor := literal_small_perturbation_factor hC hδ hδsmall (hQ i).1 (hQ i).2 hψ.2 hstop
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
      have ht := (descentThreshold_range (literalControl_bounds hC).1).2.2
      linarith only [hstop.2,ht]
  · left
    have hi : ∀ i, wrappedSelector M i x = 0 := by simpa using hex
    rw [attachment_fderiv M ν Q W hR x,outerPerturbation_zero M Q W x hi,add_zero]
    linarith only [hmacro,hg]

end Bilevel.PolishedLiteral
