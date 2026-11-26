import Bilevel.ChiExtensionLedgerAbsorption
import Bilevel.ChiSourceFineExtension

/-! One uniform choice of the normal, curvature, and accuracy constants
pays the actual coarse/fine/radial ledger shapes. This is numerical
calibration; the analytic bounds are supplied by the scheduled extension
theorems, not postulated by this result. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem exists_uniform_extension_calibration
    {C B P Q R S V Cb η₀ t η δ γ M cms Aextra : ℝ}
    (hC : 1 ≤ C) (hB : 1 ≤ B) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hCb : 0 < Cb) (hη₀ : 0 < η₀)
    (ht : 0 < t) (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 < δ) (hγ : 0 < γ)
    (hM : 1 ≤ M) (_hcms : 0 < cms) (hAextra : 1 ≤ Aextra) :
    ∃ Cf CT Cacc c A : ℝ,1 ≤ Cf ∧ 1 ≤ CT ∧ 1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧
      1 ≤ A ∧ Aextra ≤ A ∧
      2*M*(max 1 (116*SmallGapLiftSupport.C/cms^2)*B^2) ≤ Cf ∧
      ∀ (L μ κ θ Δ ε a : ℝ),0 < L → 0 < μ → 1 ≤ κ → 1 ≤ θ → 0 < ε →
      ε ≤ accuracyWindow c Cacc L κ θ Δ (ChiIndependentWidths.chosenDepth θ) 6 →
      1 ≤ ChiIndependentWidths.chosenDepth θ → 0 < a → a ≤ ChiCurvatureSchedule.scale θ CT 6 →
      let J := ChiIndependentWidths.chosenDepth θ
      let b := sourceWidth Cb ε η₀ L t η J
      1 ≤ fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J ∧
      P*C^(J+2)*((J:ℝ)+1)^2*b+Q*B^(J+2)*b+R*((J:ℝ)+1)^2*b ≤ δ ∧
      (S*C^(J+2)+V)*((J:ℝ)+1)^2*ChiCurvatureSchedule.scale θ CT 6+
        2*θ/(3*(2*M)) ≤ 2*θ/(3*M) ∧
      A^(J+1)*((J:ℝ)+1)^6*b*θ/((κ/6)*η^J) ≤ γ := by
  let Cf := max 1 (2*M*(max 1 (116*SmallGapLiftSupport.C/cms^2)*B^2))
  let A₂ := max 1 (P+Q+R)*(C+B)^2
  let A₃ := max 1 (S+V)*(C+1)^2
  let A := A₂+Aextra
  let CT := max 1 (max (3*M*A₃) (max 1 (12*η₀)*Cf))
  have hCf : 1 ≤ Cf := le_max_left _ _
  have hCT : 1 ≤ CT := le_max_left _ _
  have hA₂ : 1 ≤ A₂ := three_coefficients_constant_ge_one hC hB
  have hA : 1 ≤ A := by dsimp only [A]; linarith
  have hA₂A : A₂ ≤ A := by dsimp only [A]; linarith
  have hAextraA : Aextra ≤ A := by dsimp only [A]; linarith
  have hCTp : 0 < CT := by linarith
  have hCTthird : 3*M*A₃ ≤ CT := (le_max_left _ _).trans (le_max_right _ _)
  have hCTfine : max 1 (12*η₀)*Cf ≤ CT := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Cacc,c,hCacc,hc,hc1,haccuracy⟩ := exists_uniform_hessian_hidden_budget
    (show 0 ≤ A by linarith) hCb.le hη₀ ht hη hη1 hδ hγ
  refine ⟨Cf,CT,Cacc,c,A,hCf,hCT,hCacc,hc,hc1,hA,hAextraA,le_max_right _ _,?_⟩
  intro L μ κ θ Δ ε a hL hμ hκ hθ hε hwindow hJ ha haT
  dsimp only
  let J := ChiIndependentWidths.chosenDepth θ
  let b := sourceWidth Cb ε η₀ L t η J
  have hb : 0 < b := sourceWidth_pos hCb hε hη₀ hL ht hη J
  have hac := haccuracy L κ θ Δ ε J 6 hL hκ hθ hwindow
  have hsecond := source_extension_second_absorption hP hQ hR hC hB hb.le J
  have hpow : A₂^(J+1) ≤ A^(J+1) := pow_le_pow_left₀ (by linarith) hA₂A _
  have hdepth : ((J:ℝ)+1)^2 ≤ ((J:ℝ)+1)^6 :=
    pow_le_pow_right₀ (by have := Nat.cast_nonneg (α:=ℝ) J; linarith) (by norm_num)
  have hsecond' : A₂^(J+1)*((J:ℝ)+1)^2*b ≤ A^(J+1)*((J:ℝ)+1)^6*b :=
    mul_le_mul_of_nonneg_right (mul_le_mul hpow hdepth (sq_nonneg _) (by positivity)) hb.le
  have hthird := source_extension_third_absorption hS hV hC (show 0 ≤ θ by linarith)
    (show 1 ≤ 3*M by linarith) hCTp hCTthird 6 (by norm_num)
  refine ⟨fineParameter_ge_one (by linarith) hμ hL hη₀ ha hCf hCTp hCTfine 6 (by norm_num) hJ haT,
    hsecond.trans (hsecond'.trans hac.1),?_,hac.2⟩
  have hm : 0 < M := by linarith
  have he : θ/(3*M)+2*θ/(3*(2*M)) = 2*θ/(3*M) := by field_simp; ring
  exact (add_le_add_right hthird _).trans_eq he

end Bilevel.ChiExtensionCalibration
