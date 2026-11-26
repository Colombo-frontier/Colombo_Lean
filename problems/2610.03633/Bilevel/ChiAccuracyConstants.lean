import Bilevel.ChiAccuracyCalibration

/-! Numerical accuracy constants chosen before every dimension, depth,
public budget and noise level. The source window is nonempty for Δ>0. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem exists_accuracy_constants {A Cb η₀ t η δ γ : ℝ}
    (hA : 0 ≤ A) (hCb : 0 ≤ Cb) (hη₀ : 0 < η₀) (ht : 0 < t) (hη : 0 < η)
    (hδ : 0 < δ) (hγ : 0 < γ) : ∃ Cacc c : ℝ,
      1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧ A ≤ Cacc*t*η^2 ∧
      A*Cb*c ≤ δ*η₀ ∧ 6*A*Cb*c ≤ γ*η₀ := by
  let Cacc := 1+A/(t*η^2)
  let c := min 1 (min (δ*η₀/(A*Cb+1)) (γ*η₀/(6*A*Cb+1)))
  have hAC : 0 ≤ A*Cb := mul_nonneg hA hCb
  have hC : 1 ≤ Cacc := by dsimp [Cacc]; linarith [div_nonneg hA (show 0 ≤ t*η^2 by positivity)]
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hca : c ≤ δ*η₀/(A*Cb+1) := (min_le_right _ _).trans (min_le_left _ _)
  have hcg : c ≤ γ*η₀/(6*A*Cb+1) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Cacc,c,hC,hc,hc1,?_,?_,?_⟩
  · have he : Cacc*t*η^2 = t*η^2+A := by dsimp [Cacc]; field_simp; ring
    rw [he]
    linarith [mul_nonneg ht.le (sq_nonneg η)]
  · have hh := (le_div_iff₀ (show 0 < A*Cb+1 by positivity)).mp hca
    nlinarith only [hh,hc]
  · have hh := (le_div_iff₀ (show 0 < 6*A*Cb+1 by positivity)).mp hcg
    nlinarith only [hh,hc]

theorem exists_uniform_hessian_hidden_budget {A Cb η₀ t η δ γ : ℝ}
    (hA : 0 ≤ A) (hCb : 0 ≤ Cb) (hη₀ : 0 < η₀) (ht : 0 < t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ Cacc c : ℝ,1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ (L κ θ Δ ε : ℝ) (J q : ℕ),0 < L → 1 ≤ κ → 1 ≤ θ →
        ε ≤ accuracyWindow c Cacc L κ θ Δ J q →
        A^(J+1)*((J:ℝ)+1)^q*sourceWidth Cb ε η₀ L t η J ≤ δ ∧
        A^(J+1)*((J:ℝ)+1)^q*sourceWidth Cb ε η₀ L t η J*θ/((κ/6)*η^J) ≤ γ := by
  obtain ⟨Cacc,c,hC,hc,hc1,habs,hsmallδ,hsmallγ⟩ := exists_accuracy_constants hA hCb hη₀ ht hη hδ hγ
  refine ⟨Cacc,c,hC,hc,hc1,?_⟩
  intro L κ θ Δ ε J q hL hκ hθ hε
  have hCp : 0 < Cacc := by linarith
  exact ⟨sourceWidth_hessian_budget hA hCp hCb hη₀ hL ht hη hη1 hc.le hκ hθ hδ.le
      habs hsmallδ J q hε,
    sourceWidth_hidden_ratio hA hCp hCb hη₀ hL ht hη hc.le hκ (by linarith) hγ.le
      habs hsmallγ J q hε⟩

end Bilevel.ChiExtensionCalibration
