import Bilevel.ChiCoarseExtension
import Bilevel.GradientJetBounds

/-! Global full-gradient envelope of an actual coarse normal extension.
No bound is imposed on the normal query coordinate. -/
noncomputable section
namespace Bilevel.ChiCoarse
open CompensatedMean SmallGapLiftSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem extension_first_jet {f : E → ℝ} (hf : ContDiff ℝ 3 f) {W A D₁ : ℝ}
    (hW : 0<W) (hA : 0 ≤ A) (hD : 0 ≤ D₁) (y : LowerSpace E)
    (h0 : |f (uProj E y)| ≤ A) (h1 : ‖iteratedFDeriv ℝ 1 f (uProj E y)‖ ≤ D₁) :
    ‖iteratedFDeriv ℝ 1 (extension f W) y‖ ≤ C*(A+D₁*W) := by
  let P := singleData f hf W hW
  let B : ℕ → ℝ := fun k => if k=0 then A else D₁
  have hB (k : ℕ) : 0 ≤ B k := by dsimp [B];split_ifs <;> assumption
  have hb (k : ℕ) (hk : k ≤ 1) : ‖iteratedFDeriv ℝ k f (uProj E y)‖ ≤ B k := by
    interval_cases k
    · simpa only [B,if_pos rfl,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h0
    · simpa only [B,if_neg (by decide : ¬1=0)] using h1
  have hh := P.couplingTerm_jet_bound 0 (by simp [P,singleData]) y 1 (by norm_num) B hB hb
  apply hh.trans_eq
  norm_num [B,Finset.sum_range_succ,P,singleData]
  field_simp
  ring

theorem coarse_first_jet {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {N ℓ h M : ℝ} (hN : 1 ≤ N) (hℓ : 0 ≤ ℓ) (hh : 0<h) (hM : 0 ≤ M)
    (hb : ∀ z,|f z| ≤ M*N*ℓ*h^2 ∧ ‖iteratedFDeriv ℝ 1 f z‖ ≤ M*ℓ*h*Real.sqrt N)
    (y : LowerSpace E) :
    ‖iteratedFDeriv ℝ 1 (extension f (h*N^(1/3:ℝ))) y‖ ≤ 2*C*M*N*ℓ*h^2 := by
  have hNp : 0<N := by linarith
  have hC := C_pos
  obtain ⟨ha,hcube,hs⟩ := cube_width_properties hN
  have hap : 0<N^(1/3:ℝ) := by linarith
  have hprod : Real.sqrt N*N^(1/3:ℝ) ≤ N := by
    have hp := mul_le_mul_of_nonneg_right hs hap.le
    nlinarith
  have ht := extension_first_jet hf (mul_pos hh hap) (by positivity) (by positivity)
    y (hb _).1 (hb _).2
  apply ht.trans
  have he : M*N*ℓ*h^2+(M*ℓ*h*Real.sqrt N)*(h*N^(1/3:ℝ))=
      M*ℓ*h^2*(N+Real.sqrt N*N^(1/3:ℝ)) := by ring
  rw [he]
  have hr := mul_le_mul_of_nonneg_left (show N+Real.sqrt N*N^(1/3:ℝ) ≤ 2*N by linarith)
    (show 0 ≤ C*(M*ℓ*h^2) by positivity)
  convert hr using 1 <;> ring

theorem coarse_gradient_envelope [CompleteSpace E] {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {N ℓ h M : ℝ} (hN : 1 ≤ N) (hℓ : 0 ≤ ℓ) (hh : 0<h) (hM : 0 ≤ M)
    (hb : ∀ z,|f z| ≤ M*N*ℓ*h^2 ∧ ‖iteratedFDeriv ℝ 1 f z‖ ≤ M*ℓ*h*Real.sqrt N)
    (y : LowerSpace E) :
    ‖gradient (extension f (h*N^(1/3:ℝ))) y‖ ≤ 2*C*M*N*ℓ*h^2 := by
  have ht := coarse_first_jet hf hN hℓ hh hM hb y
  rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero,
    ← GradientJetBounds.gradient_norm_eq] at ht
  exact ht

end Bilevel.ChiCoarse
