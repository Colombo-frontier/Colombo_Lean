import Bilevel.ChiFineInactiveLocality
import Bilevel.ChiFineCoupling

/-! The actual fixed deepest-frontier difference R-R_tau. Its value keeps
the small flattening scale; all positive jets have the exact signal scales. -/
noncomputable section
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainResidualBounds

def signalResidual (n : ℕ) (ℓ β τ : ℝ) (z : Space n) : ℝ :=
  frontier n ℓ β z-flatFrontier n ℓ β τ z

theorem signalResidual_contDiff (n : ℕ) (ℓ β τ : ℝ) : ContDiff ℝ 3 (signalResidual n ℓ β τ) :=
  (frontier_contDiff n ℓ β).sub (flatFrontier_contDiff n ℓ β τ)

theorem signal_residual_bounds : ∃ B : ℝ,1 ≤ B ∧
    ∀ (n : ℕ) (ℓ β τ : ℝ),0 ≤ ℓ → 0<β → 0<τ → τ ≤ β/16 → ∀ z : Space n,
      |signalResidual n ℓ β τ z| ≤ B*ℓ*β*τ ∧
      ∀ j : Fin 3,‖iteratedFDeriv ℝ (j.val+1) (signalResidual n ℓ β τ) z‖ ≤
        2*B*ℓ*β/τ^j.val := by
  obtain ⟨M,hM,hm⟩ := source_frontier_jet_bounds
  obtain ⟨C,hC,hc⟩ := source_flattening_derivative_bounds
  let E := 2*Real.sqrt (Real.exp 1)
  let B := M+C+E
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hB : 1 ≤ B := by dsimp [B];linarith
  have hMB : M ≤ B := by dsimp [B];linarith
  have hCB : C ≤ B := by dsimp [B];linarith
  have hEB : E ≤ B := by dsimp [B];linarith
  refine ⟨B,hB,fun n ℓ β τ hℓ hβ hτ hs z => ⟨?_,fun j => ?_⟩⟩
  · apply (source_flattening_error n ℓ β τ hℓ hβ hτ z).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hEB hℓ) hβ.le) hτ.le
  · have htβ : τ ≤ β := by linarith
    have ha := hm n (j.val+1) ℓ β (by omega) hℓ hβ z
    have hb := hc n ℓ β τ hℓ hβ hτ hs j z
    have he : M*ℓ*β^2/β^(j.val+1)=M*ℓ*β/β^j.val := by
      rw [pow_succ]
      field_simp
      ring
    rw [he] at ha
    have hupper : M*ℓ*β/β^j.val ≤ B*ℓ*β/τ^j.val := by
      apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ M*ℓ*β)
        (pow_pos hτ _) (pow_le_pow_left₀ hτ.le htβ _)).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMB hℓ) hβ.le) (by positivity)
    have hupper' : C*ℓ*β/τ^j.val ≤ B*ℓ*β/τ^j.val :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB hℓ) hβ.le) (by positivity)
    have hh := jet_sub_norm_le (frontier_contDiff n ℓ β) (flatFrontier_contDiff n ℓ β τ)
      z (j.val+1) (by omega)
    exact hh.trans ((add_le_add (ha.trans hupper) (hb.trans hupper')).trans_eq (by ring))

end Bilevel.ChiFine
