import Bilevel.MultiscalePerturbation
import Bilevel.GradientJetBounds

/-! Global O(L) smoothness of the actual revealed upper term. The radial
radius enters through its stated chain-dimension scaling. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open ZeroChain

theorem scaled_gradient_lipschitz (n : ℕ) (a β D : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
    (_hD : 0 ≤ D)
    (hb : ∀ u v : Space n,‖gradient (ZeroChain.value n) u-gradient (ZeroChain.value n) v‖ ≤ D*‖u-v‖)
    (u v : Space n) :
    ‖gradient (ScaledZeroChain.value n a β) u-gradient (ScaledZeroChain.value n a β) v‖ ≤
      (D*a/β^2)*‖u-v‖ := by
  rw [ScaledZeroChain.actual_gradient,ScaledZeroChain.actual_gradient]
  simp only [ScaledZeroChain.gradientField,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ha hβ.le)]
  have hh := hb (β⁻¹ • u) (β⁻¹ • v)
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hβ)] at hh
  calc
    _ ≤ (a/β)*(D*(β⁻¹*‖u-v‖)) := mul_le_mul_of_nonneg_left hh (div_nonneg ha hβ.le)
    _ = _ := by field_simp; ring

theorem actual_upper_smoothness : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n), P.β*Real.sqrt (n+1:ℕ) ≤ P.R → P.ν ≤ P.L →
      ∀ u v : E,‖gradient P.revealed u-gradient P.revealed v‖ ≤ (C*P.L)*‖u-v‖ := by
  obtain ⟨B,hB,hcoord⟩ := ZeroChain.coordinate_gradient_uniform_bound
  obtain ⟨D,hd⟩ := ZeroChainRegularity.gradient_lipschitz_uniform
  obtain ⟨A,hA,hr⟩ := residual_jet_budget
  let C := 1+(D:ℝ)+4*B+A
  have hC : 1 ≤ C := by dsimp [C]; linarith [D.coe_nonneg]
  refine ⟨C,hC,fun E _ _ _ n P hR hν u v => ?_⟩
  have hL := P.L_pos
  have hβ := P.β_pos
  have ha := P.amplitude_nonneg
  have hη := P.η_nonneg
  have hA0 : 0 ≤ A := by linarith
  have hRp : 0 < P.R := P.β_pos.trans_le P.β_le_R
  have he : P.amplitude/P.β = P.η*P.L*P.β := by dsimp [Parameters.amplitude]; field_simp; ring
  have he2 : P.amplitude/P.β^2 = P.η*P.L := by dsimp [Parameters.amplitude]; field_simp
  let G := P.amplitude/P.β*B*Real.sqrt (n+1:ℕ)
  have hG : G ≤ B*P.L*P.R := by
    have hηL : P.η*P.L ≤ P.L := by nlinarith [P.η_le_one]
    have h1 := mul_le_mul_of_nonneg_right hηL
      (show 0 ≤ B*(P.β*Real.sqrt (n+1:ℕ)) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hR (mul_nonneg hB hL.le)
    dsimp [G]
    rw [he]
    nlinarith only [h1,h2]
  have hscale : (D:ℝ)*P.amplitude/P.β^2 ≤ (D:ℝ)*P.L := by
    rw [mul_div_assoc,he2]
    exact mul_le_mul_of_nonneg_left (by nlinarith [P.η_le_one]) D.coe_nonneg
  have hGdiv : 4*G/P.R ≤ 4*B*P.L := (div_le_iff₀ hRp).mpr (by nlinarith only [hG])
  have hH := WrappedChain.gradient_difference_bound n P.amplitude P.β P.ν P.R G
    ((D:ℝ)*P.amplitude/P.β^2) P.ν_nonneg hRp (by positivity)
    (fun z => ScaledZeroChain.gradient_norm_bound n P.amplitude P.β B ha hβ hB (hcoord n) z)
    (scaled_gradient_lipschitz n P.amplitude P.β D ha hβ D.coe_nonneg (fun z w => (hd n).norm_sub_le z w))
    P.U u v
  have hH' : ‖gradient P.outer u-gradient P.outer v‖ ≤ ((D:ℝ)+4*B+1)*P.L*‖u-v‖ := by
    apply hH.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith only [hscale,hGdiv,hν]
  have hres (w : E) : ‖iteratedFDeriv ℝ 2 P.residual w‖ ≤ A*P.L := by
    have hh := hr E n P w 2
    change ‖iteratedFDeriv ℝ 2 P.residual w‖ ≤ A*P.L*P.β^2/P.β^2 at hh
    have hei : A*P.L*P.β^2/P.β^2 = A*P.L := by field_simp
    rwa [hei] at hh
  have hrl := GradientJetBounds.gradient_lipschitz P.residual_contDiff (A*P.L) hres u v
  rw [P.revealed_gradient,P.revealed_gradient]
  have hid : gradient P.outer u-gradient P.residual u-(gradient P.outer v-gradient P.residual v) =
      (gradient P.outer u-gradient P.outer v)-(gradient P.residual u-gradient P.residual v) := by abel
  rw [hid]
  apply (norm_sub_le _ _).trans
  apply (add_le_add hH' hrl).trans_eq
  dsimp [C]
  ring

end Bilevel.MultiscaleMean
