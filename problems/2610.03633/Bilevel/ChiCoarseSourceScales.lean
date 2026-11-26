import Bilevel.ChiSourcePhysicalScales
import Bilevel.ChiExtensionCalibration
import Bilevel.ChiCoarseArithmetic

/-! Actual floor chain lengths and physical scales in the coarse normal
ledger. The estimates retain the actual floor rather than replacing the
construction by an assumed chain length. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiCurvatureSchedule ChiRecursive

theorem length_le_ratio {cn η T : ℝ} (hcn : 0 ≤ cn) (hT : 1 ≤ T) (j : ℕ) :
    (length cn η T j:ℝ) ≤ (cn/η^2)*T := by
  have hb := length_upper (η:=η) hcn (by linarith : 0 < T) j
  have hr := sourceRatio_le hT (j+1)
  have hh := mul_le_mul_of_nonneg_left hr (div_nonneg hcn (sq_nonneg η))
  change (cn/η^2)*(curvature T (j+1)/curvature T j) ≤ _ at hh
  apply hb.trans
  convert hh using 1
  ring

theorem cube_square_le {N : ℝ} (hN : 1 ≤ N) : (N^(1/3:ℝ))^2 ≤ N := by
  obtain ⟨ha,hcube,_⟩ := ChiCoarse.cube_width_properties hN
  have hm := mul_le_mul_of_nonneg_left ha (sq_nonneg (N^(1/3:ℝ)))
  nlinarith only [hm,hcube]

theorem high_coarse_third_scale {cn η T L η₀ : ℝ}
    (hcn : 0 ≤ cn) (hT : 0 < T) (hL : 0 < L) (hη₀ : 0 ≤ η₀) (J j : ℕ) :
    (η₀*L*curvature T (j+1))/normalCoefficient L J *
      (length cn η T j:ℝ)^(1/3:ℝ) ≤
      4*η₀*Real.sqrt (2*(J:ℝ))*(cn/η^2)^(1/3:ℝ)*T := by
  rw [normalCoefficient_ratio hL]
  have hh := mul_le_mul_of_nonneg_left (weighted_length_bound (η:=η) hcn hT j)
    (show 0 ≤ 4*η₀*Real.sqrt (2*(J:ℝ)) by positivity)
  convert hh using 1 <;> ring

theorem high_coarse_second_scale {cn η T L η₀ b κ : ℝ}
    (hcn : 0 ≤ cn) (hη : 0 < η) (hη1 : η ≤ 1) (hT : 1 ≤ T) (hTκ : T ≤ κ)
    (hL : 0 < L) (hη₀ : 0 ≤ η₀) (hb : 0 ≤ b) (hκ : 1 ≤ κ)
    (hlen : 128 ≤ cn/η^2) (J j : ℕ) :
    ((η₀*L*curvature T (j+1))*(η^(j+1)*b/((κ/6)*curvature T (j+1))))/
      normalCoefficient L J*((length cn η T j:ℝ)^(1/3:ℝ))^2 ≤
      24*η₀*b*Real.sqrt (2*(J:ℝ))*(cn/η^2) := by
  have hκp : 0 < κ := by linarith
  have hTp : 0 < T := by linarith
  have ha := (curvature_pos hTp (j+1)).ne'
  have he : ((η₀*L*curvature T (j+1))*(η^(j+1)*b/((κ/6)*curvature T (j+1))))/
      normalCoefficient L J = 24*η₀*b*Real.sqrt (2*(J:ℝ))*η^(j+1)/κ := by
    unfold normalCoefficient
    field_simp
    ring
  rw [he]
  have hN : 1 ≤ (length cn η T j:ℝ) := by
    exact_mod_cast (show 1 ≤ length cn η T j from (by norm_num : 1 ≤ 128).trans (length_large hcn hT hlen j))
  have hlenκ := (length_le_ratio hcn hT j).trans
    (mul_le_mul_of_nonneg_left hTκ (div_nonneg hcn (sq_nonneg η)))
  have hroot := (cube_square_le hN).trans hlenκ
  have hp := pow_le_one₀ hη.le hη1 (n:=j+1)
  have hprod := mul_le_mul hp hroot (sq_nonneg _) zero_le_one
  have hmul := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 24*η₀*b*Real.sqrt (2*(J:ℝ))/κ by positivity)
  convert hmul using 1
  · ring
  · field_simp
    ring

theorem high_coarse_energy_scale {cn η T L η₀ b K : ℝ}
    (hcn : 0 ≤ cn) (hη : 0 < η) (hT : 1 ≤ T) (hL : 0 < L)
    (hη₀ : 0 ≤ η₀) (_hb : 0 ≤ b) (hK : 0 < K) (J j : ℕ) :
    (length cn η T j:ℝ)*(η₀*L*curvature T (j+1))*
      (η^(j+1)*b/(K*curvature T (j+1)))^2/normalCoefficient L J ≤
      4*cn*η₀*Real.sqrt (2*(J:ℝ))*η^(2*j)*b^2/K^2 := by
  have hTp : 0 < T := by linarith
  have ha := curvature_pos hTp (j+1)
  have ha0 := curvature_pos hTp j
  have hn := length_upper (η:=η) hcn hTp j
  have hmul := mul_le_mul_of_nonneg_right hn
    (show 0 ≤ (η₀*L*curvature T (j+1))*(η^(j+1)*b/(K*curvature T (j+1)))^2 by positivity)
  have he : (cn*(curvature T (j+1)/curvature T j)/η^2)*
      ((η₀*L*curvature T (j+1))*(η^(j+1)*b/(K*curvature T (j+1)))^2) =
      cn*η₀*L*η^(2*j)*b^2/(K^2*curvature T j) := by
    rw [show η^(2*j) = (η^j)^2 by rw [Nat.mul_comm 2 j,pow_mul],pow_succ]
    field_simp
    ring
  rw [he] at hmul
  have hcurv : cn*η₀*L*η^(2*j)*b^2/(K^2*curvature T j) ≤ cn*η₀*L*η^(2*j)*b^2/K^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hK)
    exact le_mul_of_one_le_right (sq_nonneg K) (curvature_bounds hT j).1
  have hd : 0 ≤ normalCoefficient L J := by unfold normalCoefficient; positivity
  have hh := div_le_div_of_nonneg_right (hmul.trans hcurv) hd
  convert hh using 1
  · ring
  · unfold normalCoefficient
    field_simp
    ring

end Bilevel.ChiExtensionCalibration
