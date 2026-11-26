import Bilevel.ChiCoarseSourceScales

/-! Finite coarse extension ledger at the actual curvature and floor
schedule. The geometric energy sum has no factor equal to the depth. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtensionCalibration
open ChiCurvatureSchedule

theorem geometric_square_sum_le_two {η : ℝ} (_hη : 0 ≤ η) (hsmall : η^2 ≤ 1/2) (J : ℕ) :
    ∑ i : Fin J,η^(2*i.val) ≤ 2 := by
  have he : (∑ i ∈ Finset.range J,(η^2)^i)*(1-η^2) = 1-(η^2)^J := geom_sum_mul_neg (η^2) J
  have hs : 0 ≤ ∑ i ∈ Finset.range J,(η^2)^i := Finset.sum_nonneg (fun i _ => pow_nonneg (sq_nonneg η) i)
  have hp := pow_nonneg (sq_nonneg η) J
  have hm := mul_le_mul_of_nonneg_left hsmall hs
  have hbound : ∑ i ∈ Finset.range J,(η^2)^i ≤ 2 := by nlinarith
  rw [← Fin.sum_univ_eq_sum_range] at hbound
  simpa only [← pow_mul] using hbound

theorem coarse_scheduled_sums {cn η T L η₀ b κ P : ℝ}
    (hcn : 0 ≤ cn) (hη : 0 < η) (hη1 : η ≤ 1) (hηsq : η^2 ≤ 1/2)
    (hT : 1 ≤ T) (hTκ : T ≤ κ) (hL : 0 < L) (hη₀ : 0 ≤ η₀) (hb : 0 ≤ b)
    (hκ : 1 ≤ κ) (hP : 0 ≤ P) (hlen : 128 ≤ cn/η^2) (J : ℕ) :
    let N := fun i : Fin J => (length cn η T i.val:ℝ)
    let ell := fun i : Fin J => η₀*L*curvature T (i.val+1)
    let h := fun i : Fin J => η^(i.val+1)*b/((κ/6)*curvature T (i.val+1))
    (∑ i : Fin J,2*P*N i*ell i*(h i)^2/normalCoefficient L J) ≤
      16*P*cn*η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 ∧
    (∑ i : Fin J,4*P*ell i*h i*((N i)^(1/3:ℝ))^2/normalCoefficient L J) ≤
      192*P*η₀*b*(cn/η^2)*((J:ℝ)+1)^2 ∧
    (∑ i : Fin J,8*P*ell i*(N i)^(1/3:ℝ)/normalCoefficient L J) ≤
      64*P*η₀*(cn/η^2)^(1/3:ℝ)*((J:ℝ)+1)^2*T := by
  dsimp only
  have hκp : 0 < κ := by linarith
  have hs := sqrt_two_depth_le J
  have hJ0 : (0:ℝ) ≤ J := Nat.cast_nonneg _
  have hJJ : (J:ℝ)*((J:ℝ)+1) ≤ ((J:ℝ)+1)^2 := by nlinarith
  constructor
  · have hterm (i : Fin J) := mul_le_mul_of_nonneg_left
      (high_coarse_energy_scale hcn hη hT hL hη₀ hb (show 0 < κ/6 by positivity) J i.val)
      (show 0 ≤ 2*P by positivity)
    have hsum : (∑ i : Fin J,2*P*(length cn η T i.val:ℝ)*(η₀*L*curvature T (i.val+1))*
        (η^(i.val+1)*b/((κ/6)*curvature T (i.val+1)))^2/normalCoefficient L J) ≤
        (8*P*cn*η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2)*(∑ i : Fin J,η^(2*i.val)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      convert hterm i using 1 <;> ring
    have hm := mul_le_mul_of_nonneg_left (geometric_square_sum_le_two hη.le hηsq J)
      (show 0 ≤ 8*P*cn*η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 by positivity)
    apply hsum.trans
    convert hm using 1
    ring
  constructor
  · have hterm (i : Fin J) := mul_le_mul_of_nonneg_left
      (high_coarse_second_scale hcn hη hη1 hT hTκ hL hη₀ hb hκ hlen J i.val)
      (show 0 ≤ 4*P by positivity)
    have hsum : (∑ i : Fin J,4*P*(η₀*L*curvature T (i.val+1))*
        (η^(i.val+1)*b/((κ/6)*curvature T (i.val+1)))*((length cn η T i.val:ℝ)^(1/3:ℝ))^2/normalCoefficient L J) ≤
        (J:ℝ)*(96*P*η₀*b*Real.sqrt (2*(J:ℝ))*(cn/η^2)) := by
      calc
        _ ≤ ∑ _ : Fin J,96*P*η₀*b*Real.sqrt (2*(J:ℝ))*(cn/η^2) := by
          apply Finset.sum_le_sum
          intro i _
          convert hterm i using 1 <;> ring
        _ = _ := by simp
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 96*P*η₀*b*(cn/η^2)*(J:ℝ) by positivity)
    have hm' := mul_le_mul_of_nonneg_left hJJ (show 0 ≤ 192*P*η₀*b*(cn/η^2) by positivity)
    nlinarith only [hsum,hm,hm']
  · have hterm (i : Fin J) := mul_le_mul_of_nonneg_left
      (high_coarse_third_scale (η:=η) hcn (show 0 < T by linarith) hL hη₀ J i.val)
      (show 0 ≤ 8*P by positivity)
    have hsum : (∑ i : Fin J,8*P*(η₀*L*curvature T (i.val+1))*(length cn η T i.val:ℝ)^(1/3:ℝ)/normalCoefficient L J) ≤
        (J:ℝ)*(32*P*η₀*Real.sqrt (2*(J:ℝ))*(cn/η^2)^(1/3:ℝ)*T) := by
      calc
        _ ≤ ∑ _ : Fin J,32*P*η₀*Real.sqrt (2*(J:ℝ))*(cn/η^2)^(1/3:ℝ)*T := by
          apply Finset.sum_le_sum
          intro i _
          convert hterm i using 1 <;> ring
        _ = _ := by simp
    have hm := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 32*P*η₀*(cn/η^2)^(1/3:ℝ)*T*(J:ℝ) by positivity)
    have hm' := mul_le_mul_of_nonneg_left hJJ
      (show 0 ≤ 64*P*η₀*(cn/η^2)^(1/3:ℝ)*T by positivity)
    nlinarith only [hsum,hm,hm']

end Bilevel.ChiExtensionCalibration
