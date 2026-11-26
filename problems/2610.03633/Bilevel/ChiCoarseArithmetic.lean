import Bilevel.ChiCurvatureSchedule

/-! The coarse normal width h*N^(1/3) pays each mixed derivative block.
These numerical inequalities will be instantiated with the actual joint
selected-carrier ledger, including macro-variable derivatives. -/
noncomputable section
namespace Bilevel.ChiCoarse

theorem cube_width_properties {N : ℝ} (hN : 1 ≤ N) :
    1 ≤ N^(1/3:ℝ) ∧ (N^(1/3:ℝ))^3=N ∧
      Real.sqrt N ≤ (N^(1/3:ℝ))^2 := by
  have hNp : 0<N := by linarith
  have ha : 1 ≤ N^(1/3:ℝ) := Real.one_le_rpow hN (by norm_num)
  have hcube : (N^(1/3:ℝ))^3=N := by
    rw [← Real.rpow_natCast _ 3,← Real.rpow_mul hNp.le]
    norm_num
  refine ⟨ha,hcube,?_⟩
  have hs := Real.sq_sqrt hNp.le
  have hp := mul_nonneg (show 0 ≤ (N^(1/3:ℝ))^3 by positivity)
    (show 0 ≤ N^(1/3:ℝ)-1 by linarith)
  nlinarith [sq_nonneg (N^(1/3:ℝ)),Real.sqrt_nonneg N]

theorem coarse_second_blocks {N ℓ h M : ℝ} (hN : 1 ≤ N) (hℓ : 0 ≤ ℓ)
    (hh : 0<h) (hM : 0 ≤ M) :
    M*N*ℓ*h^2/(h*N^(1/3:ℝ))+2*(M*ℓ*h*Real.sqrt N)+(M*ℓ)*(h*N^(1/3:ℝ)) ≤
      4*M*ℓ*h*(N^(1/3:ℝ))^2 := by
  obtain ⟨ha,hcube,hs⟩ := cube_width_properties hN
  have hap : 0<N^(1/3:ℝ) := by linarith
  have he : M*N*ℓ*h^2/(h*N^(1/3:ℝ))+2*(M*ℓ*h*Real.sqrt N)+(M*ℓ)*(h*N^(1/3:ℝ))=
      M*ℓ*h*((N^(1/3:ℝ))^2+2*Real.sqrt N+N^(1/3:ℝ)) := by
    nth_rw 1 [← hcube]
    field_simp
    ring
  rw [he]
  have hsmall : (N^(1/3:ℝ))^2+2*Real.sqrt N+N^(1/3:ℝ) ≤ 4*(N^(1/3:ℝ))^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ M*ℓ*h)).trans_eq (by ring)

theorem coarse_third_blocks {N ℓ h M : ℝ} (hN : 1 ≤ N) (hℓ : 0 ≤ ℓ)
    (hh : 0<h) (hM : 0 ≤ M) :
    M*N*ℓ*h^2/(h*N^(1/3:ℝ))^2+3*(M*ℓ*h*Real.sqrt N)/(h*N^(1/3:ℝ))+
      3*(M*ℓ)+(M*ℓ/h)*(h*N^(1/3:ℝ)) ≤ 8*M*ℓ*N^(1/3:ℝ) := by
  obtain ⟨ha,hcube,hs⟩ := cube_width_properties hN
  have hap : 0<N^(1/3:ℝ) := by linarith
  have he : M*N*ℓ*h^2/(h*N^(1/3:ℝ))^2+3*(M*ℓ*h*Real.sqrt N)/(h*N^(1/3:ℝ))+
      3*(M*ℓ)+(M*ℓ/h)*(h*N^(1/3:ℝ))=
      M*ℓ*(2*N^(1/3:ℝ)+3*Real.sqrt N/N^(1/3:ℝ)+3) := by
    nth_rw 1 [← hcube]
    field_simp
    ring
  rw [he]
  have hdiv : Real.sqrt N/N^(1/3:ℝ) ≤ N^(1/3:ℝ) :=
    (div_le_iff₀ hap).mpr (by nlinarith)
  have hsmall : 2*N^(1/3:ℝ)+3*Real.sqrt N/N^(1/3:ℝ)+3 ≤ 8*N^(1/3:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ) ≤ 3)
    rw [← mul_div_assoc] at hm
    linarith
  exact (mul_le_mul_of_nonneg_left hsmall (mul_nonneg hM hℓ)).trans_eq (by ring)

end Bilevel.ChiCoarse
