import Bilevel.ChiBoundedChainSourceAmplitude

/-! The source order of fixed numerical choices is feasible for any prescribed
payload amplitude and energy contraction, independently of recursion depth. -/
noncomputable section
namespace Bilevel.ChiRecursive
open ChiBoundedChain

theorem exists_source_small_parameters {A K δ q : ℝ}
    (hA : 0≤A) (hK : 0<K) (hδ : 0<δ) (hq : 0<q) :
    ∃ ζ cn η : ℝ,0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ 0<η ∧ η≤1 ∧
      128≤cn/η^2 ∧ η^2≤q ∧ sourceAmplitudeConstant A K ζ cn η≤δ := by
  have hA1 : 0<A+1 := by linarith
  have hK1 : 0<K+1 := by linarith
  have hG0 := gaussianBound_nonneg
  have hG1 : 0<gaussianBound+1 := by linarith
  let ζ := min (1/15:ℝ) (δ/(36*(A+1)))
  let cn := δ/(4*(gaussianBound+1))
  have hζ : 0<ζ := by dsimp only [ζ];positivity
  have hcn : 0<cn := by dsimp only [cn];positivity
  let η := min (1:ℝ) (min (Real.sqrt (cn/128))
    (min (δ/(12*(A+1))) (min (Real.sqrt (δ*ζ/(8*(A+1)*(K+1)))) (Real.sqrt q))))
  have hη : 0<η := by dsimp only [η];positivity
  have hη1 : η≤1 := min_le_left _ _
  have hηc : η≤Real.sqrt (cn/128) := (min_le_right _ _).trans (min_le_left _ _)
  have hηa : η≤δ/(12*(A+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηk : η≤Real.sqrt (δ*ζ/(8*(A+1)*(K+1))) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηq : η≤Real.sqrt q :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hηcsq : η^2≤cn/128 := by
    have hh := (sq_le_sq₀ hη.le (Real.sqrt_nonneg _)).mpr hηc
    simpa only [Real.sq_sqrt (show 0≤cn/128 by positivity)] using hh
  have hηksq : η^2≤δ*ζ/(8*(A+1)*(K+1)) := by
    have hh := (sq_le_sq₀ hη.le (Real.sqrt_nonneg _)).mpr hηk
    simpa only [Real.sq_sqrt (show 0≤δ*ζ/(8*(A+1)*(K+1)) by positivity)] using hh
  have hηqsq : η^2≤q := by
    have hh := (sq_le_sq₀ hη.le (Real.sqrt_nonneg _)).mpr hηq
    simpa only [Real.sq_sqrt hq.le] using hh
  have hzupper : ζ≤δ/(36*(A+1)) := min_le_right _ _
  have hzscaled := (le_div_iff₀ (show 0<36*(A+1) by positivity)).mp hzupper
  have hascaled := (le_div_iff₀ (show 0<12*(A+1) by positivity)).mp hηa
  have hkscaled := (le_div_iff₀ (show 0<8*(A+1)*(K+1) by positivity)).mp hηksq
  have hceq : 4*(gaussianBound+1)*cn=δ := by dsimp only [cn];field_simp
  have hcterm : gaussianBound*cn≤δ/4 := by nlinarith
  have hzterm : 9*A*ζ≤δ/4 := by nlinarith
  have haterm : 3*A*η≤δ/4 := by nlinarith
  have hkterm : 2*A*K*η^2/ζ≤δ/4 := by
    apply (div_le_iff₀ hζ).mpr
    have hak : A*K≤(A+1)*(K+1) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hak (sq_nonneg η)
    nlinarith only [hkscaled,hh]
  refine ⟨ζ,cn,η,hζ,(min_le_left _ _).trans (by norm_num),hcn,hη,hη1,?_,hηqsq,?_⟩
  · apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
    nlinarith only [hηcsq]
  · unfold sourceAmplitudeConstant
    nlinarith only [hcterm,hzterm,haterm,hkterm]

end Bilevel.ChiRecursive
