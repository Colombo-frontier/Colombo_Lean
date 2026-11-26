import SecondOrder.CurvatureScales

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def curvatureNoiseBudget (P : Parameters) : ℝ := min P.hessianNoise P.hessianBound

theorem curvatureNoiseBudget_pos (P : Parameters) : 0<curvatureNoiseBudget P :=
  lt_min P.hessianNoise_pos P.hessianBound_pos

/-- Explicit manuscript scales give an admissible rich common scalar loss.
The small-tolerance assumptions below are concrete sufficient inequalities,
with fixed universal constants independent of chain length and dimension. -/
theorem curvatureHardFamily_admissible {m T : ℕ} (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) (P : Parameters) {σ₀ γ : ℝ} (hσ₀ : 0<σ₀) (hγ : 0<γ)
    (hsmall : 64*curvatureNoiseConstant*γ≤curvatureNoiseBudget P)
    (hLip : 8*curvatureGeometryConstant*γ≤P.gradientLip)
    (hgrad : 16*curvatureGeometryConstant*curvatureNoiseBudget P*γ*Real.sqrt ((2*m:ℕ):ℝ)≤
      P.hessianHolder*P.gradientNoise)
    (hvalue : 256*curvatureGeometryConstant^2*((2*m:ℕ):ℝ)*curvatureNoiseBudget P*γ^2≤
      σ₀*P.hessianHolder^2)
    (hgap : curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ*(T+1:ℕ)≤P.gap) :
    RichCommonLoss (curvatureCoefficientLaw Θ (curvatureCoefficientScale (curvatureNoiseBudget P) γ)
      (curvatureCoefficientScale_ge_two hγ hsmall)).toMeasure P σ₀
      (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ)
        (curvatureInputScale P.hessianHolder γ))
      (scaledCurvatureSample Θ (curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ)
        (curvatureInputScale P.hessianHolder γ)) := by
  have hD : (0:ℝ)<(2*m:ℕ) := by exact_mod_cast Nat.mul_pos (by omega) hm
  have hA := curvatureOutputScale_pos hD P.hessianHolder_pos hγ
  have hβ := curvatureInputScale_pos P.hessianHolder_pos hγ
  have hs := curvatureScales_smoothness hD P.hessianHolder_pos hγ
  apply scaledCurvatureRichCommonLoss Θ hm P hA.le hβ.le hσ₀ _ _ hgap
  · rw [hs.1]
    exact hLip
  · rw [hs.2]
    linarith [P.hessianHolder_pos]
  · exact (curvatureScales_value_noise hD P.hessianHolder_pos hγ hsmall).trans
      ((div_le_iff₀ (sq_pos_of_pos P.hessianHolder_pos)).2 hvalue)
  · exact (curvatureScales_gradient_noise hD P.hessianHolder_pos hγ hsmall).trans
      ((div_le_iff₀ P.hessianHolder_pos).2 (by nlinarith only [hgrad]))
  · exact curvatureScales_hessian_noise hD P.hessianHolder_pos hγ hsmall

/-- The parameter T in our chain counts links; the manuscript counts blocks. -/
def curvatureBudgetLinks (Δ A : ℝ) : ℕ := ⌊Δ/(2*A)⌋₊-1

theorem curvatureBudgetLinks_count {Δ A : ℝ} (hA : 0<A) (hsize : 2*A≤Δ) :
    curvatureBudgetLinks Δ A+1=⌊Δ/(2*A)⌋₊ := by
  have hn : 0<⌊Δ/(2*A)⌋₊ := Nat.floor_pos.2 ((le_div_iff₀ (by positivity)).2 (by nlinarith only [hsize]))
  unfold curvatureBudgetLinks
  omega

theorem curvatureBudgetLinks_gap {Δ A : ℝ} (hA : 0<A) (hsize : 2*A≤Δ) :
    A*(curvatureBudgetLinks Δ A+1:ℕ)≤Δ/2 := by
  rw [curvatureBudgetLinks_count hA hsize]
  have hΔ : 0≤Δ := by linarith
  have hh := mul_le_mul_of_nonneg_left (Nat.floor_le (div_nonneg hΔ (by positivity : 0≤2*A))) hA.le
  apply hh.trans_eq
  field_simp
  <;> ring

theorem curvatureBudgetLinks_dimension {m : ℕ} (hm : 0<m) {Δ L γ : ℝ}
    (hL : 0<L) (hγ : 0<γ) (hsize : 2*curvatureOutputScale ((2*m:ℕ):ℝ) L γ≤Δ) :
    ((CurvatureDimension m (curvatureBudgetLinks Δ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)) : ℕ):ℝ)≤
      Δ*L^2/(4096*curvatureGeometryConstant^2*γ^3) := by
  have hD : (0:ℝ)<(2*m:ℕ) := by exact_mod_cast Nat.mul_pos (by omega) hm
  have hA := curvatureOutputScale_pos hD hL hγ
  have hg := curvatureBudgetLinks_gap hA hsize
  have hn : ((curvatureBudgetLinks Δ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)+1:ℕ):ℝ)≤
      (Δ/2)/curvatureOutputScale ((2*m:ℕ):ℝ) L γ :=
    (le_div_iff₀ hA).2 (by nlinarith only [hg])
  have hh := mul_le_mul_of_nonneg_right hn hD.le
  unfold CurvatureDimension
  rw [Nat.cast_mul]
  apply hh.trans_eq
  rw [(curvatureScales_identities hD hL hγ).2.2]
  have hm0 : (m:ℝ)≠0 := ne_of_gt (by exact_mod_cast hm)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hm0, ne_of_gt hL, ne_of_gt hγ, ne_of_gt curvatureGeometryConstant_pos]
  <;> ring
  all_goals field_simp [hm0, ne_of_gt hγ, ne_of_gt curvatureGeometryConstant_pos]
  <;> ring

end
end SecondOrder
