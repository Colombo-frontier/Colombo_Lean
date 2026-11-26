import FullJet.UpperParameters

namespace FullJet

theorem failure_fraction_quarter (A S M D s U R N Δ ε : ℝ)
    (hS : 0 < S) (hA : 64 * S ≤ A) (hM : S ≤ M) (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hsum : D + s ≤ S) (hU : 0 < U) (hR : 0 < R) (hN : 0 < N) (hε : 0 < ε)
    (hwork : Δ ≤ N * S * U) (hradius : 32 * M * R ≤ ε) :
    (Δ + N * ((s + D) * U)) / (A * U * N) + (2 / ε) * (s * R) ≤ 1 / 4 := by
  have hAp : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hden : 0 < A * U * N := by positivity
  have hNSU : 0 ≤ N * S * U := by positivity
  have hvar := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show s + D ≤ S by linarith) hN.le) hU.le
  have hnum : Δ + N * ((s + D) * U) ≤ 2 * N * S * U := by nlinarith
  have hdenbound := mul_le_mul_of_nonneg_right hA (mul_nonneg hU.le hN.le)
  have hboundary : (Δ + N * ((s + D) * U)) / (A * U * N) ≤ 1 / 16 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hnum, hdenbound, hNSU]
  have hsmall : s ≤ M := by linarith
  have hnoise' := mul_le_mul_of_nonneg_right hsmall hR.le
  have hnoise : (2 / ε) * (s * R) ≤ 1 / 16 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hε).mpr
    nlinarith only [hnoise', hradius]
  linarith

theorem upperRadius_stationarity (p : ℕ) (hp : 0 < p) (L ε : ℝ) (m B : ℕ)
    (hL : 0 < L) (hε : 0 < ε) :
    (L + upperModelScale p L m B / (p.factorial : ℝ) + higherErrorCoefficient p L m) *
      upperRadius p L ε m B ^ p ≤ ε / 2 := by
  have hM := upperModelScale_pos p L m B hL
  have hr := upperRadius_pos p L ε m B hL hε
  have hS := upperModelScale_ge_errorScale p L m B hL
  have hs := gradientNoiseCoefficient_nonneg p L m B hL.le
  have hP : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.factorial_pos p
  have hdiv := div_le_self hM.le hP
  have hcoef : L + upperModelScale p L m B / (p.factorial : ℝ) + higherErrorCoefficient p L m ≤
      2 * upperModelScale p L m B := by
    unfold upperErrorScale at hS
    linarith
  have hbound := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr.le p)
  have heq := upperRadius_equation p hp L ε m B hL hε
  nlinarith

abbrev UpperSeed (p : ℕ) (Δ L ε : ℝ) (m B n : ℕ) :=
  RandomEpochSeed (upperEpochCount p Δ L ε m B) m B n

noncomputable def upperSeedLaw (p : ℕ) (Δ L ε : ℝ) (m B n : ℕ)
    (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hm : 0 < m) (hn : 0 < n) :
    PMF (UpperSeed p Δ L ε m B n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty (Fin (upperEpochCount p Δ L ε m B)) :=
    ⟨⟨0, upperEpochCount_pos p Δ L ε m B hΔ hL hε hm⟩⟩
  exact PMF.uniformOfFintype _

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n : ℕ}

noncomputable def upperCandidate (hp : 1 ≤ p) (f : Fin n → E → ℝ) (Δ L ε : ℝ) (m B : ℕ)
    (hL : 0 < L) (hε : 0 < ε) (seed : UpperSeed p Δ L ε m B n) : E :=
  multiEpochOutput hp f (upperModelScale p L m B) (upperRadius p L ε m B)
    (upperRadius_pos p L ε m B hL hε).le seed

/-- Fully specified regularization, radius, and number of periods give an
actual candidate with failure probability at most 1/4. This is a finite
macro-algorithm guarantee; its individual oracle calls are counted separately. -/
theorem Admissible.upperCandidate_failure_quarter {f : Fin n → E → ℝ} {Δ L ε : ℝ}
    (hf : Admissible p n Δ L f) (hp : 2 ≤ p) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε)
    (m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    ((upperSeedLaw p Δ L ε m B n hΔ hL hε hm hf.n_pos).toOuterMeasure
      {seed | ε < ‖fderiv ℝ (average f) (upperCandidate (by omega) f Δ L ε m B hL hε seed)‖}).toReal ≤ 1 / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  let M := upperModelScale (k + 2) L m B
  let r := upperRadius (k + 2) L ε m B
  let H := upperEpochCount (k + 2) Δ L ε m B
  let S := upperErrorScale (k + 2) L m B
  let D := higherErrorCoefficient (k + 2) L m
  let s := gradientNoiseCoefficient (k + 2) L m B
  let A := M / ((k + 2 + 1).factorial : ℝ) - L
  let U := r ^ (k + 2 + 1)
  let R := r ^ (k + 2)
  let N := (H : ℝ) * m
  have hMp : 0 < M := upperModelScale_pos (k + 2) L m B hL
  have hrp : 0 < r := upperRadius_pos (k + 2) L ε m B hL hε
  have hHp : 0 < H := upperEpochCount_pos (k + 2) Δ L ε m B hΔ hL hε hm
  have hSp : 0 < S := upperErrorScale_pos (k + 2) L m B hL
  have hA : 64 * S ≤ A := upperModelScale_descent (k + 2) L m B hL
  have hAp : 0 < A := lt_of_lt_of_le (by positivity) hA
  letI : Nonempty (Fin n) := ⟨⟨0, hf.n_pos⟩⟩
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty (Fin H) := ⟨⟨0, hHp⟩⟩
  change ((PMF.uniformOfFintype (RandomEpochSeed H m B n)).toOuterMeasure
    {seed | ε < ‖fderiv ℝ (average f) (multiEpochOutput (p := k + 2) (by omega) f M r hrp.le seed)‖}).toReal ≤ _
  have hdet : (L + M / ((k + 2).factorial : ℝ) + ((k + 2 : ℕ) : ℝ) * L * (m : ℝ) ^ (k + 2 - 1)) *
      r ^ (k + 2) ≤ ε / 2 := upperRadius_stationarity (k + 2) (by omega) L ε m B hL hε
  apply (hf.multiEpoch_failure_bound (H := H) hB hL.le hm hHp M r ε hMp.le hrp hε hAp hdet).trans
  change (Δ + N * (r * epochNoiseBound (k + 2) L m r B + D * U)) / (A * U * N) +
    (2 / ε) * epochNoiseBound (k + 2) L m r B ≤ _
  have hη : epochNoiseBound (k + 2) L m r B = s * R := epochNoiseBound_factor (k + 2) (by omega) L m r B
  have hpow : r * R = U := by dsimp only [R, U]; rw [pow_succ]; ring
  have he : r * (s * R) + D * U = (s + D) * U := by rw [← hpow]; ring
  rw [hη, he]
  apply failure_fraction_quarter A S M D s U R N Δ ε hSp hA
    (upperModelScale_ge_errorScale (k + 2) L m B hL)
    (higherErrorCoefficient_nonneg (k + 2) L m hL.le)
    (gradientNoiseCoefficient_nonneg (k + 2) L m B hL.le)
  · dsimp only [S, D, s, upperErrorScale]
    linarith
  · exact pow_pos hrp _
  · exact pow_pos hrp _
  · exact mul_pos (by exact_mod_cast hHp) (by exact_mod_cast hm)
  · exact hε
  · exact upperEpochCount_work (k + 2) Δ L ε m B hL hε hm
  · exact (upperRadius_equation (k + 2) (by omega) L ε m B hL hε).le

end FullJet
