import NCConcave16991.InnerLoop

/-! # Arithmetic averaging of the actual finite-seed primal trajectory -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.InnerAlgorithm

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- Jensen for a two-point real convex combination, proved by the Hilbert square expansion. -/
theorem convex_combination_square {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (u v : P) : ‖a • u + b • v‖ ^ 2 ≤ a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2 := by
  have hcross : 2 * ⟪u, v⟫_ℝ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have h := sq_nonneg ‖u - v‖
    rw [norm_sub_sq_real] at h
    linarith
  have hc := mul_le_mul_of_nonneg_left hcross (mul_nonneg ha hb)
  calc
    _ = a ^ 2 * ‖u‖ ^ 2 + (a * b) * (2 * ⟪u, v⟫_ℝ) + b ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      ring
    _ ≤ a ^ 2 * ‖u‖ ^ 2 + (a * b) * (‖u‖ ^ 2 + ‖v‖ ^ 2) + b ^ 2 * ‖v‖ ^ 2 := by linarith
    _ = a * (a + b) * ‖u‖ ^ 2 + b * (a + b) * ‖v‖ ^ 2 := by ring
    _ = _ := by rw [hab]; ring

variable {n : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- The running arithmetic average of the first `k` primal coordinates, before each sampled step. -/
def averagedOutput (coordinate : E → P) (G : Fin n → E → E) (regularizer : E → E)
    (anchor : S) (bias : E) (η : ℝ) : (k : ℕ) → Seed n k → P
  | 0, _ => 0
  | k + 1, ω => ((k : ℝ) / (k + 1)) • averagedOutput coordinate G regularizer anchor bias η k ω.1 +
      (1 / ((k : ℝ) + 1)) • coordinate (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω.1)

/-- Exact expectation of the error of the averaged primal iterate. -/
def meanOutputError (coordinate : E → P) (G : Fin n → E → E) (regularizer : E → E)
    (anchor : S) (bias : E) (η : ℝ) (p : P) (k : ℕ) : ℝ :=
  ∫ ω, ‖averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η k ω - p‖ ^ 2 ∂seedLaw k

 theorem averagedOutput_jensen_step (coordinate : E → P) (G : Fin n → E → E)
    (regularizer : E → E) (anchor : S) (bias : E) (η : ℝ) (p : P) (k : ℕ) (ω : Seed n (k + 1)) :
    ‖averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η (k + 1) ω - p‖ ^ 2 ≤
      ((k : ℝ) / (k + 1)) *
        ‖averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η k ω.1 - p‖ ^ 2 +
      (1 / ((k : ℝ) + 1)) *
        ‖coordinate (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω.1) - p‖ ^ 2 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hab : (k : ℝ) / (k + 1) + 1 / ((k : ℝ) + 1) = 1 := by field_simp <;> ring
  have h := convex_combination_square (P := P) (div_nonneg (Nat.cast_nonneg k) hk.le)
    (div_nonneg (by norm_num) hk.le) hab
    (averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η k ω.1 - p)
    (coordinate (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω.1) - p)
  have hid :
      ((k : ℝ) / (k + 1)) • (averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η k ω.1 - p) +
        (1 / ((k : ℝ) + 1)) • (coordinate (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω.1) - p) =
      averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η (k + 1) ω - p := by
    dsimp only [averagedOutput]
    rw [smul_sub, smul_sub]
    have hp : ((k : ℝ) / (k + 1)) • p + (1 / ((k : ℝ) + 1)) • p = p := by
      rw [← add_smul, hab, one_smul]
    calc
      _ = ((k : ℝ) / (k + 1)) • averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η k ω.1 +
          (1 / ((k : ℝ) + 1)) • coordinate (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω.1) -
          (((k : ℝ) / (k + 1)) • p + (1 / ((k : ℝ) + 1)) • p) := by abel
      _ = _ := by rw [hp]
  rw [hid] at h
  exact h

/-- Jensen's inequality is integrated under the actual finite product seed law. -/
theorem meanOutputError_jensen_recursion (coordinate : E → P) (G : Fin n → E → E)
    (regularizer : E → E) (anchor : S) (bias : E) (η : ℝ) (p : P) (k : ℕ) :
    ((k : ℝ) + 1) * meanOutputError S hne hclosed hconvex coordinate G regularizer anchor bias η p (k + 1) ≤
      (k : ℝ) * meanOutputError S hne hclosed hconvex coordinate G regularizer anchor bias η p k +
        meanCost S hne hclosed hconvex G regularizer anchor bias η (fun z ↦ ‖coordinate z - p‖ ^ 2) k := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hp (ω : Seed n k) := averagedOutput_jensen_step S hne hclosed hconvex coordinate G regularizer anchor bias η p k (ω, 0)
  have hi := integral_mono (μ := seedLaw k) Integrable.of_finite Integrable.of_finite hp
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul] at hi
  have hleft : meanOutputError S hne hclosed hconvex coordinate G regularizer anchor bias η p (k + 1) =
      ∫ ω : Seed n k,
        ‖((k : ℝ) / (k + 1)) • averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η k ω +
          (1 / ((k : ℝ) + 1)) • coordinate (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω) - p‖ ^ 2
        ∂seedLaw k := by
    rw [meanOutputError, seedLaw, integral_prod _ Integrable.of_finite]
    simp only [averagedOutput, integral_const, probReal_univ, one_smul]
  change (∫ ω : Seed n k,
        ‖((k : ℝ) / (k + 1)) • averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η k ω +
          (1 / ((k : ℝ) + 1)) • coordinate (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω) - p‖ ^ 2
        ∂seedLaw k) ≤
      ((k : ℝ) / (k + 1)) * meanOutputError S hne hclosed hconvex coordinate G regularizer anchor bias η p k +
        (1 / ((k : ℝ) + 1)) * meanCost S hne hclosed hconvex G regularizer anchor bias η (fun z ↦ ‖coordinate z - p‖ ^ 2) k at hi
  rw [← hleft] at hi
  calc
    _ ≤ ((k : ℝ) + 1) * (((k : ℝ) / (k + 1)) *
        meanOutputError S hne hclosed hconvex coordinate G regularizer anchor bias η p k +
      (1 / ((k : ℝ) + 1)) * meanCost S hne hclosed hconvex G regularizer anchor bias η
        (fun z ↦ ‖coordinate z - p‖ ^ 2) k) := mul_le_mul_of_nonneg_left hi hk.le
    _ = _ := by field_simp <;> ring

/-- The expected squared error of the actual average is bounded by the mean of the actual errors. -/
theorem meanOutputError_jensen (coordinate : E → P) (G : Fin n → E → E)
    (regularizer : E → E) (anchor : S) (bias : E) (η : ℝ) (p : P) (K : ℕ) :
    (K : ℝ) * meanOutputError S hne hclosed hconvex coordinate G regularizer anchor bias η p K ≤
      ∑ k ∈ Finset.range K, meanCost S hne hclosed hconvex G regularizer anchor bias η
        (fun z ↦ ‖coordinate z - p‖ ^ 2) k := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hr := meanOutputError_jensen_recursion S hne hclosed hconvex coordinate G regularizer anchor bias η p K
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    linarith

/-- The actual averaged output satisfies the first inner-error estimate before public constants. -/
theorem meanOutputError_bound (coordinate : E → P) {G : Fin n → E → E}
    (regularizer : E → E) {L μ : ℝ} (hL : 0 < L) (hAS : AveragedSmooth G S L)
    (anchor : S) (bias : E) {η : ℝ} (hη : 0 < η) (hsmall : 11 * η * L ^ 2 ≤ μ)
    (star : S)
    (hstar : VariationalInequality.IsSolution S (fun w ↦ operator G regularizer w + bias) star)
    (W : E → ℝ) (Vstar : ℝ)
    (hLip : ∀ z ∈ S, ‖operator G regularizer z - operator G regularizer star‖ ≤ 3 * L * ‖z - star‖)
    (hMono : ∀ z ∈ S, W z ≤ ⟪operator G regularizer z - operator G regularizer star, z - star⟫_ℝ)
    (hcoercive : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ W z)
    (hcoordinate : ∀ z ∈ S, L * ‖coordinate z - coordinate star‖ ^ 2 ≤ W z)
    (hanchor : ‖(star : E) - anchor‖ ^ 2 ≤ Vstar) {K : ℕ} (hK : 0 < K) :
    meanOutputError S hne hclosed hconvex coordinate G regularizer anchor bias η (coordinate star) K ≤
      (1 / (η * L * (K : ℝ)) + 2 * η * L) * Vstar := by
  have hj := meanOutputError_jensen S hne hclosed hconvex coordinate G regularizer anchor bias η (coordinate star) K
  have hc (k : ℕ) :
      L * meanCost S hne hclosed hconvex G regularizer anchor bias η
        (fun z ↦ ‖coordinate z - coordinate star‖ ^ 2) k ≤
      meanCost S hne hclosed hconvex G regularizer anchor bias η W k := by
    have hp (ω : Seed n k) := hcoordinate
      (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω)
      (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω).property
    have hi := integral_mono (μ := seedLaw k) Integrable.of_finite Integrable.of_finite hp
    simpa only [meanCost, integral_const_mul] using hi
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range K) ↦ hc k)
  rw [← Finset.mul_sum] at hsum
  have hjL := mul_le_mul_of_nonneg_left hj hL.le
  have hjη := mul_le_mul_of_nonneg_left (hjL.trans hsum) hη.le
  have ht := meanCost_sum_bound S hne hclosed hconvex regularizer hL.le hAS anchor bias hη hsmall
    star hstar W Vstar hLip hMono hcoercive hanchor K
  have h0 : ‖(anchor : E) - star‖ ^ 2 ≤ Vstar := by simpa only [norm_sub_rev] using hanchor
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hd : 0 < η * L * (K : ℝ) := mul_pos (mul_pos hη hL) hKreal
  apply (mul_le_mul_iff_right₀ hd).mp
  have hid : (η * L * (K : ℝ)) * ((1 / (η * L * (K : ℝ)) + 2 * η * L) * Vstar) =
      Vstar + (K : ℝ) * (2 * η ^ 2 * L ^ 2 * Vstar) := by
    field_simp [hη.ne', hL.ne', hKreal.ne'] <;> ring
  rw [hid]
  nlinarith

end NCConcave16991.InnerAlgorithm




