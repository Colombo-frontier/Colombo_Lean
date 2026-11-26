import NCConcave16991.InnerAveraging

/-! # Explicit public constants for the independent inner algorithm -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.InnerAlgorithm

/-- The paper's prescribed inner step size `μ/(2^16 L²)`. -/
def sourceStepSize (L μ : ℝ) : ℝ := μ / (65536 * L ^ 2)

 theorem sourceStepSize_pos {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) :
    0 < sourceStepSize L μ := by dsimp [sourceStepSize]; positivity

 theorem sourceStepSize_small {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) :
    11 * sourceStepSize L μ * L ^ 2 ≤ μ := by
  have hid : 11 * sourceStepSize L μ * L ^ 2 = (11 / 65536 : ℝ) * μ := by
    dsimp [sourceStepSize]
    field_simp [hL.ne'] <;> ring
  rw [hid]
  nlinarith

/-- The actual public horizon `K ≥ 2^32 κ²` gives the source coefficient. -/
theorem source_inner_coefficient {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ)
    {K : ℕ} (hK : 4294967296 * (L / μ) ^ 2 ≤ (K : ℝ)) :
    1 / (sourceStepSize L μ * L * (K : ℝ)) + 2 * sourceStepSize L μ * L ≤
      3 / (65536 * (L / μ)) := by
  have hκ : 0 < L / μ := div_pos hL hμ
  have hη := sourceStepSize_pos hL hμ
  have hm := mul_le_mul_of_nonneg_left hK (mul_nonneg hη.le hL.le)
  have hid : (sourceStepSize L μ * L) * (4294967296 * (L / μ) ^ 2) =
      65536 * (L / μ) := by
    dsimp [sourceStepSize]
    field_simp [hL.ne', hμ.ne'] <;> ring
  rw [hid] at hm
  have hprod : 65536 * (L / μ) ≤ sourceStepSize L μ * L * (K : ℝ) := hm
  have hinv := one_div_le_one_div_of_le (by positivity : 0 < 65536 * (L / μ)) hprod
  have hnoise : 2 * sourceStepSize L μ * L = 2 / (65536 * (L / μ)) := by
    dsimp [sourceStepSize]
    field_simp [hL.ne', hμ.ne'] <;> ring
  calc
    _ ≤ 1 / (65536 * (L / μ)) + 2 * sourceStepSize L μ * L := by linarith
    _ = _ := by rw [hnoise]; ring

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- The paper's first inner-error line for the genuine finite-seed averaged output.
The hypotheses are actual AS/operator/VI interfaces, rather than an algorithmic recurrence. -/
theorem source_inner_output_bound (coordinate : E → P) {G : Fin n → E → E}
    (regularizer : E → E) {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hAS : AveragedSmooth G S L)
    (anchor : S) (bias : E) (star : S)
    (hstar : VariationalInequality.IsSolution S (fun w ↦ operator G regularizer w + bias) star)
    (W : E → ℝ) (Vstar : ℝ)
    (hLip : ∀ z ∈ S, ‖operator G regularizer z - operator G regularizer star‖ ≤ 3 * L * ‖z - star‖)
    (hMono : ∀ z ∈ S, W z ≤ ⟪operator G regularizer z - operator G regularizer star, z - star⟫_ℝ)
    (hcoercive : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ W z)
    (hcoordinate : ∀ z ∈ S, L * ‖coordinate z - coordinate star‖ ^ 2 ≤ W z)
    (hanchor : ‖(star : E) - anchor‖ ^ 2 ≤ Vstar) {K : ℕ}
    (hK : 4294967296 * (L / μ) ^ 2 ≤ (K : ℝ)) :
    meanOutputError S hne hclosed hconvex coordinate G regularizer anchor bias
      (sourceStepSize L μ) (coordinate star) K ≤ 3 / (65536 * (L / μ)) * Vstar := by
  have hκ : 0 < L / μ := div_pos hL hμ
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hK
    exact_mod_cast this
  have hV : 0 ≤ Vstar := (sq_nonneg _).trans hanchor
  have hb := meanOutputError_bound S hne hclosed hconvex coordinate regularizer hL hAS anchor bias
    (sourceStepSize_pos hL hμ) (sourceStepSize_small hL hμ) star hstar W Vstar
    hLip hMono hcoercive hcoordinate hanchor hKpos
  exact hb.trans (mul_le_mul_of_nonneg_right (source_inner_coefficient hL hμ hK) hV)

end NCConcave16991.InnerAlgorithm
