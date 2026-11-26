import LowRank.SchattenTwoSidedPinching
import LowRank.SchattenTransposeOptimum
import LowRank.MeasurableColumnCompletion
import LowRank.SchattenPaddingOptimum

/-! A measurable right output obtained from the image of compressed left
Ritz columns. The zero-eigenvalue mask keeps the proof valid for deficient
rank, while two-sided pinching gives residual guarantees for all p >= 1. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def refinedRitzColumns (a b k : ℕ) (hka : k ≤ a) (hkb : k ≤ b)
    (M : Matrix (Fin b) (Fin a) ℝ) : Matrix (Fin b) (Fin k) ℝ :=
  completeOrthonormalColumns b k hkb (M * optimalColumnSelector b a k hka M)

theorem measurable_refinedRitzColumns (a b k : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    Measurable (refinedRitzColumns a b k hka hkb) := by
  have hm : Measurable (fun M : Matrix (Fin b) (Fin a) ℝ => M * optimalColumnSelector b a k hka M) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    change Measurable (fun M : Matrix (Fin b) (Fin a) ℝ =>
      ∑ l, M i l * optimalColumnSelector b a k hka M l j)
    apply Finset.measurable_sum
    intro l _
    exact ((measurable_pi_apply l).comp (measurable_pi_apply i)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply l).comp
        (measurable_optimalColumnSelector b a k hka)))
  exact (measurable_completeOrthonormalColumns b k hkb).comp hm

theorem refinedRitzColumns_orthogonal {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (M : Matrix (Fin b) (Fin a) ℝ) :
    (refinedRitzColumns a b k hka hkb M)ᵀ * refinedRitzColumns a b k hka hkb M = 1 :=
  completeOrthonormalColumns_orthogonal hkb _

theorem refinedRitzColumns_fixes {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (M : Matrix (Fin b) (Fin a) ℝ) :
    let Z := refinedRitzColumns a b k hka hkb M
    (Z * Zᵀ) * (M * optimalColumnSelector b a k hka M) = M * optimalColumnSelector b a k hka M :=
  completeOrthonormalColumns_fixes hkb _

theorem schattenPower_masked_left_capture {a b k : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) (W : Matrix (Fin a) (Fin k) ℝ) (hW : Wᵀ * W = 1)
    {D : Matrix (Fin k) (Fin k) ℝ} (hD : IsOrthogonalProjector D) :
    schattenPower p (W * D * Wᵀ * A) = schattenPower p ((Aᵀ * W) * D) := by
  calc
    _ = schattenPower p (W * D * Wᵀ * A)ᵀ := (schattenPower_transpose hp _).symm
    _ = schattenPower p (((Aᵀ * W) * D) * Wᵀ) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hD.symmetric, Matrix.mul_assoc]
    _ = _ := schattenPower_right_extension hp _ W hW

theorem refinedRitzColumns_residual_power {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin a) (Fin a) ℝ}
    (hP : IsOrthogonalProjector P) {p : ℝ} (hp : 1 ≤ p) :
    let M := Aᵀ * P
    let Z := refinedRitzColumns a b k hka hkb M
    schattenPower p (A * (1 - Z * Zᵀ)) ≤
      schattenPower p A - schattenPower p (M * optimalColumnSelector b a k hka M) := by
  let M := Aᵀ * P
  let W := optimalColumnSelector b a k hka M
  let Z := refinedRitzColumns a b k hka hkb M
  have hW : Wᵀ * W = 1 := optimalColumnSelector_orthogonal hka M
  obtain ⟨D, hD, he⟩ := compressedRitz_mask_factorization hka Aᵀ hP
  change M * W = (Aᵀ * W) * D at he
  let R := W * D * Wᵀ
  have hR : IsOrthogonalProjector R := isometric_projector W hW hD
  have hAR : Aᵀ * R = (M * W) * Wᵀ := by
    calc
      _ = ((Aᵀ * W) * D) * Wᵀ := by simp only [R, Matrix.mul_assoc]
      _ = _ := by rw [← he]
  have hfix : (Z * Zᵀ) * (M * W) = M * W := refinedRitzColumns_fixes hka hkb M
  have hs : (Z * Zᵀ) * (Aᵀ * R) = Aᵀ * R := by
    rw [hAR, ← Matrix.mul_assoc, hfix]
  have h := schattenPower_residual_le_sub_left_capture hp A hR
    (column_projector Z (refinedRitzColumns_orthogonal hka hkb M)) hs
  have hc : schattenPower p (R * A) = schattenPower p (M * W) := by
    change schattenPower p (W * D * Wᵀ * A) = _
    rw [schattenPower_masked_left_capture (by linarith : 0 < p) A W hW hD, ← he]
  rw [hc] at h
  exact h

theorem refinedRitzColumns_residual_le_optimum_add_deficit {a b k : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin a) (Fin a) ℝ} (hP : IsOrthogonalProjector P) {p δ : ℝ} (hp : 1 ≤ p)
    (hcapture : schattenPower p (Aᵀ * optimalColumnSelector b a k hka Aᵀ) - δ ≤
      schattenPower p ((Aᵀ * P) * optimalColumnSelector b a k hka (Aᵀ * P))) :
    let Z := refinedRitzColumns a b k hka hkb (Aᵀ * P)
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k + δ := by
  have hp0 : 0 < p := by linarith
  have h := refinedRitzColumns_residual_power hka hkb A hP hp
  have ht := schattenPower_eq_optimum_add_capture hka Aᵀ hp0
  rw [schattenPower_transpose hp0, optimalSchattenPower_transpose hka hkb A hp0] at ht
  dsimp only at h ⊢
  linarith

theorem refinedRitzColumns_relative_of_ritz_errors {a b k : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin a) (Fin a) ℝ} (hP : IsOrthogonalProjector P)
    {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 ≤ ε) (e : Fin k → ℝ) (he : ∀ j, 0 ≤ e j)
    (happrox : ∀ j, (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value
      (lastColumnIndex a k hka j) - e j ≤
        (canonicalOrderedSpectrum a (symmetricRightGram (Aᵀ * P))).value (lastColumnIndex a k hka j))
    (hbudget : (∑ j, max 1 (p / 2) * e j *
      ((canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value
        (lastColumnIndex a k hka j)) ^ (p / 2 - 1)) ≤ ε * optimalSchattenPower p A k) :
    let Z := refinedRitzColumns a b k hka hkb (Aᵀ * P)
    schattenNorm p (A * (1 - Z * Zᵀ)) ≤ (1 + ε) * optimalSchattenNorm p A k := by
  have hc := optimalColumnSelector_power_deficit hka (Aᵀ * P) (by linarith : 0 < p)
    (fun j => (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    e (fun j => (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value_nonneg
      (rightGram_posSemidef Aᵀ) (lastColumnIndex a k hka j)) he happrox
  rw [← optimalColumnSelector_schattenPower hka Aᵀ p] at hc
  have hr := refinedRitzColumns_residual_le_optimum_add_deficit hka hkb A hP hp hc
  dsimp only at hr ⊢
  apply schattenNorm_relative_of_power_excess hkb A _ hp hε
  linarith

end
end LowRank
