import NCConcave16991.BranchOracleSupport
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Actual word-support correlation with the uniform terminal target -/

namespace NCConcave16991.BranchOracle
noncomputable section
open scoped BigOperators InnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem formalWeight_sq (t : ℕ) : (BranchGeometry.beta ι ^ t) ^ 2 = 1 / (Fintype.card ι : ℝ) ^ t := by
  rw [← pow_mul, Nat.mul_comm t 2, pow_mul, BranchGeometry.beta_sq, div_pow, one_pow]

def supportedTarget (t : ℕ) (S : Finset (Word ι t)) (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (e : E) : FormalLayer (ι := ι) E t :=
  WithLp.toLp 2 (fun w ↦ BranchGeometry.beta ι ^ t • (if w ∈ S then e else W.starProjection e))

theorem supportedTarget_inner {t : ℕ} (S : Finset (Word ι t)) (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (e : E) (z : FormalLayer (ι := ι) E t) (hz : z ∈ wordSupport t S W) :
    ⟪formalTarget E t e, z⟫_ℝ = ⟪supportedTarget t S W e, z⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w ∈ S
  · simp [formalTarget, supportedTarget, hw]
  · have ho := W.starProjection_inner_eq_zero e (z w) (hz w hw)
    rw [inner_sub_left] at ho
    have he : ⟪e, z w⟫_ℝ = ⟪W.starProjection e, z w⟫_ℝ := by linarith
    simpa only [formalTarget, supportedTarget, PiLp.toLp_apply, if_neg hw, real_inner_smul_left, he]

theorem supportedTarget_norm_sq_bound {t : ℕ} (S : Finset (Word ι t)) (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (e : E) (he : ‖e‖ = 1) :
    ‖supportedTarget t S W e‖ ^ 2 ≤ (S.card : ℝ) / (Fintype.card ι : ℝ) ^ t + ‖W.starProjection e‖ ^ 2 := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hp (w : Word ι t) : ‖(if w ∈ S then e else W.starProjection e)‖ ^ 2 ≤
      (if w ∈ S then (1 : ℝ) else 0) + ‖W.starProjection e‖ ^ 2 := by
    by_cases hw : w ∈ S
    · simp only [if_pos hw, he, one_pow]
      exact le_add_of_nonneg_right (sq_nonneg _)
    · simp only [if_neg hw, zero_add, le_refl]
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Word ι t))) ↦ hp w)
  have hind : (∑ w : Word ι t, if w ∈ S then (1 : ℝ) else 0) = S.card := by simp
  rw [Finset.sum_add_distrib, hind, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hc : (Fintype.card (Word ι t) : ℝ) = (Fintype.card ι : ℝ) ^ t := by norm_cast; simp [Word]
  rw [hc] at hsum
  have hnorm : ‖supportedTarget t S W e‖ ^ 2 = (BranchGeometry.beta ι ^ t) ^ 2 *
      ∑ w : Word ι t, ‖(if w ∈ S then e else W.starProjection e)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [supportedTarget, PiLp.toLp_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]
  rw [hnorm, formalWeight_sq]
  calc
    _ ≤ (1 / (Fintype.card ι : ℝ) ^ t) * ((S.card : ℝ) + (Fintype.card ι : ℝ) ^ t * ‖W.starProjection e‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp [hn.ne']

/-- The nuisance reservoir contributes its actual projection score. -/
theorem wordSupport_correlation {t : ℕ} (S : Finset (Word ι t)) (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (e : E) (he : ‖e‖ = 1)
    (z : FormalLayer (ι := ι) E t) (hz : z ∈ wordSupport t S W) (hzn : ‖z‖ ≤ 1) :
    ⟪formalTarget E t e, z⟫_ℝ ^ 2 ≤ (S.card : ℝ) / (Fintype.card ι : ℝ) ^ t +
      ‖W.orthogonalProjectionOnto e‖ ^ 2 := by
  rw [supportedTarget_inner S W e z hz]
  have hi := (abs_real_inner_le_norm (supportedTarget t S W e) z).trans
    ((mul_le_mul_of_nonneg_left hzn (norm_nonneg _)).trans_eq (mul_one _))
  have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hi
  rw [sq_abs] at hs
  exact hs.trans (supportedTarget_norm_sq_bound S W e he)

theorem rotated_wordSupport_correlation {t : ℕ} (S : Finset (Word ι t)) (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (e : E) (he : ‖e‖ = 1)
    (Q : FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (z : FormalLayer (ι := ι) E t) (hz : Q.symm z ∈ wordSupport t S W) (hzn : ‖z‖ ≤ 1) :
    ⟪Q (formalTarget E t e), z⟫_ℝ ^ 2 ≤ (S.card : ℝ) / (Fintype.card ι : ℝ) ^ t +
      ‖W.orthogonalProjectionOnto e‖ ^ 2 := by
  have hi : ⟪Q (formalTarget E t e), z⟫_ℝ = ⟪formalTarget E t e, Q.symm z⟫_ℝ := by
    calc
      _ = ⟪Q (formalTarget E t e), Q (Q.symm z)⟫_ℝ := by rw [Q.apply_symm_apply]
      _ = _ := Q.inner_map_map _ _
  rw [hi]
  exact wordSupport_correlation S W e he (Q.symm z) hz (by simpa using hzn)

end
end NCConcave16991.BranchOracle
