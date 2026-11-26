import MatchingBounds1005.GaussianNets
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Tactic

/-! Deterministic finite-net control of multilinear operator norms. -/
noncomputable section
open scoped BigOperators

namespace MatchingBounds1005.TensorNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem multilinear_norm_le_of_unit {k : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v : Fin k → E, (∀ i, ‖v i‖ = 1) → |f v| ≤ C) :
    ‖f‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  by_cases hv : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hv
    rw [f.map_coord_zero i hi, norm_zero]
    positivity
  have hp : ∀ i, 0 < ‖v i‖ := fun i => norm_pos_iff.mpr (fun hi => hv ⟨i, hi⟩)
  let u : Fin k → E := fun i => ‖v i‖⁻¹ • v i
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    simp only [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp i)),
      inv_mul_cancel₀ (hp i).ne']
  have he : (fun i => ‖v i‖ • u i) = v := by
    funext i
    simp only [u, smul_smul, mul_inv_cancel₀ (hp i).ne', one_smul]
  have hs := f.map_smul_univ (fun i => ‖v i‖) u
  rw [he] at hs
  rw [hs, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hp i).le)), Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hb u hu)
    (Finset.prod_nonneg (fun i _ => (hp i).le))).trans_eq (mul_comm _ _)

/-- A 1/8-net suffices for tensor degrees at most four; the uniform operator
norm is at most twice the largest sampled absolute value. -/
theorem multilinear_norm_bound_of_net {k : ℕ} (hk : k ≤ 4)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (s : Finset E)
    (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 8)
    {r : ℝ} (hr : 0 ≤ r) (hb : ∀ v : Fin k → E, (∀ i, v i ∈ s) → |f v| ≤ r) :
    ‖f‖ ≤ 2 * r := by
  have hpoint : ‖f‖ ≤ r + ‖f‖ / 2 := by
    apply multilinear_norm_le_of_unit f (by positivity)
    intro u hu
    choose v hv hdist using fun i => hnet (u i) (hu i)
    have hnU : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (fun i => (hu i).le)
    have hnV : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (fun i => (hs (v i) (hv i)).le)
    have hnD : ‖u - v‖ ≤ (1 : ℝ) / 8 :=
      (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)).mpr (fun i => (hdist i).le)
    have hdiff := f.norm_image_sub_le u v
    have hpow : max ‖u‖ ‖v‖ ^ (k - 1) ≤ 1 :=
      pow_le_one₀ (le_max_of_le_left (norm_nonneg u)) (max_le hnU hnV)
    have hdiff' : |f u - f v| ≤ ‖f‖ * k / 8 := by
      apply hdiff.trans
      simp only [Fintype.card_fin]
      calc
        _ ≤ ‖f‖ * k * 1 * (1 / 8) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hnD
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    have hkd := mul_le_mul_of_nonneg_left hkR (norm_nonneg f)
    have ht := abs_add (f u - f v) (f v)
    rw [sub_add_cancel] at ht
    have hvb := hb v hv
    linarith
  linarith

end MatchingBounds1005.TensorNets
