import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic hidden-direction estimate

This file verifies the deterministic subspace argument in the proof of
`geo:thm:hidden` (source lines 1758–1784). The Haar probability estimate and
the adaptive query-containment statement are not assumptions disguised as
conclusions here: they are outside the scope of these deterministic lemmas.
-/

namespace MatchingBounds1005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A bound on the projection from `A` into `R` also bounds the reverse
projection. This is the elementary self-adjointness argument for the angle
between subspaces. -/
theorem reverse_projection_bound (A R : Submodule ℝ E) (η : ℝ)
    (hη : 0 ≤ η)
    (hangle : ∀ a ∈ A, ‖R.orthogonalProjection a‖ ≤ η * ‖a‖)
    (v : E) (hv : v ∈ R) :
    ‖A.orthogonalProjection v‖ ≤ η * ‖v‖ := by
  let q : A := A.orthogonalProjection v
  have hq : inner (𝕜 := ℝ) (q : E) v = ‖q‖ ^ 2 := by
    have h := A.orthogonalProjection_inner_eq_zero v (q : E) q.property
    rw [inner_sub_left] at h
    have hself : inner (𝕜 := ℝ) (q : E) (q : E) = ‖q‖ ^ 2 :=
      real_inner_self_eq_norm_sq _
    change inner (𝕜 := ℝ) v (q : E) - inner (𝕜 := ℝ) (q : E) (q : E) = 0 at h
    rw [real_inner_comm] at h
    linarith
  have hr : inner (𝕜 := ℝ) (R.orthogonalProjection (q : E) : E) v =
      inner (𝕜 := ℝ) (q : E) v := by
    have h := R.orthogonalProjection_inner_eq_zero (q : E) v hv
    rw [inner_sub_left] at h
    linarith
  have hb := abs_real_inner_le_norm
    (R.orthogonalProjection (q : E) : E) v
  have ha := hangle (q : E) q.property
  have hnorm : ‖q‖ ^ 2 ≤ (η * ‖q‖) * ‖v‖ := by
    calc
      ‖q‖ ^ 2 = inner (𝕜 := ℝ) (R.orthogonalProjection (q : E) : E) v := by
        rw [hr, hq]
      _ ≤ |inner (𝕜 := ℝ) (R.orthogonalProjection (q : E) : E) v| := le_abs_self _
      _ ≤ ‖R.orthogonalProjection (q : E)‖ * ‖v‖ := hb
      _ ≤ (η * ‖q‖) * ‖v‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  change ‖q‖ ≤ η * ‖v‖
  by_cases hzero : ‖q‖ = 0
  · rw [hzero]
    positivity
  · have hpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

/-- The actual orthogonal projection onto `I + R` is small on a hidden
vector in `A ∩ Iᗮ`, provided `R` makes a small angle with `A`.
This is the factor-two version used by the manuscript. -/
theorem hidden_projection_bound (A I R : Submodule ℝ E) (η : ℝ)
    (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hIA : I ≤ A)
    (hangle : ∀ a ∈ A, ‖R.orthogonalProjection a‖ ≤ η * ‖a‖)
    (a : E) (ha : a ∈ A) (haI : a ∈ Iᗮ) :
    ‖(I ⊔ R).orthogonalProjection a‖ ≤ 2 * η * ‖a‖ := by
  have hinner (w : E) (hw : w ∈ I ⊔ R) :
      |inner (𝕜 := ℝ) a w| ≤ (2 * η * ‖a‖) * ‖w‖ := by
    obtain ⟨i, hi, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
    have hrev := reverse_projection_bound A R η hη hangle v hv
    have hcon : ‖Aᗮ.orthogonalProjection (i + v)‖ ≤ ‖i + v‖ := by
      exact (Aᗮ.orthogonalProjection.le_opNorm _).trans
        (by simpa using (mul_le_mul_of_nonneg_right (Aᗮ.orthogonalProjection_norm_le)
          (norm_nonneg (i + v))))
    have hi0 : Aᗮ.orthogonalProjection i = 0 := by
      apply Submodule.orthogonalProjection_eq_zero_iff.mpr
      exact A.le_orthogonal_orthogonal (hIA hi)
    have hvbound : ‖v‖ ≤ 2 * ‖i + v‖ := by
      have ht' : ‖v‖ ≤ ‖v - (A.orthogonalProjection v : E)‖ +
          ‖A.orthogonalProjection v‖ := by
        simpa using norm_add_le (v - (A.orthogonalProjection v : E))
          (A.orthogonalProjection v : E)
      rw [map_add, hi0, zero_add] at hcon
      rw [← Submodule.norm_coe, Submodule.orthogonalProjection_orthogonal_val] at hcon
      have he := mul_le_mul_of_nonneg_right hηhalf (norm_nonneg v)
      nlinarith
    have hai : inner (𝕜 := ℝ) a i = 0 := by
      exact (Submodule.mem_orthogonal' I a).mp haI i hi
    have har : inner (𝕜 := ℝ) (R.orthogonalProjection a : E) v =
        inner (𝕜 := ℝ) a v := by
      have h := R.orthogonalProjection_inner_eq_zero a v hv
      rw [inner_sub_left] at h
      linarith
    rw [inner_add_right, hai, zero_add, ← har]
    calc
      _ ≤ ‖R.orthogonalProjection a‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (η * ‖a‖) * (2 * ‖i + v‖) := mul_le_mul (hangle a ha) hvbound
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  let q : (I ⊔ R : Submodule ℝ E) := (I ⊔ R).orthogonalProjection a
  have h := hinner (q : E) q.property
  have hq : inner (𝕜 := ℝ) a (q : E) = ‖q‖ ^ 2 := by
    have hp := (I ⊔ R).orthogonalProjection_inner_eq_zero a (q : E) q.property
    rw [inner_sub_left] at hp
    change inner (𝕜 := ℝ) a (q : E) - inner (𝕜 := ℝ) (q : E) (q : E) = 0 at hp
    rw [real_inner_self_eq_norm_sq] at hp
    change inner (𝕜 := ℝ) a (q : E) - ‖q‖ ^ 2 = 0 at hp
    linarith
  rw [hq, abs_of_nonneg (sq_nonneg _)] at h
  change ‖q‖ ^ 2 ≤ (2 * η * ‖a‖) * ‖q‖ at h
  change ‖q‖ ≤ 2 * η * ‖a‖
  by_cases hzero : ‖q‖ = 0
  · rw [hzero]
    positivity
  · have hpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

end MatchingBounds1005
