import RandomizedFO2003.SphereBasisMoments
import Mathlib.Probability.Variance

namespace RandomizedFO2003.Spherical

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [Fintype I]

noncomputable def projectionMass (b : OrthonormalBasis I ℝ E) (S : Finset I) (x : E) : ℝ :=
  ∑ i ∈ S, inner (𝕜 := ℝ) (b i) x ^ 2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem projectionMass_nonneg (b : OrthonormalBasis I ℝ E) (S : Finset I) (x : E) :
    0 ≤ projectionMass b S x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem projectionMass_le_norm_sq (b : OrthonormalBasis I ℝ E) (S : Finset I) (x : E) :
    projectionMass b S x ≤ ‖x‖ ^ 2 := by
  rw [← basis_square_sum b]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
  intro i _ _
  exact sq_nonneg _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem continuous_projectionMass (b : OrthonormalBasis I ℝ E) (S : Finset I) :
    Continuous (projectionMass b S) := by unfold projectionMass; fun_prop

theorem projectionMass_memLp (b : OrthonormalBasis I ℝ E) (S : Finset I) :
    MemLp (projectionMass b S) 2 (sphereLaw E) := by
  apply MemLp.of_bound (continuous_projectionMass b S).aestronglyMeasurable 1
  filter_upwards [ae_norm_one E] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (projectionMass_nonneg b S x)]
  simpa [hx] using projectionMass_le_norm_sq b S x

theorem projectionMass_mean (b : OrthonormalBasis I ℝ E) (S : Finset I) :
    (∫ x, projectionMass b S x ∂sphereLaw E) = (S.card : ℝ) / (Fintype.card I : ℝ) := by
  unfold projectionMass
  rw [integral_finset_sum S (fun i _ => integrable_inner_pow E (b i) 2)]
  have hm (i : I) : (∫ x, inner (𝕜 := ℝ) (b i) x ^ 2 ∂sphereLaw E) =
      1 / (Fintype.card I : ℝ) := basis_second_moment b i
  simp_rw [hm]
  simp [div_eq_mul_inv]

theorem projectionMass_second_moment (b : OrthonormalBasis I ℝ E) (S : Finset I) :
    (∫ x, projectionMass b S x ^ 2 ∂sphereLaw E) =
      (S.card : ℝ) * (S.card + 2) / ((Fintype.card I : ℝ) * (Fintype.card I + 2)) := by
  classical
  let d := (Fintype.card I : ℝ) * (Fintype.card I + 2)
  have hj (i j : I) :
      (∫ x, inner (𝕜 := ℝ) (b i) x ^ 2 * inner (𝕜 := ℝ) (b j) x ^ 2 ∂sphereLaw E) =
        (if j = i then 2 / d else 0) + 1 / d := by
    by_cases hij : j = i
    · subst j
      have heq : (fun x => inner (𝕜 := ℝ) (b i) x ^ 2 * inner (𝕜 := ℝ) (b i) x ^ 2) =
          (fun x => inner (𝕜 := ℝ) (b i) x ^ 4) := by funext x; ring
      rw [heq, if_pos rfl]
      change moment E (b i) 4 = _
      rw [basis_fourth_moment]
      dsimp [d]
      ring
    · rw [if_neg hij, zero_add]
      exact basis_mixed_second_moment b i j (Ne.symm hij)
  have heq : (fun x => projectionMass b S x ^ 2) =
      (fun x => ∑ i ∈ S, ∑ j ∈ S,
        inner (𝕜 := ℝ) (b i) x ^ 2 * inner (𝕜 := ℝ) (b j) x ^ 2) := by
    funext x
    simp only [projectionMass, sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_finset_sum S (fun i _ => integrable_finset_sum S
    (fun j _ => integrable_inner_pow_mul E (b i) (b j) 2 2))]
  have hinner (i : I) (hi : i ∈ S) :
      (∫ x, ∑ j ∈ S, inner (𝕜 := ℝ) (b i) x ^ 2 * inner (𝕜 := ℝ) (b j) x ^ 2 ∂sphereLaw E) =
        2 / d + (S.card : ℝ) / d := by
    rw [integral_finset_sum S (fun j _ => integrable_inner_pow_mul E (b i) (b j) 2 2)]
    simp_rw [hj]
    simp [Finset.sum_add_distrib, hi, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [d]
  ring

theorem projectionMass_variance (b : OrthonormalBasis I ℝ E) (S : Finset I)
    (hd : 0 < (Fintype.card I : ℝ)) :
    variance (projectionMass b S) (sphereLaw E) =
      2 * S.card * ((Fintype.card I : ℝ) - S.card) /
        ((Fintype.card I : ℝ) ^ 2 * (Fintype.card I + 2)) := by
  rw [variance_def' (projectionMass_memLp b S)]
  simp only [Pi.pow_apply]
  rw [projectionMass_second_moment, projectionMass_mean]
  have hd2 : (Fintype.card I : ℝ) + 2 ≠ 0 := by linarith
  field_simp [hd.ne', hd2]
  ring

/-- A relative deviation bound for the energy of any nonzero coordinate
subspace. No independence of sphere coordinates is asserted. -/
theorem projectionMass_relative_tail (b : OrthonormalBasis I ℝ E) (S : Finset I)
    (hS : S.Nonempty) (η : ℝ) (hη : 0 < η) :
    sphereLaw E {x | η * ((S.card : ℝ) / Fintype.card I) ≤
      |projectionMass b S x - (S.card : ℝ) / Fintype.card I|} ≤
      ENNReal.ofReal (2 / (η ^ 2 * (S.card : ℝ))) := by
  have hk : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hd : 0 < (Fintype.card I : ℝ) := hk.trans_le (by exact_mod_cast S.card_le_univ)
  have hv := projectionMass_variance b S hd
  have hvbound : variance (projectionMass b S) (sphereLaw E) ≤
      2 * (S.card : ℝ) / (Fintype.card I : ℝ) ^ 2 := by
    rw [hv]
    have hd2 : 0 < (Fintype.card I : ℝ) + 2 := by linarith
    rw [div_mul_eq_div_div]
    apply (div_le_iff₀ hd2).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hd)).mpr
    nlinarith
  have ht := meas_ge_le_variance_div_sq (projectionMass_memLp b S)
    (mul_pos hη (div_pos hk hd))
  rw [projectionMass_mean] at ht
  apply ht.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (2 * (S.card : ℝ) / (Fintype.card I : ℝ) ^ 2) /
        (η * ((S.card : ℝ) / Fintype.card I)) ^ 2 :=
      div_le_div_of_nonneg_right hvbound (sq_nonneg _)
    _ = _ := by field_simp; ring

end RandomizedFO2003.Spherical
