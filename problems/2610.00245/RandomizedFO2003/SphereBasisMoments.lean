import RandomizedFO2003.SphereMoments

namespace RandomizedFO2003.Spherical

open MeasureTheory
open scoped BigOperators

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [Fintype I]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem basis_square_sum (b : OrthonormalBasis I ℝ E) (x : E) :
    (∑ i, inner (𝕜 := ℝ) (b i) x ^ 2) = ‖x‖ ^ 2 := by
  simpa [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner x

theorem basis_second_moment (b : OrthonormalBasis I ℝ E) (i : I) :
    moment E (b i) 2 = 1 / (Fintype.card I : ℝ) := by
  have hsame (j : I) : moment E (b j) 2 = moment E (b i) 2 :=
    integral_inner_pow_eq_of_norm_eq E (b j) (b i) (by simp) 2
  have hsum : (∑ j, moment E (b j) 2) = 1 := by
    unfold moment
    rw [← integral_finset_sum _ (fun j _ => integrable_inner_pow E (b j) 2)]
    calc
      _ = ∫ x, ‖x‖ ^ 2 ∂sphereLaw E := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (basis_square_sum b)
      _ = ∫ _x, (1 : ℝ) ∂sphereLaw E := by
        apply integral_congr_ae
        filter_upwards [ae_norm_one E] with x hx
        simp [hx]
      _ = 1 := by simp
  simp_rw [hsame] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hn : (Fintype.card I : ℝ) ≠ 0 := by intro h; simp [h] at hsum
  apply (eq_div_iff hn).mpr
  linarith

theorem basis_fourth_moment (b : OrthonormalBasis I ℝ E) (i : I) :
    moment E (b i) 4 = 3 / ((Fintype.card I : ℝ) * (Fintype.card I + 2)) := by
  classical
  let C := moment E (b i) 4
  have hj (j : I) :
      (∫ x, inner (𝕜 := ℝ) (b i) x ^ 2 * inner (𝕜 := ℝ) (b j) x ^ 2 ∂sphereLaw E) =
        (if j = i then 2 * C / 3 else 0) + C / 3 := by
    by_cases hji : j = i
    · subst j
      simp only [if_true]
      have heq : (fun x => inner (𝕜 := ℝ) (b i) x ^ 2 * inner (𝕜 := ℝ) (b i) x ^ 2) =
          (fun x => inner (𝕜 := ℝ) (b i) x ^ 4) := by funext x; ring
      rw [heq]
      change C = _
      ring
    · rw [if_neg hji, zero_add]
      apply orthogonal_fourth_mixed E (b i) (b j) (by simp) (by simp)
      exact b.orthonormal.inner_eq_zero (Ne.symm hji)
  have hsum : moment E (b i) 2 =
      ∑ j, ∫ x, inner (𝕜 := ℝ) (b i) x ^ 2 * inner (𝕜 := ℝ) (b j) x ^ 2 ∂sphereLaw E := by
    rw [← integral_finset_sum _ (fun j _ => integrable_inner_pow_mul E (b i) (b j) 2 2)]
    apply integral_congr_ae
    filter_upwards [ae_norm_one E] with x hx
    rw [← Finset.mul_sum, basis_square_sum, hx]
    simp
  simp_rw [hj] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [basis_second_moment] at hsum
  have hn : 0 < (Fintype.card I : ℝ) := by
    haveI : Nonempty I := ⟨i⟩
    exact_mod_cast Fintype.card_pos
  apply (eq_div_iff (mul_pos hn (by linarith)).ne').mpr
  have heq := (eq_div_iff hn.ne').mp hsum.symm
  change C * _ = _
  nlinarith

theorem basis_mixed_second_moment (b : OrthonormalBasis I ℝ E) (i j : I) (hij : i ≠ j) :
    (∫ x, inner (𝕜 := ℝ) (b i) x ^ 2 * inner (𝕜 := ℝ) (b j) x ^ 2 ∂sphereLaw E) =
      1 / ((Fintype.card I : ℝ) * (Fintype.card I + 2)) := by
  rw [orthogonal_fourth_mixed E (b i) (b j) (by simp) (by simp)
    (b.orthonormal.inner_eq_zero hij), basis_fourth_moment]
  ring

end RandomizedFO2003.Spherical
