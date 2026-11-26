import NCConcave16991.ConditionalHaarMoments

/-! # Actual conditional covariance of unrevealed orthogonal columns -/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.Haar

noncomputable section

theorem entry_continuous {k : ℕ} (i j : Fin k) : Continuous (fun Q : OrthogonalGroup k ↦ entry Q i j) :=
  (PiLp.continuous_apply 2 _ i).comp (continuous_orthogonalLinearIsometryEquiv_apply (basisVector j))

theorem entry_norm_le_one {k : ℕ} (Q : OrthogonalGroup k) (i j : Fin k) : ‖entry Q i j‖ ≤ 1 := by
  have hh := PiLp.norm_apply_le (orthogonalLinearIsometryEquiv Q (basisVector j)) i
  simpa only [entry, (orthogonalLinearIsometryEquiv Q).norm_map, basisVector,
    PiLp.norm_single, norm_one] using hh

theorem entry_product_integrable {k : ℕ} (i j h l : Fin k) :
    Integrable (fun Q ↦ entry Q i j * entry Q h l) (haarLaw k) := by
  apply (integrable_const (1:ℝ)).mono' ((entry_continuous i j).mul (entry_continuous h l)).aestronglyMeasurable
  filter_upwards with Q
  change ‖entry Q i j * entry Q h l‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_mul (entry_norm_le_one Q i j) (entry_norm_le_one Q h l) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem entry_signFlip_other {k : ℕ} (Q : OrthogonalGroup k) (i j l : Fin k) (hl : l ≠ j) :
    entry (Q * signFlip j) i l = entry Q i l := by
  change orthogonalLinearIsometryEquiv (Q * signFlip j) (basisVector l) i =
    orthogonalLinearIsometryEquiv Q (basisVector l) i
  rw [action_mul, signFlip_basis, ite_eq_right hl]

/-- Cross terms between distinct input columns vanish conditionally, even
when the other input column has already been revealed. -/
theorem conditional_distinct_columns_zero {k : ℕ} (A : Finset (Fin k))
    (i h j l : Fin k) (hj : j ∉ A) (hjl : j ≠ l) :
    (haarLaw k)[(fun Q ↦ entry Q i j * entry Q h l) | columnSigma A] =ᵐ[haarLaw k]
      fun _ ↦ (0:ℝ) := by
  apply conditional_zero_of_right_negation (observeColumns A) (observeColumns_measurable A)
    (signFlip j) (observeColumns_signFlip A j hj) (entry_product_integrable i j h l)
  intro Q
  rw [entry_signFlip, entry_signFlip_other Q h j l hjl.symm]
  ring

theorem conditional_same_column_product_eq {k : ℕ} (A : Finset (Fin k))
    (i h j l : Fin k) (hj : j ∉ A) (hl : l ∉ A) :
    (haarLaw k)[(fun Q ↦ entry Q i j * entry Q h j) | columnSigma A] =ᵐ[haarLaw k]
      (haarLaw k)[(fun Q ↦ entry Q i l * entry Q h l) | columnSigma A] :=
  conditional_right_symmetry (observeColumns A) (observeColumns_measurable A)
    (permutationOrthogonal (Equiv.swap j l)) (observeColumns_swap A j l hj hl)
    (entry_product_integrable i j h j) (entry_product_integrable i l h l)
    (fun Q ↦ by rw [entry_swap, entry_swap])

theorem row_inner {k : ℕ} (Q : OrthogonalGroup k) (i h : Fin k) :
    (∑ j : Fin k, entry Q i j * entry Q h j) = if i=h then 1 else 0 := by
  have hh := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ ↦ M i h)
    (Unitary.mul_star_self_of_mem Q.property)
  simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial, Matrix.one_apply, entry_eq_matrix] using hh

def remainingCovariance {k : ℕ} (A : Finset (Fin k)) (i h : Fin k) (Q : OrthogonalGroup k) : ℝ :=
  (if i=h then 1 else 0) - ∑ j : A, entry Q i j.val * entry Q h j.val

theorem remainingCovariance_eq_sum {k : ℕ} (A : Finset (Fin k)) (i h : Fin k) (Q : OrthogonalGroup k) :
    remainingCovariance A i h Q = ∑ j ∈ Aᶜ, entry Q i j * entry Q h j := by
  have hs := Finset.sum_add_sum_compl A (fun j : Fin k ↦ entry Q i j * entry Q h j)
  rw [row_inner] at hs
  unfold remainingCovariance
  rw [Finset.sum_coe_sort A (fun j : Fin k ↦ entry Q i j * entry Q h j)]
  linarith

theorem remainingCovariance_integrable {k : ℕ} (A : Finset (Fin k)) (i h : Fin k) :
    Integrable (remainingCovariance A i h) (haarLaw k) :=
  (integrable_const _).sub (integrable_finsetSum _ (fun j _ ↦ entry_product_integrable i j.val h j.val))

theorem remainingCovariance_observed {k : ℕ} (A : Finset (Fin k)) (i h : Fin k) :
    StronglyMeasurable[columnSigma A] (remainingCovariance A i h) := by
  have ho : Measurable[columnSigma A] (observeColumns A) :=
    measurable_iff_comap_le.mpr le_rfl
  have hj (j : A) : Measurable[columnSigma A] (fun Q ↦ entry Q i j.val * entry Q h j.val) :=
    (((PiLp.continuous_apply 2 _ i).measurable.comp ((measurable_pi_apply j).comp ho)).mul
      ((PiLp.continuous_apply 2 _ h).measurable.comp ((measurable_pi_apply j).comp ho)))
  exact (measurable_const.sub (Finset.measurable_sum _ (fun j _ ↦ hj j))).stronglyMeasurable

/-- The complete conditional covariance matrix of an unrevealed column is
the remaining orthogonal projector divided by the unrevealed dimension. -/
theorem conditional_column_covariance {k : ℕ} (A : Finset (Fin k)) (i h j : Fin k) (hj : j ∉ A) :
    (haarLaw k)[(fun Q ↦ entry Q i j * entry Q h j) | columnSigma A] =ᵐ[haarLaw k]
      fun Q ↦ remainingCovariance A i h Q / (Aᶜ.card : ℝ) := by
  have hs := condExp_finsetSum (μ := haarLaw k) (s := Aᶜ)
    (f := fun l Q ↦ entry Q i l * entry Q h l)
    (fun l _ ↦ entry_product_integrable i l h l) (columnSigma A)
  have hsum : (∑ l ∈ Aᶜ, fun Q ↦ entry Q i l * entry Q h l) = remainingCovariance A i h := by
    funext Q
    simp only [Finset.sum_apply]
    exact (remainingCovariance_eq_sum A i h Q).symm
  rw [hsum, condExp_of_stronglyMeasurable (columnSigma_le A)
    (remainingCovariance_observed A i h) (remainingCovariance_integrable A i h)] at hs
  have heq : ∀ l : Fin k, ∀ᵐ Q ∂haarLaw k, l ∉ A →
      ((haarLaw k)[(fun Q ↦ entry Q i l * entry Q h l) | columnSigma A]) Q =
      ((haarLaw k)[(fun Q ↦ entry Q i j * entry Q h j) | columnSigma A]) Q := by
    intro l
    by_cases hl : l ∉ A
    · exact (conditional_same_column_product_eq A i h l j hl hj).mono (fun Q hQ _ ↦ hQ)
    · filter_upwards with Q
      intro h
      exact False.elim (hl h)
  have hforall := ae_all_iff.mpr heq
  have hcard : (0 : ℝ) < Aᶜ.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨j, Finset.mem_compl.mpr hj⟩
  filter_upwards [hs, hforall] with Q hQ heQ
  simp only [Finset.sum_apply] at hQ
  have hsumQ : (∑ l ∈ Aᶜ, ((haarLaw k)[(fun Q ↦ entry Q i l * entry Q h l) | columnSigma A]) Q) =
      (Aᶜ.card : ℝ) * ((haarLaw k)[(fun Q ↦ entry Q i j * entry Q h j) | columnSigma A]) Q := by
    calc
      _ = ∑ l ∈ Aᶜ, ((haarLaw k)[(fun Q ↦ entry Q i j * entry Q h j) | columnSigma A]) Q :=
        Finset.sum_congr rfl (fun l hl ↦ heQ l (Finset.mem_compl.mp hl))
      _ = _ := by simp
  rw [hsumQ] at hQ
  apply (eq_div_iff hcard.ne').2
  nlinarith only [hQ]

end

end NCConcave16991.Haar
