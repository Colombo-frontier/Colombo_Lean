import NCConcave16991.ConditionalHaarColumns

/-! # Exact conditional Haar second moments after fixed column reveals -/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.Haar

noncomputable section

theorem entry_eq_matrix {k : ℕ} (Q : OrthogonalGroup k) (i j : Fin k) :
    entry Q i j = Q.val i j := by
  change (Q.val.mulVec (Pi.single j (1:ℝ))) i = Q.val i j
  rw [Matrix.mulVec_single_one]
  rfl

theorem row_energy {k : ℕ} (Q : OrthogonalGroup k) (i : Fin k) :
    (∑ j : Fin k, entry Q i j ^ 2) = 1 := by
  have hh := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ ↦ M i i)
    (Unitary.mul_star_self_of_mem Q.property)
  simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial, Matrix.one_apply_eq, pow_two, entry_eq_matrix] using hh

def remainingEnergy {k : ℕ} (A : Finset (Fin k)) (i : Fin k) (Q : OrthogonalGroup k) : ℝ :=
  1 - ∑ j : A, entry Q i j.val ^ 2

theorem remainingEnergy_eq_sum {k : ℕ} (A : Finset (Fin k)) (i : Fin k) (Q : OrthogonalGroup k) :
    remainingEnergy A i Q = ∑ j ∈ Aᶜ, entry Q i j ^ 2 := by
  have hs := Finset.sum_add_sum_compl A (fun j : Fin k ↦ entry Q i j ^ 2)
  rw [row_energy] at hs
  unfold remainingEnergy
  rw [Finset.sum_coe_sort A (fun j : Fin k ↦ entry Q i j ^ 2)]
  linarith

theorem remainingEnergy_nonneg {k : ℕ} (A : Finset (Fin k)) (i : Fin k) (Q : OrthogonalGroup k) :
    0 ≤ remainingEnergy A i Q := by
  rw [remainingEnergy_eq_sum]
  exact Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)

theorem remainingEnergy_le_one {k : ℕ} (A : Finset (Fin k)) (i : Fin k) (Q : OrthogonalGroup k) :
    remainingEnergy A i Q ≤ 1 := by
  unfold remainingEnergy
  have hs : 0 ≤ ∑ j : A, entry Q i j.val ^ 2 := Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)
  linarith

theorem remainingEnergy_integrable {k : ℕ} (A : Finset (Fin k)) (i : Fin k) :
    Integrable (remainingEnergy A i) (haarLaw k) :=
  (integrable_const 1).sub (integrable_finsetSum _ (fun j _ ↦ entry_sq_integrable i j.val))

theorem remainingEnergy_observed {k : ℕ} (A : Finset (Fin k)) (i : Fin k) :
    StronglyMeasurable[columnSigma A] (remainingEnergy A i) := by
  have ho : Measurable[columnSigma A] (observeColumns A) :=
    measurable_iff_comap_le.mpr le_rfl
  have hj (j : A) : Measurable[columnSigma A] (fun Q ↦ entry Q i j.val ^ 2) :=
    (((PiLp.continuous_apply 2 _ i).measurable.comp
      ((measurable_pi_apply j).comp ho)).pow_const 2)
  exact (measurable_const.sub (Finset.measurable_sum _ (fun j _ ↦ hj j))).stronglyMeasurable

/-- The exact conditional variance of one unrevealed column, derived from
actual Haar symmetry and row normalization. The numerator is the observed
residual row energy, not an assumed isotropy certificate. -/
theorem conditional_entry_second_moment {k : ℕ} (A : Finset (Fin k)) (i j : Fin k) (hj : j ∉ A) :
    (haarLaw k)[(fun Q ↦ entry Q i j ^ 2) | columnSigma A] =ᵐ[haarLaw k]
      fun Q ↦ remainingEnergy A i Q / (Aᶜ.card : ℝ) := by
  have hs := condExp_finsetSum (μ := haarLaw k) (s := Aᶜ)
    (f := fun l Q ↦ entry Q i l ^ 2) (fun l _ ↦ entry_sq_integrable i l) (columnSigma A)
  have hsum : (∑ l ∈ Aᶜ, fun Q ↦ entry Q i l ^ 2) = remainingEnergy A i := by
    funext Q
    simp only [Finset.sum_apply]
    exact (remainingEnergy_eq_sum A i Q).symm
  rw [hsum, condExp_of_stronglyMeasurable (columnSigma_le A)
    (remainingEnergy_observed A i) (remainingEnergy_integrable A i)] at hs
  have heq : ∀ l : Fin k, ∀ᵐ Q ∂haarLaw k, l ∉ A →
      ((haarLaw k)[(fun Q ↦ entry Q i l ^ 2) | columnSigma A]) Q =
      ((haarLaw k)[(fun Q ↦ entry Q i j ^ 2) | columnSigma A]) Q := by
    intro l
    by_cases hl : l ∉ A
    · exact (conditional_entry_sq_eq A i l j hl hj).mono (fun Q hQ _ ↦ hQ)
    · filter_upwards with Q
      intro h
      exact False.elim (hl h)
  have hforall := ae_all_iff.mpr heq
  have hcard : (0 : ℝ) < Aᶜ.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨j, Finset.mem_compl.mpr hj⟩
  filter_upwards [hs, hforall] with Q hQ heQ
  have hsumQ : (∑ l ∈ Aᶜ, ((haarLaw k)[(fun Q ↦ entry Q i l ^ 2) | columnSigma A]) Q) =
      (Aᶜ.card : ℝ) * ((haarLaw k)[(fun Q ↦ entry Q i j ^ 2) | columnSigma A]) Q := by
    calc
      _ = ∑ l ∈ Aᶜ, ((haarLaw k)[(fun Q ↦ entry Q i j ^ 2) | columnSigma A]) Q :=
        Finset.sum_congr rfl (fun l hl ↦ heQ l (Finset.mem_compl.mp hl))
      _ = _ := by simp
  simp only [Finset.sum_apply] at hQ
  rw [hsumQ] at hQ
  apply (eq_div_iff hcard.ne').2
  nlinarith only [hQ]

end

end NCConcave16991.Haar
