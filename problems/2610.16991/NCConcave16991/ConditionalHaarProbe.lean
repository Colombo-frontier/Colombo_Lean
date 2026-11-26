import NCConcave16991.ConditionalHaarCovariance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# History-dependent probes against unrevealed Haar columns

The probe coefficients are measurable functions of the actual revealed
columns. They are not independent of that history. Conditional moments are
derived using the genuine Haar covariance and the pull-out theorem.
-/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.Haar

noncomputable section

def probe {k : ℕ} (a : Fin k → OrthogonalGroup k → ℝ) (j : Fin k) (Q : OrthogonalGroup k) : ℝ :=
  ∑ i, a i Q * entry Q i j

/-- The complete observation-dependent probe is conditionally centered,
despite arbitrary dependence of its coefficients on the revealed columns. -/
theorem conditional_probe_mean_zero {k : ℕ} (A : Finset (Fin k))
    (a : Fin k → OrthogonalGroup k → ℝ) {C : ℝ}
    (hameas : ∀ i, StronglyMeasurable[columnSigma A] (a i))
    (habound : ∀ i Q, ‖a i Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) :
    (haarLaw k)[probe a j | columnSigma A] =ᵐ[haarLaw k] fun _ ↦ (0:ℝ) := by
  have hi (i : Fin k) : Integrable (fun Q ↦ a i Q * entry Q i j) (haarLaw k) :=
    (entry_integrable i j).bdd_mul ((hameas i).mono (columnSigma_le A)).aestronglyMeasurable
      (Filter.Eventually.of_forall (habound i))
  have ht (i : Fin k) :
      (haarLaw k)[(fun Q ↦ a i Q * entry Q i j) | columnSigma A] =ᵐ[haarLaw k]
        fun _ ↦ (0:ℝ) := by
    have hp := condExp_mul_of_stronglyMeasurable_left (μ := haarLaw k)
      (hameas i) (hi i) (entry_integrable i j)
    have hz := conditional_entry_mean_zero A i j hj
    filter_upwards [hp, hz] with Q hP hZ
    change ((haarLaw k)[(fun Q ↦ a i Q * entry Q i j) | columnSigma A]) Q =
      a i Q * ((haarLaw k)[(fun Q ↦ entry Q i j) | columnSigma A]) Q at hP
    simpa only [hZ, mul_zero] using hP
  have hs := condExp_finsetSum (μ := haarLaw k) (s := Finset.univ)
    (f := fun i ↦ fun Q ↦ a i Q * entry Q i j) (fun i _ ↦ hi i) (columnSigma A)
  have he : probe a j = ∑ i : Fin k, fun Q ↦ a i Q * entry Q i j := by
    funext Q
    simp only [probe, Finset.sum_apply]
  rw [he]
  have hall := ae_all_iff.mpr ht
  filter_upwards [hs, hall] with Q hS hA
  simp only [Finset.sum_apply] at hS
  rw [hS]
  simp_rw [hA]
  simp

theorem probe_square {k : ℕ} (a : Fin k → OrthogonalGroup k → ℝ) (j : Fin k) (Q : OrthogonalGroup k) :
    probe a j Q ^ 2 = ∑ i : Fin k, ∑ h : Fin k,
      (a i Q * a h Q) * (entry Q i j * entry Q h j) := by
  rw [pow_two, probe, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro h hh
  ring

theorem coefficient_product_bound {k : ℕ} (a : Fin k → OrthogonalGroup k → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i Q, ‖a i Q‖ ≤ C) (i h : Fin k) (Q : OrthogonalGroup k) :
    ‖a i Q * a h Q‖ ≤ C ^ 2 := by
  rw [norm_mul]
  exact (mul_le_mul (ha i Q) (ha h Q) (norm_nonneg _) hC).trans_eq (by ring)

theorem weighted_entry_product_integrable {k : ℕ} (A : Finset (Fin k))
    (a : Fin k → OrthogonalGroup k → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hameas : ∀ i, StronglyMeasurable[columnSigma A] (a i))
    (habound : ∀ i Q, ‖a i Q‖ ≤ C) (i h j : Fin k) :
    Integrable (fun Q ↦ (a i Q * a h Q) * (entry Q i j * entry Q h j)) (haarLaw k) :=
  (entry_product_integrable i j h j).bdd_mul
    (((hameas i).mul (hameas h)).mono (columnSigma_le A)).aestronglyMeasurable
    (Filter.Eventually.of_forall (coefficient_product_bound a hC habound i h))

/-- A complete conditional mean-square formula for a probe chosen from the
observed history, with no independence or conditional-isotropy premise. -/
theorem conditional_probe_second_moment {k : ℕ} (A : Finset (Fin k))
    (a : Fin k → OrthogonalGroup k → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hameas : ∀ i, StronglyMeasurable[columnSigma A] (a i))
    (habound : ∀ i Q, ‖a i Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) :
    (haarLaw k)[(fun Q ↦ probe a j Q ^ 2) | columnSigma A] =ᵐ[haarLaw k]
      fun Q ↦ ∑ i : Fin k, ∑ h : Fin k,
        (a i Q * a h Q) * (remainingCovariance A i h Q / (Aᶜ.card : ℝ)) := by
  let term := fun i h : Fin k ↦ fun Q : OrthogonalGroup k ↦
    (a i Q * a h Q) * (entry Q i j * entry Q h j)
  have hint (i h : Fin k) : Integrable (term i h) (haarLaw k) :=
    weighted_entry_product_integrable A a hC hameas habound i h j
  have hterm (i h : Fin k) :
      (haarLaw k)[term i h | columnSigma A] =ᵐ[haarLaw k]
        fun Q ↦ (a i Q * a h Q) * (remainingCovariance A i h Q / (Aᶜ.card : ℝ)) := by
    have hp := condExp_mul_of_stronglyMeasurable_left (μ := haarLaw k)
      ((hameas i).mul (hameas h)) (hint i h) (entry_product_integrable i j h j)
    have hc := conditional_column_covariance A i h j hj
    filter_upwards [hp, hc] with Q hP hCov
    change ((haarLaw k)[term i h | columnSigma A]) Q =
      (a i Q * a h Q) * ((haarLaw k)[(fun Q ↦ entry Q i j * entry Q h j) | columnSigma A]) Q at hP
    rw [hCov] at hP
    exact hP
  have hexpr : (fun Q ↦ probe a j Q ^ 2) = ∑ i : Fin k, ∑ h : Fin k, term i h := by
    funext Q
    simp only [Finset.sum_apply]
    exact probe_square a j Q
  have houter := condExp_finsetSum (μ := haarLaw k) (s := Finset.univ)
    (f := fun i ↦ ∑ h : Fin k, term i h)
    (fun i _ ↦ integrable_finsetSum' _ (fun h _ ↦ hint i h)) (columnSigma A)
  have hinner (i : Fin k) := condExp_finsetSum (μ := haarLaw k) (s := Finset.univ)
    (f := fun h ↦ term i h) (fun h _ ↦ hint i h) (columnSigma A)
  have hinnerAll := ae_all_iff.mpr hinner
  have htermAll := ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (hterm i))
  rw [hexpr]
  filter_upwards [houter, hinnerAll, htermAll] with Q hO hI hT
  simp only [Finset.sum_apply] at hO hI
  rw [hO]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hI i]
  exact Finset.sum_congr rfl (fun h hh ↦ hT i h)

theorem probe_covariance_sum {k : ℕ} (A : Finset (Fin k))
    (a : Fin k → OrthogonalGroup k → ℝ) (Q : OrthogonalGroup k) :
    (∑ i : Fin k, ∑ h : Fin k, (a i Q * a h Q) * remainingCovariance A i h Q) =
      (∑ i : Fin k, a i Q ^ 2) - ∑ l : A, probe a l.val Q ^ 2 := by
  have hdiag : (∑ i : Fin k, ∑ h : Fin k,
      (a i Q * a h Q) * (if i=h then 1 else 0)) = ∑ i : Fin k, a i Q ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_ite, eq_comm, pow_two]
  have htriple : (∑ i : Fin k, ∑ h : Fin k,
      (a i Q * a h Q) * ∑ l : A, entry Q i l.val * entry Q h l.val) =
      ∑ l : A, probe a l.val Q ^ 2 := by
    calc
      _ = ∑ i : Fin k, ∑ h : Fin k, ∑ l : A,
          (a i Q * a h Q) * (entry Q i l.val * entry Q h l.val) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ i : Fin k, ∑ l : A, ∑ h : Fin k,
          (a i Q * a h Q) * (entry Q i l.val * entry Q h l.val) := by
        exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_comm)
      _ = ∑ l : A, ∑ i : Fin k, ∑ h : Fin k,
          (a i Q * a h Q) * (entry Q i l.val * entry Q h l.val) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun l _ ↦ (probe_square a l.val Q).symm)
  simp_rw [remainingCovariance, mul_sub, Finset.sum_sub_distrib]
  rw [hdiag, htriple]

theorem conditional_probe_variance_formula {k : ℕ} (A : Finset (Fin k))
    (a : Fin k → OrthogonalGroup k → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hameas : ∀ i, StronglyMeasurable[columnSigma A] (a i))
    (habound : ∀ i Q, ‖a i Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) :
    (haarLaw k)[(fun Q ↦ probe a j Q ^ 2) | columnSigma A] =ᵐ[haarLaw k]
      fun Q ↦ ((∑ i : Fin k, a i Q ^ 2) - ∑ l : A, probe a l.val Q ^ 2) / (Aᶜ.card : ℝ) := by
  have hh := conditional_probe_second_moment A a hC hameas habound j hj
  apply hh.trans
  filter_upwards with Q
  simp_rw [← mul_div_assoc, ← Finset.sum_div]
  rw [probe_covariance_sum]

theorem conditional_probe_variance_bound {k : ℕ} (A : Finset (Fin k))
    (a : Fin k → OrthogonalGroup k → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hameas : ∀ i, StronglyMeasurable[columnSigma A] (a i))
    (habound : ∀ i Q, ‖a i Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) :
    ∀ᵐ Q ∂haarLaw k, ((haarLaw k)[(fun Q ↦ probe a j Q ^ 2) | columnSigma A]) Q ≤
      (∑ i : Fin k, a i Q ^ 2) / (Aᶜ.card : ℝ) := by
  filter_upwards [conditional_probe_variance_formula A a hC hameas habound j hj] with Q hQ
  rw [hQ]
  exact div_le_div_of_nonneg_right (sub_le_self _ (Finset.sum_nonneg (fun l _ ↦ sq_nonneg _)))
    (Nat.cast_nonneg _)

end

end NCConcave16991.Haar
