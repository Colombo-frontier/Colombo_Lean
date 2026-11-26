import SecondOrder.CurvaturePrefixSampling
import SecondOrder.FirstOrderScales
import SecondOrder.FiniteConditionalEntropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def firstOrderFairArray (d : ℕ) (R : ℝ) (hR : 2≤R) : PMF (Fin d → SignedCoefficient R) :=
  finitePiPMF (fun _ => fairCoefficientPMF R hR)

theorem firstOrderFairArray_ne_zero (d : ℕ) (R : ℝ) (hR : 2≤R) :
    ∀ a, firstOrderFairArray d R hR a≠0 :=
  finitePiPMF_ne_zero _ (fun _ => fairCoefficientPMF_ne_zero R hR)

theorem firstOrderCoefficientLaw_ne_zero (θ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R) :
    ∀ a, firstOrderCoefficientLaw θ R hR a≠0 :=
  finitePiPMF_ne_zero _ (fun e => coefficientPMF_ne_zero R _ hR (signValue_sq (θ e)))

/-- Only the specified hidden prefix affects the sampling law. Unused future
arrays are filled with independent fair coefficients on the same support. -/
def firstOrderPrefixArray (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (revealed : ℕ) (i : Fin (T+1)) : PMF (Fin d → SignedCoefficient R) :=
  if i.val<revealed then firstOrderCoefficientLaw (Θ i) R hR else firstOrderFairArray d R hR

def firstOrderPrefixCoefficientLaw (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (revealed : ℕ) : PMF (FirstOrderCoefficients d T R) :=
  finitePiPMF (firstOrderPrefixArray Θ R hR revealed)

theorem firstOrderPrefixArray_ne_zero (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (revealed : ℕ) (i : Fin (T+1)) : ∀ a, firstOrderPrefixArray Θ R hR revealed i a≠0 := by
  unfold firstOrderPrefixArray
  split_ifs
  · exact firstOrderCoefficientLaw_ne_zero (Θ i) R hR
  · exact firstOrderFairArray_ne_zero d R hR

theorem firstOrderPrefixCoefficientLaw_ne_zero (Θ : Fin (T+1) → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (revealed : ℕ) : ∀ z, firstOrderPrefixCoefficientLaw Θ R hR revealed z≠0 :=
  finitePiPMF_ne_zero _ (firstOrderPrefixArray_ne_zero Θ R hR revealed)

theorem firstOrderPrefixCoefficientLaw_hidden_invariant (Θ Θ' : Fin (T+1) → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (revealed : ℕ) (hΘ : ∀ i, i.val<revealed → Θ i=Θ' i) :
    firstOrderPrefixCoefficientLaw Θ R hR revealed=firstOrderPrefixCoefficientLaw Θ' R hR revealed := by
  unfold firstOrderPrefixCoefficientLaw
  congr 1
  funext i
  unfold firstOrderPrefixArray
  split_ifs with hi
  · rw [hΘ i hi]
  · rfl

theorem firstOrderCoefficientLaw_pmfKL (θ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R) :
    pmfKL (firstOrderCoefficientLaw θ R hR) (firstOrderFairArray d R hR)≤
      (d:ℝ)/R^2 := by
  unfold firstOrderCoefficientLaw firstOrderFairArray
  rw [pmfKL_finitePi_any_fintype _ _ _
    (fun e => coefficientPMF_ne_zero R _ hR (signValue_sq (θ e)))
    (fun _ => fairCoefficientPMF_ne_zero R hR)]
  calc
    _ ≤ ∑ _ : Fin d, 1/R^2 := Finset.sum_le_sum (fun e _ => by
      rw [pmfKL_coefficient]
      exact biased_sign_entropy hR (signValue_sq (θ e)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]; ring

/-- Enlarging the hidden prefix by one array costs only that array's entropy. -/
theorem firstOrderPrefixCoefficientLaw_pmfKL (Θ : Fin (T+1) → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) {k : ℕ} (hk : k≤T) :
    pmfKL (firstOrderPrefixCoefficientLaw Θ R hR (k+1)) (firstOrderPrefixCoefficientLaw Θ R hR k)≤
      (d:ℝ)/R^2 := by
  unfold firstOrderPrefixCoefficientLaw
  rw [pmfKL_finitePi_any_fintype _ _ _ (firstOrderPrefixArray_ne_zero Θ R hR (k+1))
    (firstOrderPrefixArray_ne_zero Θ R hR k)]
  let j : Fin (T+1) := ⟨k,by omega⟩
  have he : (∑ i, pmfKL (firstOrderPrefixArray Θ R hR (k+1) i) (firstOrderPrefixArray Θ R hR k i)) =
      pmfKL (firstOrderCoefficientLaw (Θ j) R hR) (firstOrderFairArray d R hR) := by
    rw [Finset.sum_eq_single j]
    · simp [firstOrderPrefixArray, j]
    · intro i _ hij
      have hne : i.val≠k := by intro h; apply hij; exact Fin.ext h
      unfold firstOrderPrefixArray
      by_cases hi : i.val<k
      · simp only [if_pos hi, if_pos (show i.val<k+1 by omega), pmfKL_self]
      · simp only [if_neg hi, if_neg (show ¬i.val<k+1 by omega), pmfKL_self]
    · simp
  rw [he]
  exact firstOrderCoefficientLaw_pmfKL (Θ j) R hR

end
end SecondOrder

