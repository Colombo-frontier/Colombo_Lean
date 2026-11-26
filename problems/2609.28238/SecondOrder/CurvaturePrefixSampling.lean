import SecondOrder.CurvatureHardFamily
import SecondOrder.FiniteConditionalEntropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

theorem pmfKL_finitePi_any_fintype {ι α : Type*} [Fintype ι] [Fintype α]
    (I : Fintype (ι → α)) (p q : ι → PMF α)
    (hp : ∀ i a, p i a≠0) (hq : ∀ i a, q i a≠0) :
    @pmfKL (ι → α) I (finitePiPMF p) (finitePiPMF q)=∑ i, pmfKL (p i) (q i) := by
  have he : I = @Pi.instFintype ι (fun _ => α) (Classical.decEq ι) inferInstance
      (fun _ => inferInstance) := Subsingleton.elim _ _
  rw [he]
  exact pmfKL_finitePi p q hp hq

def curvatureFairArray (m : ℕ) (R : ℝ) (hR : 2≤R) : PMF (UpperPair (2*m) → SignedCoefficient R) :=
  finitePiPMF (fun _ => fairCoefficientPMF R hR)

theorem curvatureFairArray_ne_zero (m : ℕ) (R : ℝ) (hR : 2≤R) :
    ∀ a, curvatureFairArray m R hR a≠0 :=
  finitePiPMF_ne_zero _ (fun _ => fairCoefficientPMF_ne_zero R hR)

theorem periodicCoefficientLaw_ne_zero (θ : BalancedVector m) (R : ℝ) (hR : 2≤R) :
    ∀ a, periodicCoefficientLaw θ.1 R hR a≠0 :=
  finitePiPMF_ne_zero _ (fun e => coefficientPMF_ne_zero R _ hR (pairSign_sq θ.1 e))

/-- Only the specified hidden prefix affects the sampling law. Unused future
arrays are filled with independent fair coefficients on the same support. -/
def curvaturePrefixArray (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (revealed : ℕ) (i : Fin (T+1)) : PMF (UpperPair (2*m) → SignedCoefficient R) :=
  if i.val<revealed then periodicCoefficientLaw (Θ i).1 R hR else curvatureFairArray m R hR

def curvaturePrefixCoefficientLaw (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (revealed : ℕ) : PMF (CurvatureCoefficients m T R) :=
  finitePiPMF (curvaturePrefixArray Θ R hR revealed)

theorem curvaturePrefixArray_ne_zero (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (revealed : ℕ) (i : Fin (T+1)) : ∀ a, curvaturePrefixArray Θ R hR revealed i a≠0 := by
  unfold curvaturePrefixArray
  split_ifs
  · exact periodicCoefficientLaw_ne_zero (Θ i) R hR
  · exact curvatureFairArray_ne_zero m R hR

theorem curvaturePrefixCoefficientLaw_ne_zero (Θ : Fin (T+1) → BalancedVector m)
    (R : ℝ) (hR : 2≤R) (revealed : ℕ) : ∀ z, curvaturePrefixCoefficientLaw Θ R hR revealed z≠0 :=
  finitePiPMF_ne_zero _ (curvaturePrefixArray_ne_zero Θ R hR revealed)

theorem curvaturePrefixCoefficientLaw_hidden_invariant (Θ Θ' : Fin (T+1) → BalancedVector m)
    (R : ℝ) (hR : 2≤R) (revealed : ℕ) (hΘ : ∀ i, i.val<revealed → Θ i=Θ' i) :
    curvaturePrefixCoefficientLaw Θ R hR revealed=curvaturePrefixCoefficientLaw Θ' R hR revealed := by
  unfold curvaturePrefixCoefficientLaw
  congr 1
  funext i
  unfold curvaturePrefixArray
  split_ifs with hi
  · rw [hΘ i hi]
  · rfl

theorem periodicCoefficientLaw_pmfKL (θ : BalancedVector m) (R : ℝ) (hR : 2≤R) :
    pmfKL (periodicCoefficientLaw θ.1 R hR) (curvatureFairArray m R hR)≤
      (((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2) := by
  unfold periodicCoefficientLaw curvatureFairArray
  rw [pmfKL_finitePi_any_fintype _ _ _
    (fun e => coefficientPMF_ne_zero R _ hR (pairSign_sq θ.1 e))
    (fun _ => fairCoefficientPMF_ne_zero R hR)]
  calc
    _ ≤ ∑ _ : UpperPair (2*m), 1/R^2 := Finset.sum_le_sum (fun e _ => by
      rw [pmfKL_coefficient]
      exact biased_sign_entropy hR (pairSign_sq θ.1 e))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, upperPair_card_real]; ring

/-- Enlarging the hidden prefix by one array costs only that array's entropy. -/
theorem curvaturePrefixCoefficientLaw_pmfKL (Θ : Fin (T+1) → BalancedVector m)
    (R : ℝ) (hR : 2≤R) {k : ℕ} (hk : k≤T) :
    pmfKL (curvaturePrefixCoefficientLaw Θ R hR (k+1)) (curvaturePrefixCoefficientLaw Θ R hR k)≤
      (((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2) := by
  unfold curvaturePrefixCoefficientLaw
  rw [pmfKL_finitePi_any_fintype _ _ _ (curvaturePrefixArray_ne_zero Θ R hR (k+1))
    (curvaturePrefixArray_ne_zero Θ R hR k)]
  let j : Fin (T+1) := ⟨k,by omega⟩
  have he : (∑ i, pmfKL (curvaturePrefixArray Θ R hR (k+1) i) (curvaturePrefixArray Θ R hR k i)) =
      pmfKL (periodicCoefficientLaw (Θ j).1 R hR) (curvatureFairArray m R hR) := by
    rw [Finset.sum_eq_single j]
    · simp [curvaturePrefixArray, j]
    · intro i _ hij
      have hne : i.val≠k := by intro h; apply hij; exact Fin.ext h
      unfold curvaturePrefixArray
      by_cases hi : i.val<k
      · simp only [if_pos hi, if_pos (show i.val<k+1 by omega), pmfKL_self]
      · simp only [if_neg hi, if_neg (show ¬i.val<k+1 by omega), pmfKL_self]
    · simp
  rw [he]
  exact periodicCoefficientLaw_pmfKL (Θ j) R hR

end
end SecondOrder
