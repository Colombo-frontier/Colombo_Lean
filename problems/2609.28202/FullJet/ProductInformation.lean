import FullJet.TranscriptInformation
import FullJet.UniformProduct

open scoped BigOperators

namespace FullJet

noncomputable def finiteProductWeight {ι β : Type*} [Fintype ι] (p : ι → β → ℝ)
    (v : ι → β) : ℝ := ∏ j, p j (v j)

theorem finiteProductWeight_sum {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (p : ι → β → ℝ) (hp : ∀ j, ∑ b, p j b = 1) :
    ∑ v, finiteProductWeight p v = 1 := by
  classical
  unfold finiteProductWeight
  have h := Finset.sum_prod_piFinset (ι := ι) (Finset.univ : Finset β) p
  simpa only [Fintype.piFinset_univ, hp, Finset.prod_const_one] using h

theorem finiteProductWeight_support {ι β : Type*} [Fintype ι]
    (p q : ι → β → ℝ) (hpq : ∀ j b, p j b ≠ 0 → q j b ≠ 0)
    (v : ι → β) (hv : finiteProductWeight p v ≠ 0) : finiteProductWeight q v ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun j hj => hpq j (v j) (Finset.prod_ne_zero_iff.mp hv j hj)

/-- Relative entropy of a finite vector of independent coordinates is the
sum of the coordinate relative entropies. Zeros are allowed. -/
theorem finiteKL_pi {β : Type*} [Fintype β] (D : ℕ) (p q : Fin D → β → ℝ)
    (hp : ∀ j, ∑ b, p j b = 1) (hpq : ∀ j b, p j b ≠ 0 → q j b ≠ 0) :
    finiteKL (finiteProductWeight p) (finiteProductWeight q) = ∑ j, finiteKL (p j) (q j) := by
  induction D with
  | zero => simp [finiteProductWeight, finiteKL]
  | succ D ih =>
    let pt := fun j : Fin D => p j.succ
    let qt := fun j : Fin D => q j.succ
    have heq : finiteKL (finiteProductWeight p) (finiteProductWeight q) =
        finiteKL (fun z : β × (Fin D → β) => p 0 z.1 * finiteProductWeight pt z.2)
          (fun z => q 0 z.1 * finiteProductWeight qt z.2) := by
      unfold finiteKL
      apply Fintype.sum_equiv (transcriptSplit D)
      intro v
      simp only [finiteProductWeight, Fin.prod_univ_succ, transcriptSplit, Equiv.coe_fn_mk,
        Fin.tail, pt, qt]
    rw [heq, finiteKL_product _ _ _ _ (hp 0)
      (finiteProductWeight_sum pt (fun j => hp j.succ)) (hpq 0)
      (finiteProductWeight_support pt qt (fun j => hpq j.succ))]
    rw [ih pt qt (fun j => hp j.succ) (fun j => hpq j.succ), Fin.sum_univ_succ]

def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

theorem bitWeight_sum (p : ℝ) : ∑ b, bitWeight p b = 1 := by simp [bitWeight]

theorem bitWeight_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (b : Bool) : 0 < bitWeight p b := by
  cases b <;> simp [bitWeight] <;> linarith

theorem finiteKL_bitWeight (p q : ℝ) : finiteKL (bitWeight p) (bitWeight q) = bernoulliKL p q := by
  simp [finiteKL, bitWeight, bernoulliKL]

/-- Coordinate information bounds sum across a complete Bernoulli row. -/
theorem bernoulliProduct_kl_le (D : ℕ) (p q : Fin D → ℝ)
    (hq : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (c : ℝ) (hstep : ∀ j, bernoulliKL (p j) (q j) ≤ c) :
    finiteKL (finiteProductWeight (fun j => bitWeight (p j)))
      (finiteProductWeight (fun j => bitWeight (q j))) ≤ D * c := by
  rw [finiteKL_pi D _ _ (fun j => bitWeight_sum (p j))
    (fun j b _ => (bitWeight_pos (q j) (hq j) (hq1 j) b).ne')]
  simp_rw [finiteKL_bitWeight]
  calc
    ∑ j, bernoulliKL (p j) (q j) ≤ ∑ _ : Fin D, c := Finset.sum_le_sum (fun j _ => hstep j)
    _ = D * c := by simp

theorem nextSignProbability_kl_bound_pair (n m d s theta theta' : ℝ)
    (hn : 0 < n) (hm : 0 ≤ m) (hd : 0 ≤ d) (hs : -d ≤ s ∧ s ≤ d)
    (htheta : theta = -1 ∨ theta = 1) (htheta' : theta' = -1 ∨ theta' = 1)
    (hbudget : 8 * m + 9 * d ≤ n) :
    bernoulliKL (nextSignProbability n m d s theta) (nextSignProbability n m d s theta') ≤
      32 * (m / n) ^ 2 := by
  have hp := nextSignProbability_bounds n m d s theta hn hm hd hs htheta hbudget
  have hq := nextSignProbability_bounds n m d s theta' hn hm hd hs htheta' hbudget
  have h := bernoulliKL_le_eight_sq (nextSignProbability n m d s theta)
    (nextSignProbability n m d s theta') (by linarith [hp.1]) (by linarith [hp.2])
    (by linarith [hq.1]) (by linarith [hq.2])
  have hdiff : (nextSignProbability n m d s theta - nextSignProbability n m d s theta') ^ 2 ≤
      (m / (n - d)) ^ 2 := by
    rcases htheta with rfl | rfl <;> rcases htheta' with rfl | rfl
    · simpa using sq_nonneg (m / (n - d))
    · rw [show (nextSignProbability n m d s (-1) - nextSignProbability n m d s 1) ^ 2 =
        (nextSignProbability n m d s 1 - nextSignProbability n m d s (-1)) ^ 2 by ring,
        nextSignProbability_difference]
    · rw [nextSignProbability_difference]
    · simpa using sq_nonneg (m / (n - d))
  have hnd : 0 < n - d := by linarith
  have hratio0 : 0 ≤ m / (n - d) := div_nonneg hm hnd.le
  have hratio : m / (n - d) ≤ 2 * (m / n) := by
    calc
      m / (n - d) ≤ (2 * m) / n := (div_le_div_iff₀ hnd hn).mpr (by
        nlinarith [mul_nonneg hm (show 0 ≤ n - 2 * d by linarith)])
      _ = 2 * (m / n) := by ring
  have hm0 : 0 ≤ m / n := div_nonneg hm hn.le
  nlinarith [sq_nonneg (m / (n - d) - 2 * (m / n))]

/-- For the product next-row probabilities, any two possible hidden sign
vectors differ by at most `32 D rho^2` in relative entropy. -/
theorem nextRow_kl_bound (D : ℕ) (n m d : ℝ) (s theta theta' : Fin D → ℝ)
    (hn : 0 < n) (hm : 0 ≤ m) (hd : 0 ≤ d) (hs : ∀ j, -d ≤ s j ∧ s j ≤ d)
    (htheta : ∀ j, theta j = -1 ∨ theta j = 1)
    (htheta' : ∀ j, theta' j = -1 ∨ theta' j = 1) (hbudget : 8 * m + 9 * d ≤ n) :
    finiteKL
      (finiteProductWeight (fun j => bitWeight (nextSignProbability n m d (s j) (theta j))))
      (finiteProductWeight (fun j => bitWeight (nextSignProbability n m d (s j) (theta' j)))) ≤
      32 * D * (m / n) ^ 2 := by
  have hbounds := fun j => nextSignProbability_bounds n m d (s j) (theta' j)
    hn hm hd (hs j) (htheta' j) hbudget
  have h := bernoulliProduct_kl_le D _ _
    (fun j => by linarith [(hbounds j).1]) (fun j => by linarith [(hbounds j).2])
    (32 * (m / n) ^ 2)
    (fun j => nextSignProbability_kl_bound_pair n m d (s j) (theta j) (theta' j)
      hn hm hd (hs j) (htheta j) (htheta' j) hbudget)
  convert h using 1 <;> ring

end FullJet
