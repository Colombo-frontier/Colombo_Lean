import FullJet.RowTranscriptInformation
import FullJet.ReferenceAlignment

open scoped BigOperators InnerProductSpace

namespace FullJet

def signedColumnCount {n D : ℕ} (k : ℕ) (theta : Fin D → Bool) (j : Fin D) : ℕ :=
  if theta j then k else n - k

theorem signedColumnCount_le {n D : ℕ} (k : ℕ) (hk : k ≤ n) (theta : Fin D → Bool) (j : Fin D) :
    signedColumnCount (n := n) k theta j ≤ n := by
  unfold signedColumnCount
  split_ifs
  · exact hk
  · exact Nat.sub_le _ _

theorem signedColumnCount_balance {n D : ℕ} (k : ℕ) (hk : k ≤ n)
    (m : ℝ) (hbalance : 2 * (k : ℝ) = n + m) (theta : Fin D → Bool) (j : Fin D) :
    2 * (signedColumnCount (n := n) k theta j : ℝ) = n + m * rareSign (theta j) := by
  cases hb : theta j <;> simp only [signedColumnCount, hb, Bool.false_eq_true,
    if_false, if_true, rareSign, Nat.cast_sub hk] <;> linarith

noncomputable def signedRowTranscriptLaw {n D : ℕ} (k : ℕ) (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (theta : Fin D → Bool) : PMF (Fin q → Fin D → Bool) :=
  (vectorColumnLaw Finset.univ (signedColumnCount (n := n) k theta)
    (fun j => by simpa using signedColumnCount_le k hk theta j)).map
      (fun S => runReplies (fun S hist j => decide (ask hist ∈ S j)) S past q)

noncomputable def signedRowTranscriptWeight {n D : ℕ} (k : ℕ) (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (theta : Fin D → Bool) (v : Fin q → Fin D → Bool) : ℝ :=
  (signedRowTranscriptLaw k hk ask past q theta v).toReal

theorem signedRowTranscript_information {n D : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n) (theta theta' : Fin D → Bool) :
    (∀ v, signedRowTranscriptWeight k hk ask past q theta v ≠ 0 →
      signedRowTranscriptWeight k hk ask past q theta' v ≠ 0) ∧
    finiteKL (signedRowTranscriptWeight k hk ask past q theta)
      (signedRowTranscriptWeight k hk ask past q theta') ≤ 32 * q * D * (m / n) ^ 2 := by
  have ht (t : Fin D → Bool) (j : Fin D) : rareSign (t j) = -1 ∨ rareSign (t j) = 1 := by
    cases t j <;> simp [rareSign]
  constructor
  · exact vectorRowTranscript_support hn _ _ (signedColumnCount_le k hk theta)
      (signedColumnCount_le k hk theta') m hm (fun j => rareSign (theta j))
      (fun j => rareSign (theta' j)) (ht theta) (ht theta')
      (signedColumnCount_balance k hk m hbalance theta)
      (signedColumnCount_balance k hk m hbalance theta') ask past q hbudget
  · exact vectorRowTranscript_kl_le hn _ _ (signedColumnCount_le k hk theta)
      (signedColumnCount_le k hk theta') m hm (fun j => rareSign (theta j))
      (fun j => rareSign (theta' j)) (ht theta) (ht theta')
      (signedColumnCount_balance k hk m hbalance theta)
      (signedColumnCount_balance k hk m hbalance theta') ask past q hbudget

/-- Choose uniform hidden signs, then run the actual adaptive strategy on
independent uniform fixed-size columns with the corresponding signed bias. -/
noncomputable def rowJointWeight {n D : ℕ} (k : ℕ) (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (z : (Fin D → Bool) × (Fin q → Fin D → Bool)) : ℝ :=
  cubeWeight z.1 * signedRowTranscriptWeight k hk ask past q z.1 z.2

theorem rowJointWeight_nonneg {n D : ℕ} (k : ℕ) (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (z : (Fin D → Bool) × (Fin q → Fin D → Bool)) : 0 ≤ rowJointWeight k hk ask past q z :=
  mul_nonneg (cubeWeight_nonneg _) ENNReal.toReal_nonneg

theorem rowJointWeight_sum {n D : ℕ} (k : ℕ) (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ) :
    ∑ z, rowJointWeight k hk ask past q z = 1 := by
  unfold rowJointWeight signedRowTranscriptWeight
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, pmf_toReal_sum, mul_one]
  exact cubeWeight_sum D

theorem rowJointWeight_reference_information {n D : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n) (theta0 : Fin D → Bool) :
    (∀ z, rowJointWeight k hk ask past q z ≠ 0 →
      independentReference (signedRowTranscriptWeight k hk ask past q theta0) z ≠ 0) ∧
    finiteKL (rowJointWeight k hk ask past q)
      (independentReference (signedRowTranscriptWeight k hk ask past q theta0)) ≤
      32 * q * D * (m / n) ^ 2 := by
  have hinfo := fun theta => signedRowTranscript_information hn k hk m hm hbalance
    ask past q hbudget theta theta0
  constructor
  · intro z hz
    obtain ⟨ht, hv⟩ := mul_ne_zero_iff.mp hz
    exact mul_ne_zero ht ((hinfo z.1).1 z.2 hv)
  · unfold rowJointWeight independentReference
    rw [finiteKL_chain_rule cubeWeight cubeWeight
      (signedRowTranscriptWeight k hk ask past q)
      (fun _ => signedRowTranscriptWeight k hk ask past q theta0)
      (fun theta => pmf_toReal_sum (signedRowTranscriptLaw k hk ask past q theta))
      (fun _ h => h) (fun theta _ => (hinfo theta).1), finiteKL_self, zero_add]
    calc
      _ ≤ ∑ theta : Fin D → Bool, cubeWeight theta * (32 * q * D * (m / n) ^ 2) :=
        Finset.sum_le_sum (fun theta _ => mul_le_mul_of_nonneg_left
          (hinfo theta).2 (cubeWeight_nonneg theta))
      _ = _ := by rw [← Finset.sum_mul, cubeWeight_sum, one_mul]

/-- A concrete one-stage alignment bound for every finite family of unit
directions selected from the entire adaptive row transcript. -/
theorem adaptive_row_alignment_bound {n D : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (k : ℕ) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n)
    (w : (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ v l, ‖w v l‖ ≤ 1) (a B : ℝ) (ha : 0 ≤ a) (hB : 0 < B)
    (hrare : Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) ≤ Real.exp (-B)) :
    (∑ z ∈ Finset.univ.filter (fun z : (Fin D → Bool) × (Fin q → Fin D → Bool) =>
      ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (z.1 j)), w z.2 l⟫_ℝ), rowJointWeight k hk ask past q z) ≤
      (32 * q * D * (m / n) ^ 2 + Real.log 2) / B := by
  classical
  let theta0 : Fin D → Bool := fun _ => false
  have hinfo := rowJointWeight_reference_information hn k hk m hm hbalance ask past q hbudget theta0
  have h := alignment_probability_from_information D (rowJointWeight k hk ask past q)
    (signedRowTranscriptWeight k hk ask past q theta0)
    (rowJointWeight_nonneg k hk ask past q) (rowJointWeight_sum k hk ask past q)
    (fun _ => ENNReal.toReal_nonneg) (pmf_toReal_sum (signedRowTranscriptLaw k hk ask past q theta0))
    hinfo.1 w hw a B ha hD hB hrare
  exact h.trans (div_le_div_of_nonneg_right (add_le_add_right hinfo.2 _) hB.le)

/-- With explicit dimension and query budgets, the probability that any of
the transcript-dependent directions aligns is at most one quarter. -/
theorem adaptive_row_alignment_quarter {n D : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (k : ℕ) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n)
    (w : (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ v l, ‖w v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q : ℝ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4)) :
    (∑ z ∈ Finset.univ.filter (fun z : (Fin D → Bool) × (Fin q → Fin D → Bool) =>
      ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (z.1 j)), w z.2 l⟫_ℝ), rowJointWeight k hk ask past q z) ≤
      1 / 4 := by
  classical
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hB : 0 < a ^ 2 * D / 4 := by positivity
  have hrare : Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) ≤ Real.exp (-(a ^ 2 * D / 4)) := by
    calc
      _ ≤ Real.exp (a ^ 2 * D / 4) * Real.exp (-(a ^ 2 * D / 2)) :=
        mul_le_mul_of_nonneg_right hfamily (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h := adaptive_row_alignment_bound hn hD k hk m hm hbalance ask past q hbudget w hw
    a (a ^ 2 * D / 4) ha.le hB hrare
  apply h.trans
  apply (div_le_iff₀ hB).mpr
  have hqD := mul_le_mul_of_nonneg_right hqueries hD'.le
  nlinarith

/-- A one-stage row-cost lower bound with explicit constants. The dimension
conditions control the finite family of attempted alignment directions. -/
theorem adaptive_row_cost_lower {n D : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (k : ℕ) (hk : k ≤ n)
    (m : ℝ) (hm : 0 < m) (hmn : m ≤ (n : ℝ) / 16)
    (hbalance : 2 * (k : ℝ) = n + m)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (w : (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ v l, ‖w v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4))
    (hsuccess : 1 / 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : (Fin D → Bool) × (Fin q → Fin D → Bool) =>
        ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (z.1 j)), w z.2 l⟫_ℝ), rowJointWeight k hk ask past q z) :
    min ((n : ℝ) / 18) (a ^ 2 / (1024 * (m / n) ^ 2)) < q := by
  classical
  by_contra h
  have hq : (q : ℝ) ≤ min ((n : ℝ) / 18) (a ^ 2 / (1024 * (m / n) ^ 2)) := le_of_not_gt h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hqN := hq.trans (min_le_left _ _)
  have hqM := hq.trans (min_le_right _ _)
  have hbudget : 8 * m + 9 * (q : ℝ) ≤ n := by linarith
  have hden : 0 < 1024 * (m / n) ^ 2 := by positivity
  have hqueries : (q : ℝ) * (m / n) ^ 2 ≤ a ^ 2 / 1024 := by
    have hmul := (le_div_iff₀ hden).mp hqM
    nlinarith
  have hfail := adaptive_row_alignment_quarter hn hD k hk m hm.le hbalance ask past q hbudget
    w hw a ha hqueries hdim hfamily
  linarith

end FullJet
