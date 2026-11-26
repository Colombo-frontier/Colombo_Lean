import NCConcave16991.DenseSmoothConstruction
import NCConcave16991.DenseWeakBiasColumn

/-! # Actual static sign tables, normalized unit rows and their exact hidden mean -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open DenseWeakHiding
open scoped BigOperators InnerProductSpace

set_option maxHeartbeats 600000

def signVector {D : ℕ} (s : Fin D → ℝ) : EuclideanSpace ℝ (Fin D) := WithLp.toLp 2 s

def normalizedSignVector {D : ℕ} (s : Fin D → ℝ) : EuclideanSpace ℝ (Fin D) :=
  (Real.sqrt (D : ℝ))⁻¹ • signVector s

theorem signVector_norm {D : ℕ} (s : Fin D → ℝ) (hs : ∀ l, s l ^ 2 = 1) :
    ‖signVector s‖ = Real.sqrt (D : ℝ) := by
  have hh : ‖signVector s‖ ^ 2 = (D : ℝ) := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [signVector, Real.norm_eq_abs, sq_abs, hs, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg D : (0 : ℝ) ≤ D),
    Real.sqrt_nonneg (D : ℝ), norm_nonneg (signVector s)]

theorem normalizedSignVector_unit {D : ℕ} (hD : 0 < D) (s : Fin D → ℝ) (hs : ∀ l, s l ^ 2 = 1) :
    ‖normalizedSignVector s‖ = 1 := by
  have hroot : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  rw [normalizedSignVector, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hroot), signVector_norm s hs,
    inv_mul_cancel₀ hroot.ne']

def signDirection {n m D T : ℕ} (bank : Fin (T + 1) → Fin D → EncodedColumn n m)
    (j : Fin (T + 1)) : EuclideanSpace ℝ (Fin D) :=
  normalizedSignVector (fun l ↦ hiddenSign (bank j l).1)

def signRow {n m D T : ℕ} (bank : Fin (T + 1) → Fin D → EncodedColumn n m)
    (i : Fin n) (j : Fin (T + 1)) : EuclideanSpace ℝ (Fin D) :=
  normalizedSignVector (fun l ↦ columnSign (bank j l).2.val i)

theorem signDirection_unit {n m D T : ℕ} (hD : 0 < D)
    (bank : Fin (T + 1) → Fin D → EncodedColumn n m) (j : Fin (T + 1)) :
    ‖signDirection bank j‖ = 1 :=
  normalizedSignVector_unit hD _ (fun l ↦ hiddenSign_sq _)

theorem signRow_unit {n m D T : ℕ} (hD : 0 < D)
    (bank : Fin (T + 1) → Fin D → EncodedColumn n m) (i : Fin n) (j : Fin (T + 1)) :
    ‖signRow bank i j‖ = 1 :=
  normalizedSignVector_unit hD _ (fun l ↦ columnSign_sq _ i)

theorem signRow_sum {n m D T : ℕ} (hn : 0 < n) (hm : m ≤ n) (hparity : m % 2 = n % 2)
    (bank : Fin (T + 1) → Fin D → EncodedColumn n m) (j : Fin (T + 1)) :
    ∑ i, signRow bank i j = ((n : ℝ) * ((m : ℝ) / n)) • signDirection bank j := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  ext l
  have he := map_sum (show EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ from
    PiLp.proj 2 (fun _ : Fin D ↦ ℝ) l) (fun i ↦ signRow bank i j) Finset.univ
  change (∑ i, signRow bank i j).ofLp l = ∑ i, (signRow bank i j).ofLp l at he
  rw [he]
  change (∑ i, (Real.sqrt (D : ℝ))⁻¹ * columnSign (bank j l).2.val i) =
    ((n : ℝ) * ((m : ℝ) / n)) * ((Real.sqrt (D : ℝ))⁻¹ * hiddenSign (bank j l).1)
  rw [← Finset.mul_sum, biasedColumn_sign_sum hm hparity]
  field_simp

def signTable {n m D T : ℕ} (hn : 0 < n) (hD : 0 < D)
    (hm : m ≤ n) (hparity : m % 2 = n % 2)
    (bank : Fin (T + 1) → Fin D → EncodedColumn n m) :
    Table (EuclideanSpace ℝ (Fin D)) n T ((m : ℝ) / n) where
  direction := signDirection bank
  row := signRow bank
  direction_unit := signDirection_unit hD bank
  row_unit := signRow_unit hD bank
  row_sum := signRow_sum hn hm hparity bank

end NCConcave16991.DenseSmooth
