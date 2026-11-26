import NCConcave16991.DenseWeakProductBank
import NCConcave16991.DenseWeakAlignment
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Actual finite independent stage banks and coordinatewise event bounds -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {I : Type*} [Fintype I] {M : ℕ}

theorem pi_insertNth_mass (P : Fin (M + 1) → FiniteLaw I) (j : Fin (M + 1))
    (a : I) (others : Fin M → I) :
    (pi P).mass (Fin.insertNth j a others) =
      (P j).mass a * (pi (fun i ↦ P (j.succAbove i))).mass others := by
  simp only [pi]
  rw [Fin.prod_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]

/-- Fubini's identity for the actual finite product bank, with every other
static stage held fixed. -/
theorem pi_coordinate_eventMass (P : Fin (M + 1) → FiniteLaw I) (j : Fin (M + 1))
    (E : Set (Fin (M + 1) → I)) :
    (pi P).eventMass E = ∑ others : Fin M → I,
      (pi (fun i ↦ P (j.succAbove i))).mass others *
        (P j).eventMass {a | Fin.insertNth j a others ∈ E} := by
  have he : (pi P).eventMass E =
      ∑ z : I × (Fin M → I),
        if Fin.insertNth j z.1 z.2 ∈ E then
          (P j).mass z.1 * (pi (fun i ↦ P (j.succAbove i))).mass z.2 else 0 := by
    symm
    apply Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (M + 1) ↦ I) j)
    intro z
    change (if Fin.insertNth j z.1 z.2 ∈ E then
      (P j).mass z.1 * (pi (fun i ↦ P (j.succAbove i))).mass z.2 else 0) =
        (if Fin.insertNth j z.1 z.2 ∈ E then (pi P).mass (Fin.insertNth j z.1 z.2) else 0)
    rw [pi_insertNth_mass]
  rw [he,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro others _
  rw [eventMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : Fin.insertNth j a others ∈ E <;> simp [h,mul_comm]

theorem pi_coordinate_event_bound (P : Fin (M + 1) → FiniteLaw I) (j : Fin (M + 1))
    (E : Set (Fin (M + 1) → I)) (b : ℝ)
    (hb : ∀ others : Fin M → I, (P j).eventMass {a | Fin.insertNth j a others ∈ E} ≤ b) :
    (pi P).eventMass E ≤ b := by
  rw [pi_coordinate_eventMass P j E]
  calc
    _ ≤ ∑ others, (pi (fun i ↦ P (j.succAbove i))).mass others * b := by
      exact Finset.sum_le_sum (fun others _ ↦
        mul_le_mul_of_nonneg_left (hb others) ((pi (fun i ↦ P (j.succAbove i))).nonneg others))
    _ = b := by rw [← Finset.sum_mul,(pi (fun i ↦ P (j.succAbove i))).sum_one,one_mul]

end NCConcave16991.DenseWeakHiding.FiniteLaw

namespace NCConcave16991.DenseWeakHiding

abbrev StageBank (n m D stages : ℕ) := Fin stages → ColumnBank n m D

def stageBankLaw (n m D stages : ℕ) (hm : m ≤ n) : FiniteLaw (StageBank n m D stages) :=
  FiniteLaw.pi (fun _ ↦ columnBankLaw n m D hm)

theorem stageBank_coordinate_event_bound {n m D M : ℕ} (hm : m ≤ n) (j : Fin (M + 1))
    (E : Set (StageBank n m D (M + 1))) (b : ℝ)
    (hb : ∀ others : StageBank n m D M,
      (columnBankLaw n m D hm).eventMass {a | Fin.insertNth j a others ∈ E} ≤ b) :
    (stageBankLaw n m D (M + 1) hm).eventMass E ≤ b :=
  FiniteLaw.pi_coordinate_event_bound _ j E b hb

end NCConcave16991.DenseWeakHiding
