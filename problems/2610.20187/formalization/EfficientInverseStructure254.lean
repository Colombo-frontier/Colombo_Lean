import EfficientInverse254

open Matrix
namespace Paper254

def schurTailIndex (n : ℕ) (i : Fin n) : Fin (n+1) := inverseSplit n (Sum.inr i)

theorem schurTailIndex_injective (n : ℕ) : Function.Injective (schurTailIndex n) := by
  intro i j h
  exact Sum.inr_injective ((inverseSplit n).injective h)

/-- Eliminating a pivot does not enlarge the inverse entries: the next inverse
is exactly a principal block of the current inverse. -/
theorem inverseSchur_inv_submatrix {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hA : A.PosDef) :
    (inverseSchur A)⁻¹=A⁻¹.submatrix (schurTailIndex n) (schurTailIndex n) := by
  have he := inverseAssemble_correct A hA
  ext i j
  have hi := congrArg (fun M=>M (schurTailIndex n i) (schurTailIndex n j)) he
  simpa [inverseAssemble,schurTailIndex,Matrix.reindex_apply] using hi

/-- Matrices visited by the single recursive Schur chain. -/
inductive SchurDescendant {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) :
    {n : ℕ}→Matrix (Fin n) (Fin n) ℚ→Prop
  | root : SchurDescendant A A
  | tail {n : ℕ} {B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ} :
      SchurDescendant A B→SchurDescendant A (inverseSchur B)

theorem SchurDescendant.posDef {d : ℕ} {A : Matrix (Fin d) (Fin d) ℚ}
    (hA : A.PosDef) {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB : SchurDescendant A B) : B.PosDef := by
  induction hB with
  | root => exact hA
  | tail h ih => exact inverseSchur_pos _ ih

/-- Every inverse returned during the recursion is a principal submatrix of
the original inverse. This invariant avoids exponential height recurrences. -/
theorem SchurDescendant.inverse_submatrix {d : ℕ} {A : Matrix (Fin d) (Fin d) ℚ}
    (hA : A.PosDef) {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB : SchurDescendant A B) :
    ∃ e : Fin n→Fin d,Function.Injective e ∧ B⁻¹=A⁻¹.submatrix e e := by
  induction hB with
  | root => exact ⟨id,Function.injective_id,rfl⟩
  | @tail n B h ih =>
    obtain ⟨e,he,hinv⟩ := ih
    refine ⟨e ∘ schurTailIndex n,he.comp (schurTailIndex_injective n),?_⟩
    rw [inverseSchur_inv_submatrix B (h.posDef hA),hinv]
    rfl

theorem SchurDescendant.dimension_le {d : ℕ} {A : Matrix (Fin d) (Fin d) ℚ}
    (hA : A.PosDef) {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    (hB : SchurDescendant A B) : n≤d := by
  obtain ⟨e,he,_⟩ := hB.inverse_submatrix hA
  simpa using Fintype.card_le_of_injective e he

/-- Each intermediate input is an inverse of a principal block of the
original inverse. Thus a generic inverse encoding bound is needed only twice,
independently of the number of elimination stages. -/
theorem SchurDescendant.input_inverse_submatrix {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℚ} (hA : A.PosDef) {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℚ} (hB : SchurDescendant A B) :
    ∃ e : Fin n→Fin d,Function.Injective e ∧ B=(A⁻¹.submatrix e e)⁻¹ := by
  obtain ⟨e,he,hinv⟩ := hB.inverse_submatrix hA
  refine ⟨e,he,?_⟩
  rw [←hinv]
  letI := (hB.posDef hA).isUnit.invertible
  exact (Matrix.inv_inv_of_invertible B).symm

end Paper254
#print axioms Paper254.SchurDescendant.inverse_submatrix
#print axioms Paper254.SchurDescendant.input_inverse_submatrix
