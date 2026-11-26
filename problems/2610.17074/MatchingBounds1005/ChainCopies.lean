import MatchingBounds1005.ChainQuadratic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # The actual chain operator and its orthogonal decoy copies -/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.BlockGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def chainOperator (G : BlockGeometry E) (n : ℕ) : BlockSpace (E := E) n →L[ℝ] BlockSpace (E := E) n :=
  (InnerProductSpace.toDual ℝ (BlockSpace (E := E) n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (G.chainBilinear n)

theorem chainOperator_inner (G : BlockGeometry E) (n : ℕ) (z v : BlockSpace (E := E) n) :
    ⟪G.chainOperator n z, v⟫_ℝ = G.chainBilinear n z v :=
  InnerProductSpace.toDual_symm_apply

theorem chainOperator_symmetric (G : BlockGeometry E) (n : ℕ) :
    (G.chainOperator n).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪G.chainOperator n x, y⟫_ℝ = ⟪x, G.chainOperator n y⟫_ℝ
  rw [G.chainOperator_inner, real_inner_comm (G.chainOperator n y) x, G.chainOperator_inner,
    G.chainBilinear_symmetric]

abbrev CopySpace (n K : ℕ) := PiLp 2 (fun _ : Fin (K + 1) => BlockSpace (E := E) n)

def copyInsert (n K : ℕ) (j : Fin (K + 1)) :
    BlockSpace (E := E) n →ₗᵢ[ℝ] CopySpace (E := E) n K where
  toFun x := (WithLp.equiv 2 (Fin (K + 1) → BlockSpace (E := E) n)).symm (Pi.single j x)
  map_add' x y := by ext i : 1; simp [Pi.single_add]
  map_smul' c x := by ext i : 1; simp [Pi.single_smul]
  norm_map' x := PiLp.norm_equiv_symm_single 2 (fun _ : Fin (K + 1) => BlockSpace (E := E) n) j x

def activeInsert (n K : ℕ) : BlockSpace (E := E) n →ₗᵢ[ℝ] CopySpace (E := E) n K :=
  copyInsert n K 0

def activeSpace (n K : ℕ) : Submodule ℝ (CopySpace (E := E) n K) :=
  LinearMap.range (activeInsert (E := E) n K).toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem copyInsert_apply (n K : ℕ) (j i : Fin (K + 1)) (x : BlockSpace (E := E) n) :
    copyInsert n K j x i = (Pi.single j x : Fin (K + 1) → BlockSpace (E := E) n) i := rfl

omit [FiniteDimensional ℝ E] in
theorem copyInsert_inner (n K : ℕ) (j : Fin (K + 1))
    (x : BlockSpace (E := E) n) (z : CopySpace (E := E) n K) :
    ⟪copyInsert n K j x, z⟫_ℝ = ⟪x, z j⟫_ℝ := by
  simp only [PiLp.inner_apply, copyInsert_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_apply, hij]
  · simp

omit [FiniteDimensional ℝ E] in
theorem activeInsert_inner (n K : ℕ) (x : BlockSpace (E := E) n) (z : CopySpace (E := E) n K) :
    ⟪activeInsert n K x, z⟫_ℝ = ⟪x, z 0⟫_ℝ := copyInsert_inner n K 0 x z

def copyOperator (G : BlockGeometry E) (n K : ℕ) : CopySpace (E := E) n K →L[ℝ] CopySpace (E := E) n K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => (WithLp.equiv 2 _).symm (fun j => G.chainOperator n (z j))
      map_add' := by intro x y; ext j; simp [PiLp.add_apply]
      map_smul' := by intro c x; ext j; simp [PiLp.smul_apply] }

@[simp] theorem copyOperator_apply (G : BlockGeometry E) (n K : ℕ)
    (z : CopySpace (E := E) n K) (j : Fin (K + 1)) :
    G.copyOperator n K z j = G.chainOperator n (z j) := rfl

theorem copyOperator_inner (G : BlockGeometry E) (n K : ℕ)
    (z v : CopySpace (E := E) n K) :
    ⟪G.copyOperator n K z, v⟫_ℝ = ∑ j, G.chainBilinear n (z j) (v j) := by
  rw [PiLp.inner_apply]
  simp only [copyOperator_apply, G.chainOperator_inner]

theorem copyOperator_symmetric (G : BlockGeometry E) (n K : ℕ) :
    (G.copyOperator n K).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪G.copyOperator n K x, y⟫_ℝ = ⟪x, G.copyOperator n K y⟫_ℝ
  rw [G.copyOperator_inner, real_inner_comm (G.copyOperator n K y) x, G.copyOperator_inner]
  exact Finset.sum_congr rfl (fun j _ => G.chainBilinear_symmetric n _ _)

theorem copyOperator_copyInsert (G : BlockGeometry E) (n K : ℕ)
    (j : Fin (K + 1)) (x : BlockSpace (E := E) n) :
    G.copyOperator n K (copyInsert n K j x) = copyInsert n K j (G.chainOperator n x) := by
  ext i
  by_cases hij : i = j
  · subst i
    simp
  · simp [Pi.single_apply, hij]

theorem copyOperator_activeInsert (G : BlockGeometry E) (n K : ℕ) (x : BlockSpace (E := E) n) :
    G.copyOperator n K (activeInsert n K x) = activeInsert n K (G.chainOperator n x) :=
  copyOperator_copyInsert G n K 0 x

theorem activeSpace_invariant (G : BlockGeometry E) (n K : ℕ) :
    (activeSpace (E := E) n K).map (G.copyOperator n K).toLinearMap ≤ activeSpace n K := by
  rintro x ⟨z, ⟨v, rfl⟩, rfl⟩
  exact ⟨G.chainOperator n v, (G.copyOperator_activeInsert n K v).symm⟩

theorem copyOperator_norm_le (G : BlockGeometry E) (n K : ℕ) :
    ‖G.copyOperator n K‖ ≤ ‖G.chainOperator n‖ := by
  refine (G.copyOperator n K).opNorm_le_bound (by positivity) (fun z => ?_)
  have hsq : ‖G.copyOperator n K z‖ ^ 2 ≤ ‖G.chainOperator n‖ ^ 2 * ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [G.copyOperator_apply]
    have h := (G.chainOperator n).le_opNorm (z j)
    have hpos := mul_nonneg (norm_nonneg (G.chainOperator n)) (norm_nonneg (z j))
    nlinarith [norm_nonneg (G.chainOperator n (z j))]
  have hpos := mul_nonneg (norm_nonneg (G.chainOperator n)) (norm_nonneg z)
  nlinarith [norm_nonneg (G.copyOperator n K z)]

end MatchingBounds1005.BlockGeometry
