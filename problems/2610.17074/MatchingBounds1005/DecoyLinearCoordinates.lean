import MatchingBounds1005.DecoyCoordinates

/-! The linear coefficient of the actual copied quadratic and its initial
calendar disclosure, in the same coordinates as the tensor reconstruction. -/
noncomputable section
open scoped InnerProductSpace BigOperators

namespace MatchingBounds1005.BlockGeometry
open TensorGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

def decoyLinearVector (n K : ℕ) : CopySpace (E := E) n K :=
  activeInsert n K ((WithLp.equiv 2 (Fin (n + 1) → E)).symm (Pi.single 0 (-G.lam • G.e)))

theorem decoyLinearVector_inner (n K : ℕ) (z : CopySpace (E := E) n K) :
    ⟪G.decoyLinearVector n K, z⟫_ℝ = G.decoyLinear n K z := by
  rw [decoyLinearVector, activeInsert_inner]
  simp only [PiLp.inner_apply, WithLp.equiv_symm_pi_apply]
  rw [Finset.sum_eq_single 0]
  · simp only [Pi.single_eq_same, real_inner_smul_left, decoyLinear,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      copyProjection, PiLp.proj_apply, firstEntry, innerSL_apply, smul_eq_mul]
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

def transportedLinearVector (n K : ℕ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) : Vec d := I (G.decoyLinearVector n K)

theorem transportedLinearVector_inner (n K : ℕ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) (x : Vec d) :
    ⟪G.transportedLinearVector n K I, x⟫_ℝ = G.decoyLinear n K (I.symm x) := by
  rw [transportedLinearVector, I.inner_map_eq_flip, G.decoyLinearVector_inner]

theorem transportedQuadratic_eq_energy (n K : ℕ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) :
    IsometricTransfer.transport I (G.decoyQuadratic n K) =
      SymmetricQuadratic.energy (G.transportedOperator n K I)
        (innerSL ℝ (G.transportedLinearVector n K I)) := by
  funext x
  rw [G.transportedQuadratic_energy]
  simp only [SymmetricQuadratic.energy, innerSL_apply, G.transportedLinearVector_inner]

theorem transportedOperator_symmetric (n K : ℕ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) (x y : Vec d) :
    ⟪x, G.transportedOperator n K I y⟫_ℝ = ⟪G.transportedOperator n K I x, y⟫_ℝ := by
  change ⟪x, I (G.copyOperator n K (I.symm y))⟫_ℝ =
    ⟪I (G.copyOperator n K (I.symm x)), y⟫_ℝ
  have hl : ⟪x, I (G.copyOperator n K (I.symm y))⟫_ℝ =
      ⟪I.symm x, G.copyOperator n K (I.symm y)⟫_ℝ := by
    simpa only [I.apply_symm_apply] using
      I.inner_map_map (I.symm x) (G.copyOperator n K (I.symm y))
  rw [hl, I.inner_map_eq_flip]
  exact G.copyOperator_pair_symmetric n K (I.symm x) (I.symm y)

end MatchingBounds1005.BlockGeometry

namespace MatchingBounds1005.PathLayers
open BlockGeometry PathGreen

theorem linearVector_initial_calendar (M n K : ℕ)
    (G : BlockGeometry (EuclideanSpace ℝ (Fin (M + 1)))) (he : G.e = entryVector M) :
    G.transportedLinearVector n K (copyEuclideanIso n K).symm ∈
      ambientLayerSpace M n K ((M + 2) / 2) 1 := by
  refine ⟨G.decoyLinearVector n K, ?_, rfl⟩
  unfold decoyLinearVector
  refine ⟨(WithLp.equiv 2 (Fin (n + 1) → EuclideanSpace ℝ (Fin (M + 1)))).symm
    (Pi.single 0 (-G.lam • G.e)), ?_, rfl⟩
  have heq : (WithLp.equiv 2 (Fin (n + 1) → EuclideanSpace ℝ (Fin (M + 1)))).symm
      (Pi.single 0 (-G.lam • G.e)) = -G.lam • blockVector M n 0 (entryVector M) := by
    ext i
    simp only [blockVector, WithLp.equiv_symm_pi_apply, PiLp.smul_apply, he]
    by_cases hi : i = 0
    · subst i; simp
    · simp [Pi.single_eq_of_ne hi]
  rw [heq]
  exact Submodule.smul_mem _ _ (initial_entry_disclosed M n)

theorem actual_linearVector_initial_calendar (L h A : ℝ) (hL : 0 < L) (hh : 0 < h)
    (hhsmall : h ≤ 1 / 4) (hA : 0 < A) (n K : ℕ) :
    (actualBlockGeometry L h A hL hh hhsmall hA).transportedLinearVector n K
      (copyEuclideanIso n K).symm ∈
        ambientLayerSpace (pathEdges h) n K ((pathEdges h + 2) / 2) 1 :=
  linearVector_initial_calendar _ _ _ _ rfl

end MatchingBounds1005.PathLayers
