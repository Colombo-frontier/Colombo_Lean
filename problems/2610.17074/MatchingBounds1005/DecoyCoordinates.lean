import MatchingBounds1005.DecoySmoothness
import MatchingBounds1005.IsometricTransfer
import MatchingBounds1005.SourceGeometry
import MatchingBounds1005.TensorSignals

/-! The actual copied-chain objective and deterministic source calendar in
the same Euclidean coordinates as the hidden tensor channels. -/
noncomputable section
open scoped InnerProductSpace ContDiff BigOperators

namespace MatchingBounds1005.BlockGeometry
open TensorGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def transportedReadout (n K : ℕ) (a : E) (A : ℝ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) (i : Fin (n + 1)) : Vec d :=
  I (decoyReadout n K a A i)

theorem transportedReadout_inner (n K : ℕ) (a : E) (A : ℝ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) (i : Fin (n + 1)) (x : Vec d) :
    ⟪transportedReadout n K a A I i, x⟫_ℝ = ⟪decoyReadout n K a A i, I.symm x⟫_ℝ :=
  I.inner_map_eq_flip _ _

theorem transportedReadout_orthonormal (n K : ℕ) {a : E} {A : ℝ}
    (hA : 0 < A) (ha : ‖a‖ = A) {d : ℕ} (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) :
    Orthonormal ℝ (transportedReadout n K a A I) :=
  (decoyReadout_orthonormal n K hA ha).comp_linearIsometry I.toLinearIsometry

variable (G : BlockGeometry E)

theorem transportedPotential_eq_ridge {A : ℝ} (hA : 0 < A) (r : ℝ) (n K : ℕ)
    {d : ℕ} (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) :
    IsometricTransfer.transport I (G.decoyPotential r n K) = fun x =>
      G.tau * ridgeSum (transportedReadout n K G.a A I) (Primitive.potential r) A x := by
  funext x
  change G.decoyPotential r n K (I.symm x) = _
  rw [G.decoyPotential_eq_ridge hA]
  simp only [ridgeSum, transportedReadout_inner]

/-- Full source objective, including every inactive copy, with exactly the
transported orthonormal readouts used by the cubic and quartic channels. -/
theorem transportedObjective_decomposition {A : ℝ} (hA : 0 < A) (r : ℝ) (n K : ℕ)
    {d : ℕ} (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) :
    IsometricTransfer.transport I (G.decoyObjective r n K) = fun x =>
      IsometricTransfer.transport I (G.decoyQuadratic n K) x +
        G.tau * ridgeSum (transportedReadout n K G.a A I) (Primitive.potential r) A x := by
  funext x
  change G.decoyObjective r n K (I.symm x) = _
  rw [G.decoyObjective_decomposition]
  change G.decoyQuadratic n K (I.symm x) + G.decoyPotential r n K (I.symm x) = _
  exact congrArg (fun v => G.decoyQuadratic n K (I.symm x) + v)
    (congrFun (G.transportedPotential_eq_ridge hA r n K I) x)

def transportedOperator (n K : ℕ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) : Vec d →L[ℝ] Vec d :=
  I.toContinuousLinearMap.comp ((G.copyOperator n K).comp I.symm.toContinuousLinearMap)

theorem transportedQuadratic_energy (n K : ℕ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) (x : Vec d) :
    IsometricTransfer.transport I (G.decoyQuadratic n K) x =
      (1 / 2 : ℝ) * ⟪x, G.transportedOperator n K I x⟫_ℝ +
        G.decoyLinear n K (I.symm x) := by
  change (1 / 2 : ℝ) * ⟪I.symm x, G.copyOperator n K (I.symm x)⟫_ℝ + _ = _
  rw [← I.inner_map_map (I.symm x) (G.copyOperator n K (I.symm x)), I.apply_symm_apply]
  rfl

theorem transportedObjective_tensor_decomposition {A : ℝ} (hA : 0 < A) (r : ℝ) (n K : ℕ)
    {d : ℕ} (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) (x : Vec d) :
    IsometricTransfer.transport I (G.decoyObjective r n K) x =
      IsometricTransfer.transport I (G.decoyQuadratic n K) x +
        mask (cubicSignal G.tau A (transportedReadout n K G.a A I))
          (quarticSignal G.tau A (transportedReadout n K G.a A I)) x +
        10 * G.tau * (n + 1) +
        G.tau * ridgeSum (transportedReadout n K G.a A I) (Primitive.correction r) A x := by
  rw [G.transportedObjective_decomposition hA]
  dsimp only
  rw [potential_tensor_decomposition]
  simp only [Fintype.card_fin]
  push_cast
  ring

end MatchingBounds1005.BlockGeometry

namespace MatchingBounds1005.PathLayers
open BlockGeometry PathGreen TensorGeometry

theorem normalizedBlockReadout_eq_smul (A : ℝ) (M n : ℕ) (s : Fin (n + 1)) :
    normalizedBlockReadout n (suffixVector A M) A s = A⁻¹ • blockVector M n s (suffixVector A M) := by
  ext i
  simp only [normalizedBlockReadout, blockVector, WithLp.equiv_symm_pi_apply, PiLp.smul_apply]
  by_cases hi : i = s
  · subst i
    simp
  · simp [Pi.single_eq_of_ne hi]

theorem transportedReadout_eq_ambientReadout (A : ℝ) (M n K : ℕ) (s : Fin (n + 1)) :
    transportedReadout n K (suffixVector A M) A (copyEuclideanIso n K).symm s =
      A⁻¹ • ambientReadout A M n K s := by
  unfold transportedReadout decoyReadout ambientReadout
  rw [normalizedBlockReadout_eq_smul, map_smul, map_smul]

theorem normalized_ambientReadout_hidden (A : ℝ) (M n K t : ℕ) (s : Fin (n + 1))
    (ht : t < (s.val + 1) * ((M + 2) / 2)) :
    transportedReadout n K (suffixVector A M) A (copyEuclideanIso n K).symm s ∈
      (ambientLayerSpace M n K ((M + 2) / 2) t)ᗮ := by
  rw [transportedReadout_eq_ambientReadout]
  exact Submodule.smul_mem _ _ (ambientReadout_hidden A M n K t s ht)

theorem normalized_ambientReadout_disclosed (A : ℝ) (M n K t : ℕ) (s : Fin (n + 1))
    (ht : (s.val + 1) * ((M + 2) / 2) ≤ t) :
    transportedReadout n K (suffixVector A M) A (copyEuclideanIso n K).symm s ∈
      ambientLayerSpace M n K ((M + 2) / 2) t := by
  rw [transportedReadout_eq_ambientReadout]
  exact Submodule.smul_mem _ _ (ambientReadout_disclosed A M n K t s ht)

theorem normalized_ambientReadout_mem_active (A : ℝ) (M n K : ℕ) (s : Fin (n + 1)) :
    transportedReadout n K (suffixVector A M) A (copyEuclideanIso n K).symm s ∈
      copyAmbientActiveSpace (E := EuclideanSpace ℝ (Fin (M + 1))) n K := by
  rw [transportedReadout_eq_ambientReadout]
  exact Submodule.smul_mem _ _ (ambientReadout_mem_active A M n K s)

end MatchingBounds1005.PathLayers
