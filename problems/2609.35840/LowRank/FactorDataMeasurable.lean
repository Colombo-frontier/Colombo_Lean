import LowRank.FactorData

/-! The complete factor-state update is measurable, and preserves both-sided
orthogonality of the cumulative ambient bases. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def FactorData.Orthogonal {d t q r s : ℕ} (st : FactorData d t q r s) : Prop :=
  st.2.1ᵀ * st.2.1 = 1 ∧ st.2.1 * st.2.1ᵀ = 1 ∧
    st.2.2ᵀ * st.2.2 = 1 ∧ st.2.2 * st.2.2ᵀ = 1

theorem measurable_extendGauge {a b : Type*} [DecidableEq a] :
    Measurable (extendGauge (a := a) (b := b)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  cases i <;> cases j <;> simp only [extendGauge, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂] <;> fun_prop

theorem measurable_changedBasis {S m n o : Type*} [MeasurableSpace S] [Fintype n]
    (B : S → Matrix m n ℝ) (L : S → Matrix n n ℝ) (e : o ≃ n)
    (hB : Measurable B) (hL : Measurable L) :
    Measurable (fun st => changedBasis (B st) (L st) e) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable (fun st => ∑ k, B st i k * L st (e j) k)
  fun_prop

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}

theorem updateFactorData_orthogonal (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (st : FactorData d t q (r + 1) (s + 1))
    (exposed : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) (h : st.Orthogonal) :
    (updateFactorData b c u st exposed).Orthogonal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact changedBasis_transpose_mul _ _ _ h.1
      (extendGauge_mul_transpose _ (gaugeMatrix_mul_transpose_self b _))
  · exact changedBasis_mul_transpose _ _ _ h.2.1
      (extendGauge_transpose_mul _ (gaugeMatrix_transpose_mul_self b _))
  · exact changedBasis_transpose_mul _ _ _ h.2.2.1
      (extendGauge_mul_transpose _ (gaugeMatrix_mul_transpose_self c _))
  · exact changedBasis_mul_transpose _ _ _ h.2.2.2
      (extendGauge_transpose_mul _ (gaugeMatrix_transpose_mul_self c _))

theorem measurable_updateFactorData {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : S → Fin (r + 1) → ℝ) (st : S → FactorData d t q (r + 1) (s + 1))
    (exposed : S → (Fin (s + 1) → ℝ) × (Fin r → ℝ))
    (hu : Measurable u) (hst : Measurable st) (he : Measurable exposed) :
    Measurable (fun x => updateFactorData b c (u x) (st x) (exposed x)) := by
  have hG : Measurable (fun x => gaugeMatrix b (rowGauge b (u x))) :=
    (measurable_rowGauge_matrix b).comp hu
  have hC : Measurable (fun x => rotateMatrixColumns b (rowGauge b (u x)) (st x).1.2) := by
    simp only [rotateMatrixColumns_eq_mul]
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply]
    fun_prop
  have hρ : Measurable (fun x => ‖(basisCoordinates c).symm (exposed x).1‖) :=
    ((basisCoordinates c).symm.continuous.measurable.comp he.fst).norm
  have hL : Measurable (fun x => extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b (u x)))) :=
    measurable_extendGauge.comp hG
  have hR : Measurable (fun x => extendGauge (a := Fin q)
      (gaugeMatrix c (rowGauge c (exposed x).1))) :=
    measurable_extendGauge.comp ((measurable_rowGauge_matrix c).comp he.fst)
  exact ((measurable_nextExposedA _ _ _ hst.fst.fst hC hρ).prodMk
    (measurable_nextExposedC _ _ hC he.snd)).prodMk
      ((measurable_changedBasis _ _ _ hst.snd.fst hL).prodMk
        (measurable_changedBasis _ _ _ hst.snd.snd hR))

end
end LowRank
