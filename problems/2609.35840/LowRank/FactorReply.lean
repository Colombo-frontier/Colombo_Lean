import LowRank.FactorVisibleRecovery

/-! Decode an actual ambient Gram reply from the old visible factors and
the newly exposed row/column. Together with visible recovery this connects
the Gaussian revelation step to an oracle transcript in both directions. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem representedMatrix_reply {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (z : Fin q ⊕ Fin r → ℝ)
    (hB : st.2.1ᵀ * st.2.1 = 1) (hV : st.2.2ᵀ * st.2.2 = 1) :
    (representedMatrix st D * (representedMatrix st D)ᵀ) *ᵥ (st.2.1 *ᵥ z) =
      st.2.1 *ᵥ ((fromBlocks st.1.1 0 st.1.2 D * (fromBlocks st.1.1 0 st.1.2 D)ᵀ) *ᵥ z) := by
  rw [representedMatrix_gram st D hV]
  simp only [Matrix.mulVec_mulVec]
  apply congrArg (fun M : Matrix (Fin d) (Fin q ⊕ Fin r) ℝ => M *ᵥ z)
  rw [Matrix.mul_assoc, hB, Matrix.mul_one]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}

def decodeFactorReply (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (vis : VisibleFactorData d q (r + 1))
    (ex : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) : Fin d → ℝ :=
  vis.2 *ᵥ Sum.elim (vis.1.1 *ᵥ (vis.1.2ᵀ *ᵥ u))
    ((vis.1.2 * vis.1.2ᵀ) *ᵥ u +
      coordinateRotation b (rowGauge b u) (exposedGramColumn c ex))

theorem decodeFactorReply_eq (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (st : FactorData d t q (r + 1) (s + 1))
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1) (hst : st.Orthogonal) :
    decodeFactorReply b c u (visibleFactorData st)
      (revealGaussianBlock c (rotateMatrixColumns b (rowGauge b u) D)).1 =
      (representedMatrix st D * (representedMatrix st D)ᵀ) *ᵥ (st.2.1 *ᵥ Sum.elim 0 u) := by
  rw [representedMatrix_reply st D _ hst.1 hst.2.2.1, block_query_reply]
  simp only [decodeFactorReply, visibleFactorData, exposedGramColumn_eq]
  rw [query_rotation_gram_reply b u hu, query_rotation_involutive]

theorem measurable_decodeFactorReply {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : S → Fin (r + 1) → ℝ) (vis : S → VisibleFactorData d q (r + 1))
    (ex : S → (Fin (s + 1) → ℝ) × (Fin r → ℝ))
    (hu : Measurable u) (hvis : Measurable vis) (he : Measurable ex) :
    Measurable (fun x => decodeFactorReply b c (u x) (vis x) (ex x)) := by
  have harg : Measurable (fun x => (u x, exposedGramColumn c (ex x))) :=
    hu.prodMk ((measurable_exposedGramColumn c).comp he)
  have hh : Measurable (fun x => coordinateRotation b (rowGauge b (u x))
      (exposedGramColumn c (ex x))) := by
    simpa only [Function.comp_def] using (measurable_coordinate_rowGauge b).comp harg
  have ht : Measurable (fun x => (vis x).1.1 *ᵥ ((vis x).1.2ᵀ *ᵥ u x)) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    fun_prop
  have hb : Measurable (fun x => ((vis x).1.2 * (vis x).1.2ᵀ) *ᵥ u x +
      coordinateRotation b (rowGauge b (u x)) (exposedGramColumn c (ex x))) := by
    apply Measurable.add _ hh
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hm : Measurable (fun x => Sum.elim ((vis x).1.1 *ᵥ ((vis x).1.2ᵀ *ᵥ u x))
      (((vis x).1.2 * (vis x).1.2ᵀ) *ᵥ u x +
        coordinateRotation b (rowGauge b (u x)) (exposedGramColumn c (ex x)))) := by
    apply measurable_pi_lambda
    intro i
    cases i with
    | inl i => exact (measurable_pi_apply i).comp ht
    | inr i => exact (measurable_pi_apply i).comp hb
  unfold decodeFactorReply
  apply measurable_pi_lambda
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

end
end LowRank
