import MinimaxAudit.PairedCoordinates

/-! Actual isometric synthesis and contractive analysis of the paired frame. -/
open scoped RealInnerProductSpace
namespace MinimaxAudit

section Operators
variable {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def frameSynthesisLinear (W : I → E) : EuclideanSpace ℝ I →ₗ[ℝ] E where
  toFun := fun r => ∑ i, r i • W i
  map_add' := by
    intro r s
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c r
    simp [Finset.smul_sum, smul_smul]

theorem frameSynthesis_norm {W : I → E} (hW : Orthonormal ℝ W) (r : EuclideanSpace ℝ I) :
    ‖frameSynthesisLinear W r‖ = ‖r‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  have hi := hW.inner_sum (fun i => r i) (fun i => r i) Finset.univ
  simpa [frameSynthesisLinear, pow_two] using hi

noncomputable def frameSynthesis {W : I → E} (hW : Orthonormal ℝ W) :
    EuclideanSpace ℝ I →ₗᵢ[ℝ] E :=
  { frameSynthesisLinear W with norm_map' := frameSynthesis_norm hW }

noncomputable def frameAnalysisLinear (W : I → E) : E →ₗ[ℝ] EuclideanSpace ℝ I where
  toFun := fun z => WithLp.toLp 2 (fun i => inner ℝ (W i) z)
  map_add' := by intro x y; ext i; simp [inner_add_right]
  map_smul' := by intro c x; ext i; simp [inner_smul_right]

theorem frameAnalysis_norm_le {W : I → E} (hW : Orthonormal ℝ W) (z : E) :
    ‖frameAnalysisLinear W z‖ ≤ ‖z‖ := by
  have h := hW.sum_inner_products_le z (s := Finset.univ)
  have hs : ‖frameAnalysisLinear W z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    simpa [EuclideanSpace.norm_sq_eq, frameAnalysisLinear] using h
  nlinarith [norm_nonneg (frameAnalysisLinear W z), norm_nonneg z]

noncomputable def frameAnalysis {W : I → E} (hW : Orthonormal ℝ W) : E →L[ℝ] EuclideanSpace ℝ I :=
  (frameAnalysisLinear W).mkContinuous 1 (fun z => by simpa using frameAnalysis_norm_le hW z)

@[simp] theorem frameAnalysis_apply {W : I → E} (hW : Orthonormal ℝ W) (z : E) (i : I) :
    frameAnalysis hW z i = inner ℝ (W i) z := rfl

@[simp] theorem frameAnalysis_synthesis {W : I → E} (hW : Orthonormal ℝ W)
    (r : EuclideanSpace ℝ I) : frameAnalysis hW (frameSynthesis hW r) = r := by
  ext i
  exact hW.inner_right_fintype (fun j => r j) i

/-- W and W^T have exactly the adjoint pairing required by the scalar pullback. -/
theorem frame_adjoint_pairing {W : I → E} (hW : Orthonormal ℝ W)
    (r : EuclideanSpace ℝ I) (z : E) :
    inner ℝ r (frameAnalysis hW z) = inner ℝ (frameSynthesis hW r) z := by
  simp [PiLp.inner_apply, frameSynthesis, frameSynthesisLinear, sum_inner,
    real_inner_smul_left, frameAnalysis_apply, mul_comm]

end Operators

noncomputable def blockPairedIndex (n : ℕ) : Fin n × Fin 2 ≃ Fin n ⊕ Fin n where
  toFun := fun i => if i.2 = 0 then Sum.inl i.1 else Sum.inr (finRotate n i.1)
  invFun := fun i => match i with
    | Sum.inl j => (j, 0)
    | Sum.inr j => ((finRotate n).symm j, 1)
  left_inv := by
    rintro ⟨j,k⟩
    fin_cases k
    · rfl
    · change ((finRotate n).symm (finRotate n j), (1 : Fin 2)) = (j, 1)
      rw [Equiv.symm_apply_apply]
  right_inv := by
    intro i
    cases i with
    | inl j => rfl
    | inr j =>
      change Sum.inr (finRotate n ((finRotate n).symm j)) = Sum.inr j
      rw [Equiv.apply_symm_apply]

noncomputable def blockPairedFrame {n dx dy : ℕ}
    (U : Fin n → Primal dx) (V : Fin n → Dual dy) :
    Fin n × Fin 2 → SaddleSpace dx dy := pairedFrame U V ∘ blockPairedIndex n

theorem blockPairedFrame_orthonormal {n dx dy : ℕ}
    {U : Fin n → Primal dx} {V : Fin n → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) : Orthonormal ℝ (blockPairedFrame U V) :=
  (paired_frame_orthonormal hU hV).comp (blockPairedIndex n) (blockPairedIndex n).injective

@[simp] theorem blockPairedFrame_first {n dx dy : ℕ}
    (U : Fin n → Primal dx) (V : Fin n → Dual dy) (j : Fin n) :
    blockPairedFrame U V (j,0) = pairedPlus U V j := by simp [blockPairedFrame, blockPairedIndex, pairedFrame]

@[simp] theorem blockPairedFrame_second {n dx dy : ℕ}
    (U : Fin n → Primal dx) (V : Fin n → Dual dy) (j : Fin n) :
    blockPairedFrame U V (j,1) = pairedMinus U V (finRotate n j) := by
  simp [blockPairedFrame, blockPairedIndex, pairedFrame]

@[simp] theorem blockPairedFrame_terminal {n dx dy : ℕ}
    (U : Fin (n+1) → Primal dx) (V : Fin (n+1) → Dual dy) :
    blockPairedFrame U V (Fin.last n,1) = pairedMinus U V 0 := by simp

end MinimaxAudit
