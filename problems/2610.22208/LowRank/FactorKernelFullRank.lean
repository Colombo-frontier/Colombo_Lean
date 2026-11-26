import LowRank.FactorKernelProjector

/-! Full column rank of a represented matrix follows from its two diagonal
blocks and the orthogonality of the cumulative bases. This permits the
kernel-projector argument to start at any exposed factor state. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem mulVec_injective_of_leftInverse {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (B : Matrix a b ℝ) (L : Matrix b a ℝ) (hL : L * B = 1) : Function.Injective B.mulVec := by
  intro x y h
  have he := congrArg (fun z => L *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using he

theorem fromBlocks_lower_injective {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (A : Matrix a a ℝ) (C : Matrix b a ℝ) (D : Matrix b c ℝ)
    (hA : Function.Injective A.mulVec) (hD : Function.Injective D.mulVec) :
    Function.Injective (fromBlocks A 0 C D).mulVec := by
  intro x y h
  have hx : A *ᵥ (x ∘ Sum.inl) = A *ᵥ (y ∘ Sum.inl) := by
    have he := congrArg (fun z => z ∘ Sum.inl) h
    simpa only [fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Matrix.zero_mulVec, add_zero] using he
  have htop := hA hx
  have hy : D *ᵥ (x ∘ Sum.inr) = D *ᵥ (y ∘ Sum.inr) := by
    have he := congrArg (fun z => z ∘ Sum.inr) h
    have he' : C *ᵥ (x ∘ Sum.inl) + D *ᵥ (x ∘ Sum.inr) =
        C *ᵥ (y ∘ Sum.inl) + D *ᵥ (y ∘ Sum.inr) := by
      simpa only [fromBlocks_mulVec, Function.comp_def, Sum.elim_inr] using he
    rw [htop] at he'
    exact add_left_cancel he'
  have hbottom := hD hy
  funext i
  cases i with
  | inl i => exact congrFun htop i
  | inr i => exact congrFun hbottom i

theorem representedMatrix_injective {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (hst : st.Orthogonal)
    (hA : Function.Injective st.1.1.mulVec) (hD : Function.Injective D.mulVec) :
    Function.Injective (representedMatrix st D).mulVec := by
  have hB := mulVec_injective_of_leftInverse st.2.1 st.2.1ᵀ hst.1
  have hV := mulVec_injective_of_leftInverse st.2.2ᵀ st.2.2 hst.2.2.2
  have hcore := fromBlocks_lower_injective st.1.1 st.1.2 D hA hD
  intro x y h
  apply hV
  apply hcore
  apply hB
  simpa only [representedMatrix, ← Matrix.mulVec_mulVec] using h

theorem factorKernelProjector_bottom_le_of_blocks {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (hst : st.Orthogonal)
    (hA : Function.Injective st.1.1.mulVec) (hD : Function.Injective D.mulVec) :
    LoewnerLE ((factorKernelProjector st D).submatrix Sum.inr Sum.inr) (leftKernelProjector D) :=
  factorKernelProjector_bottom_le st D hst (representedMatrix_injective st D hst hA hD) hD

end
end LowRank
