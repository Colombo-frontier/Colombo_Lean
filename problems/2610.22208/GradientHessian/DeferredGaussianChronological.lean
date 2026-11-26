import GradientHessian.DeferredGaussianSource

/-! A fixed leading-block permutation restores chronological query order.
It preserves the residual block, conditional law and invertible exposed block. -/

noncomputable section
namespace GradientHessian.DeferredGaussian
open Classical Matrix MeasureTheory ProbabilityTheory LowRank

def reverseLeading (q r : ℕ) : (Fin q ⊕ Fin r) ≃ (Fin q ⊕ Fin r) :=
  Equiv.sumCongr (Fin.revPerm (n := q)) (Equiv.refl _)

def chronological {d t q r s : ℕ} (st : FactorData d t q r s) : FactorData d t q r s :=
  ((st.1.1.submatrix (Fin.revPerm (n := q)) (Fin.revPerm (n := q)),st.1.2.submatrix id (Fin.revPerm (n := q))),
    (st.2.1.submatrix id (reverseLeading q r),st.2.2.submatrix id (reverseLeading q s)))

theorem chronological_unit {d t q r s : ℕ} (st : FactorData d t q r s) (h : IsUnit st.1.1) :
    IsUnit (chronological st).1.1 := (Matrix.isUnit_submatrix_equiv _ _).mpr h

theorem chronological_orthogonal {d t q r s : ℕ} (st : FactorData d t q r s) (h : st.Orthogonal) :
    (chronological st).Orthogonal := by
  have he {d' r' : ℕ} (B : Matrix (Fin d') (Fin q ⊕ Fin r') ℝ) :
      changedBasis B 1 (reverseLeading q r')=B.submatrix id (reverseLeading q r') := by
    simp only [changedBasis,Matrix.transpose_one,Matrix.mul_one]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [he] using changedBasis_transpose_mul st.2.1 1 (reverseLeading q r) h.1 (by simp)
  · simpa only [he] using changedBasis_mul_transpose st.2.1 1 (reverseLeading q r) h.2.1 (by simp)
  · simpa only [he] using changedBasis_transpose_mul st.2.2 1 (reverseLeading q s) h.2.2.1 (by simp)
  · simpa only [he] using changedBasis_mul_transpose st.2.2 1 (reverseLeading q s) h.2.2.2 (by simp)

theorem chronological_blocks {d t q r s : ℕ} (st : FactorData d t q r s)
    (G : Matrix (Fin r) (Fin s) ℝ) :
    (fromBlocks st.1.1 0 st.1.2 G).submatrix (reverseLeading q r) (reverseLeading q s) =
      fromBlocks (chronological st).1.1 0 (chronological st).1.2 G := by
  ext i j
  cases i <;> cases j <;> rfl

theorem chronological_block_form {d t q r s : ℕ} (st : FactorData d t q r s)
    (X : Matrix (Fin d) (Fin t) ℝ) (G : Matrix (Fin r) (Fin s) ℝ)
    (h : st.2.1ᵀ*X*st.2.2=fromBlocks st.1.1 0 st.1.2 G) :
    (chronological st).2.1ᵀ*X*(chronological st).2.2 =
      fromBlocks (chronological st).1.1 0 (chronological st).1.2 G := by
  change (st.2.1.submatrix id (reverseLeading q r))ᵀ*X*
    st.2.2.submatrix id (reverseLeading q s)=_
  rw [Matrix.transpose_submatrix]
  calc
    _ = (st.2.1ᵀ*X*st.2.2).submatrix (reverseLeading q r) (reverseLeading q s) := by
      ext i j
      simp only [Matrix.mul_apply,Matrix.submatrix_apply,id_eq]
    _ = _ := by rw [h,chronological_blocks]

theorem chronological_columns {d t q r s : ℕ} (st : FactorData d t q r s) :
    queryColumns (visibleFactorData (chronological st))=
      (queryColumns (visibleFactorData st)).reverse := by
  apply List.ext_getElem
  · simp [queryColumns]
  · intro i hi hj
    simp [queryColumns,chronological,visibleFactorData,reverseLeading,Fin.revPerm,Fin.rev,
      Nat.sub_sub,Nat.add_comm]

theorem chronological_leading_queries (r s n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (policy : VisibleOraclePolicy (r+n) r n 0 Seed)
    (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy)
    (w : Input r s n (Seed := Seed)) :
    queryColumns (visibleFactorData (chronological (factors r s n policy w)))=
      queryLog (r+n) r n 0 policy (w.2*w.2ᵀ)
        (w.1,visibleFactorData (initialFactorData (r+n) (s+n))) := by
  rw [chronological_columns,leading_columns_are_queries r s n policy hunit,List.reverse_reverse]

theorem measurable_submatrix {Ω m n a b : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix m n ℝ) (hA : Measurable A) (e : a → m) (f : b → n) :
    Measurable (fun w => (A w).submatrix e f) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply (f j)).comp ((measurable_pi_apply (e i)).comp hA)

theorem chronological_visible_measurable (r s n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (policy : VisibleOraclePolicy (r+n) r n 0 Seed) :
    Measurable[transcriptField r s n policy]
      (fun w => visibleFactorData (chronological (factors r s n policy w))) := by
  letI : MeasurableSpace (Input r s n (Seed := Seed)) := transcriptField r s n policy
  have h := visible_measurable_transcript r s n policy
  exact ((measurable_submatrix _ h.fst.fst _ _).prodMk
    (measurable_submatrix _ h.fst.snd _ _)).prodMk (measurable_submatrix _ h.snd _ _)

theorem chronological_factorization_ae (r s n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (policy : VisibleOraclePolicy (r+n) r n 0 Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy) {v : NNReal} (hv : v≠0) :
    ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
      let st := chronological (factors r s n policy w)
      st.Orthogonal ∧ IsUnit st.1.1 ∧
        st.2.1ᵀ*w.2*st.2.2=fromBlocks st.1.1 0 st.1.2 (gramOracleResidual r s n policy w) := by
  filter_upwards [factorization_ae r s n policy ν hunit hv,
    block_form_ae r s n policy ν hunit hv] with w hw hb
  exact ⟨chronological_orthogonal _ hw.2.1,chronological_unit _ hw.2.2,chronological_block_form _ _ _ hb⟩

end GradientHessian.DeferredGaussian
