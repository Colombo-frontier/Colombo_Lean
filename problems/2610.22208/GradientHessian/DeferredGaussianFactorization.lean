import GradientHessian.DeferredGaussianField

/-! Visible blocks and the row basis are exact actual-transcript functions;
only the column basis uses the hidden enlarged record. They factor the
original presampled Gaussian matrix almost surely. -/

noncomputable section
namespace GradientHessian.DeferredGaussian
open Classical Matrix MeasureTheory ProbabilityTheory LowRank

variable (r s n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
variable (policy : VisibleOraclePolicy (r+n) r n 0 Seed)

def factors (w : Input r s n (Seed := Seed)) :
    FactorData (r+n) (s+n) (factorCount n 0) r s :=
  ((runGramOracle r s n policy w).2.1,
    ( (runGramOracle r s n policy w).2.2,(gramOracleFactors r s n policy w).2.2))

theorem factors_visible (w : Input r s n (Seed := Seed)) :
    visibleFactorData (factors r s n policy w)=(runGramOracle r s n policy w).2 := rfl

theorem exposed_measurable_transcript :
    Measurable[transcriptField r s n policy] (fun w => (factors r s n policy w).1) :=
  (visible_measurable_transcript r s n policy).fst

theorem rowBasis_measurable_transcript :
    Measurable[transcriptField r s n policy] (fun w => (factors r s n policy w).2.1) :=
  (visible_measurable_transcript r s n policy).snd

theorem columnBasis_measurable_enlarged :
    Measurable[enlargedField r s n policy] (fun w => (factors r s n policy w).2.2) :=
  (measurable_finalFactorData (r+n) (s+n) r s n 0 (compileGramOracle r s n policy)
    (fun _ => initialFactorData (r+n) (s+n)) measurable_const).snd.snd.comp
      (revealed_measurable_enlarged r s n policy)

theorem factors_measurable_enlarged : Measurable[enlargedField r s n policy] (factors r s n policy) := by
  have hv : Measurable[enlargedField r s n policy] (fun w => (runGramOracle r s n policy w).2) :=
    (visible_measurable_transcript r s n policy).mono (transcriptField_le_enlarged r s n policy) le_rfl
  exact hv.fst.prodMk (hv.snd.prodMk (columnBasis_measurable_enlarged r s n policy))

variable (ν : Measure Seed) [IsProbabilityMeasure ν]

theorem factors_eq_ae (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy)
    {v : NNReal} (hv : v≠0) :
    factors r s n policy =ᵐ[ν.prod (iidMatrixLaw (r+n) (s+n) v)] gramOracleFactors r s n policy := by
  filter_upwards [gramOracle_factorization_ae r s n ν policy hunit hv] with w hw
  unfold factors
  rw [← hw.2.2.2]
  rfl

theorem factorization_ae (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy)
    {v : NNReal} (hv : v≠0) :
    ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
      representedMatrix (factors r s n policy w) (gramOracleResidual r s n policy w)=w.2 ∧
      (factors r s n policy w).Orthogonal ∧ IsUnit (factors r s n policy w).1.1 := by
  filter_upwards [gramOracle_factorization_ae r s n ν policy hunit hv,
    factors_eq_ae r s n policy ν hunit hv] with w hw heq
  rw [heq]
  exact ⟨hw.1,hw.2.1,hw.2.2.1⟩

theorem represented_coordinates {d t q r' s' : ℕ} (st : FactorData d t q r' s')
    (D : Matrix (Fin r') (Fin s') ℝ) (ho : st.Orthogonal) :
    st.2.1ᵀ * representedMatrix st D * st.2.2=fromBlocks st.1.1 0 st.1.2 D := by
  calc
    _ = (st.2.1ᵀ*st.2.1)*fromBlocks st.1.1 0 st.1.2 D*(st.2.2ᵀ*st.2.2) := by
      simp only [representedMatrix,Matrix.mul_assoc]
    _ = _ := by rw [ho.1,ho.2.2.1,Matrix.one_mul,Matrix.mul_one]

theorem block_form_ae (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy)
    {v : NNReal} (hv : v≠0) :
    ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
      (factors r s n policy w).2.1ᵀ*w.2*(factors r s n policy w).2.2 =
        fromBlocks (factors r s n policy w).1.1 0 (factors r s n policy w).1.2
          (gramOracleResidual r s n policy w) := by
  filter_upwards [factorization_ae r s n policy ν hunit hv] with w hw
  rw [← hw.1]
  exact represented_coordinates _ _ hw.2.1

end GradientHessian.DeferredGaussian
