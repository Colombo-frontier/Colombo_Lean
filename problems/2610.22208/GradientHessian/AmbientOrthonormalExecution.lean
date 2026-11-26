import GradientHessian.AmbientOrthonormalQuery

/-! Exact query and reply history preservation for actual adaptive
orthonormal ambient queries on the full-measure regular Gaussian execution. -/

noncomputable section
namespace GradientHessian.AmbientOrthonormal
open Classical Matrix MeasureTheory ProbabilityTheory LowRank DeferredGaussian
open scoped Matrix
universe u

theorem compile_simulates (d t r s n q : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : AmbientOraclePolicy d n T)
    (st : MeasurableStateMap S (FactorData d t q (r+n) (s+n))) (mem : MeasurableStateMap S T)
    (p : S × Matrix (Fin (r+n)) (Fin (s+n)) ℝ) (hst : (st.1 p.1).Orthogonal)
    (hreg : GaussianPolicy.Regular r s n
      (compileVisibleOracle d t r s n q (compile d r n q policy) st mem) p)
    (hqueries : OrthonormalAfter (queryColumns (visibleFactorData (st.1 p.1)))
      (queryLog d n policy (representedMatrix (st.1 p.1) p.2 * (representedMatrix (st.1 p.1) p.2)ᵀ)
        (mem.1 p.1))) :
    let X := representedMatrix (st.1 p.1) p.2
    (runVisibleOracle d r n q (compile d r n q policy) (X*Xᵀ)
      (mem.1 p.1,visibleFactorData (st.1 p.1))).1=runAmbientOracle d n policy (X*Xᵀ) (mem.1 p.1) ∧
    DeferredGaussian.queryLog d r n q (compile d r n q policy) (X*Xᵀ)
      (mem.1 p.1,visibleFactorData (st.1 p.1))=queryLog d n policy (X*Xᵀ) (mem.1 p.1) := by
  induction n generalizing q S T with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r+n+1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s+n+1)) ℝ
    let vp := compile d r (n+1) q policy
    let uq := liftVisibleQuery vp.1 st mem
    let st' := advanceFactorState b c uq st
    let mem' := advanceOracleMemory b c uq st mem
    let gp' := compileVisibleOracle d t r s n (q+1) (compile d r n (q+1) policy.2) st' mem'
    let step := adaptiveGaussianStep b c uq.1 p
    let X := representedMatrix (st.1 p.1) p.2
    let v := policy.1.1 (mem.1 p.1)
    change 0<‖(basisCoordinates c).symm step.1.2.1‖ ∧ GaussianPolicy.Regular r s n gp' step at hreg
    have hsplit := orthonormalAfter_cons _ _ v hqueries
    have hphysical : ambientQuery (visibleFactorData (st.1 p.1))
        (vp.1.1 (mem.1 p.1,visibleFactorData (st.1 p.1)))=v :=
      reduced_query_exact b _ v hst.2.1 hsplit.1 hsplit.2.1
    have hu : ‖(basisCoordinates b).symm (uq.1 p.1)‖=1 := reducedQueryDirection_norm b _ _
    have heq := visibleOracleStep_simulation b c vp.1 st mem p hu hst (ne_of_gt hreg.1)
    have horth : (st'.1 step.1).Orthogonal := updateFactorData_orthogonal b c _ _ _ hst
    have hrec : representedMatrix (st'.1 step.1) step.2=X := updateFactorData_preserves_matrix b c _ _ _
    have hmem : mem'.1 step.1=(mem.1 p.1,(X*Xᵀ) *ᵥ v) := by
      have h := congrArg Prod.fst heq
      change (mem.1 p.1,(X*Xᵀ) *ᵥ ambientQuery _ _) = mem'.1 step.1 at h
      rw [hphysical] at h
      exact h.symm
    have hcols : queryColumns (visibleFactorData (st'.1 step.1))=
        v::queryColumns (visibleFactorData (st.1 p.1)) := by
      have h := congrArg (fun w => queryColumns w.2) heq
      change queryColumns (recoverVisibleFactorData b (vp.1.1 _) _ _) = _ at h
      rw [recovered_queryColumns b _ _ _ (show
        ‖(basisCoordinates b).symm (vp.1.1 (mem.1 p.1,visibleFactorData (st.1 p.1)))‖=1 from hu),
        hphysical] at h
      exact h.symm
    have hnext := ih (q+1) policy.2 st' mem' step horth hreg.2 (by
      rw [hcols,hrec,hmem]
      exact hsplit.2.2)
    dsimp only at hnext
    have heq' : visibleOracleStep b vp.1.1 (X*Xᵀ) (mem.1 p.1,visibleFactorData (st.1 p.1))=
        ((mem.1 p.1,(X*Xᵀ) *ᵥ v),visibleFactorData (st'.1 step.1)) :=
      heq.trans (Prod.ext hmem rfl)
    constructor
    · change (runVisibleOracle d r n (q+1) (compile d r n (q+1) policy.2) (X*Xᵀ)
        (visibleOracleStep b vp.1.1 (X*Xᵀ) (mem.1 p.1,visibleFactorData (st.1 p.1)))).1 =
        runAmbientOracle d n policy.2 (X*Xᵀ) (mem.1 p.1,(X*Xᵀ) *ᵥ v)
      rw [heq']
      simpa only [hrec,hmem] using hnext.1
    · change ambientQuery (visibleFactorData (st.1 p.1)) (vp.1.1 _) ::
        DeferredGaussian.queryLog d r n (q+1) (compile d r n (q+1) policy.2) (X*Xᵀ)
          (visibleOracleStep b vp.1.1 (X*Xᵀ) (mem.1 p.1,visibleFactorData (st.1 p.1))) =
        v::queryLog d n policy.2 (X*Xᵀ) (mem.1 p.1,(X*Xᵀ) *ᵥ v)
      rw [hphysical,heq']
      exact congrArg (List.cons v) (by simpa only [hrec,hmem] using hnext.2)

theorem compile_simulates_ae (r s n : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (policy : AmbientOraclePolicy (r+n) n Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {v : NNReal} (hv : v≠0)
    (hqueries : ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
      OrthonormalAfter [] (queryLog (r+n) n policy (w.2*w.2ᵀ) w.1)) :
    ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
      (runGramOracle r s n (compile (r+n) r n 0 policy) w).1=runAmbientGram r s n policy w ∧
      DeferredGaussian.queryLog (r+n) r n 0 (compile (r+n) r n 0 policy) (w.2*w.2ᵀ)
        (w.1,visibleFactorData (initialFactorData (r+n) (s+n)))=
        queryLog (r+n) n policy (w.2*w.2ᵀ) w.1 := by
  filter_upwards [gaussianPolicy_regular_ae r s n ν
    (compileGramOracle r s n (compile (r+n) r n 0 policy)) hv,hqueries] with w hreg hq
  have h := compile_simulates (r+n) (s+n) r s n 0 policy (initialFactorState _ _)
    (identityMemory Seed) w (initialFactorData_orthogonal _ _) hreg (by
      simpa [initialFactorState,identityMemory,initialFactorData_represents,queryColumns] using hq)
  simpa only [initialFactorState,identityMemory,initialFactorData_represents,id_eq] using h

end GradientHessian.AmbientOrthonormal
