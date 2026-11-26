import GradientHessian.DeferredGaussianFactorization

/-! The leading row-basis columns are precisely the actual oracle queries.
The recursive block representation stores them in reverse exposure order. -/

noncomputable section
namespace GradientHessian.DeferredGaussian
open Classical Matrix MeasureTheory ProbabilityTheory LowRank
open scoped BigOperators

theorem gauge_first_row {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r : ℕ}
    (b : OrthonormalBasis (Fin (r+1)) ℝ E) (u : Fin (r+1) → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖=1) (j : Fin (r+1)) :
    gaugeMatrix b (rowGauge b u) 0 j=u j := by
  have h := coordinateRotation_dot b (rowGauge b u) u (Pi.single j 1)
  simp_rw [rowGauge_aligns,hu] at h
  simpa [gaugeMatrix_apply,Pi.single_apply] using h

theorem newBasis_first {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {d q r : ℕ}
    (b : OrthonormalBasis (Fin (r+1)) ℝ E) (u : Fin (r+1) → ℝ)
    (B : Matrix (Fin d) (Fin q ⊕ Fin (r+1)) ℝ)
    (hu : ‖(basisCoordinates b).symm u‖=1) (i : Fin d) :
    changedBasis B (extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b u)))
      (moveFirstTail q r) i (Sum.inl 0) = (B *ᵥ Sum.elim 0 u) i := by
  simp [changedBasis,moveFirstTail,Matrix.mul_apply,Matrix.transpose_apply,extendGauge,
    Matrix.mulVec,dotProduct,gauge_first_row b u hu]

theorem newBasis_old {d q r : ℕ} (B : Matrix (Fin d) (Fin q ⊕ Fin (r+1)) ℝ)
    (G : Matrix (Fin (r+1)) (Fin (r+1)) ℝ) (i : Fin d) (j : Fin q) :
    changedBasis B (extendGauge G) (moveFirstTail q r) i (Sum.inl j.succ)=B i (Sum.inl j) := by
  simp [changedBasis,moveFirstTail,Matrix.mul_apply,Matrix.transpose_apply,extendGauge,Matrix.one_apply]

def queryColumns {d q r : ℕ} (vis : VisibleFactorData d q r) : List (Fin d → ℝ) :=
  List.ofFn (fun j : Fin q => fun i => vis.2 i (Sum.inl j))

theorem recovered_queryColumns {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {d q r : ℕ}
    (b : OrthonormalBasis (Fin (r+1)) ℝ E) (u : Fin (r+1) → ℝ)
    (vis : VisibleFactorData d q (r+1)) (reply : Fin d → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖=1) :
    queryColumns (recoverVisibleFactorData b u vis reply)=ambientQuery vis u :: queryColumns vis := by
  unfold queryColumns
  rw [List.ofFn_succ]
  congr 1
  · funext i
    exact newBasis_first b u vis.2 hu i
  · apply congrArg List.ofFn
    funext j i
    exact newBasis_old vis.2 _ i j

universe u
def queryLog (d r : ℕ) : (n q : ℕ) → {Seed : Type u} → [MeasurableSpace Seed] →
    VisibleOraclePolicy d r n q Seed → Matrix (Fin d) (Fin d) ℝ →
    Seed × VisibleFactorData d q (r+n) → List (Fin d → ℝ)
  | 0,_,_,_,_,_,_ => []
  | n+1,q,_,_,policy,W,w => ambientQuery w.2 (policy.1.1 w) ::
      queryLog d r n (q+1) policy.2 W
        (visibleOracleStep (EuclideanSpace.basisFun (Fin (r+n+1)) ℝ) policy.1.1 W w)

theorem run_queryColumns (d r n q : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (policy : VisibleOraclePolicy d r n q Seed) (hunit : VisibleOraclePolicy.IsUnit d r n q policy)
    (W : Matrix (Fin d) (Fin d) ℝ) (w : Seed × VisibleFactorData d q (r+n)) :
    queryColumns (runVisibleOracle d r n q policy W w).2 =
      (queryLog d r n q policy W w).reverse ++ queryColumns w.2 := by
  induction n generalizing q Seed with
  | zero => simp [runVisibleOracle,queryLog]
  | succ n ih =>
    rw [runVisibleOracle,ih (q+1) policy.2 hunit.2]
    change _ ++ queryColumns (recoverVisibleFactorData _ (policy.1.1 w) w.2 _) = _
    rw [recovered_queryColumns _ _ _ _ (hunit.1 w)]
    simp only [queryLog,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem leading_columns_are_queries (r s n : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (policy : VisibleOraclePolicy (r+n) r n 0 Seed)
    (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy)
    (w : Input r s n (Seed := Seed)) :
    queryColumns (visibleFactorData (factors r s n policy w)) =
      (queryLog (r+n) r n 0 policy (w.2*w.2ᵀ)
        (w.1,visibleFactorData (initialFactorData (r+n) (s+n)))).reverse := by
  rw [factors_visible]
  change queryColumns (runVisibleOracle (r+n) r n 0 policy (w.2*w.2ᵀ)
    (w.1,visibleFactorData (initialFactorData (r+n) (s+n)))).2 = _
  rw [run_queryColumns _ _ _ _ policy hunit]
  simp [queryColumns]

end GradientHessian.DeferredGaussian
