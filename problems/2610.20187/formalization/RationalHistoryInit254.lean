import RationalHistoryRun254

open scoped BigOperators
namespace Paper254

def rationalHistoryInitial {d : ℕ} (w0 : Fin d→ℚ) (hi : ℚ) : RationalHistoryData d :=
  ⟨w0,hi • 1⟩

theorem scalar_matrix_quadratic {d : ℕ} (c : ℝ) (x : Space d) :
    matrixQuadratic (c • (1:Precision d)) x=c*‖x‖^2 := by
  simp only [matrixQuadratic,Matrix.smul_mulVec,Matrix.one_mulVec,
    EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change x j*(c*x j)=c*x j^2
  ring

theorem rationalHistoryInitial_invariant {d : ℕ} {D : ℝ} (W : Domain d D)
    (w0 : Fin d→ℚ) (hw : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier)
    (lo hi : ℚ) (hhi : 0<(hi:ℝ)) (hlohi : (lo:ℝ)≤(hi:ℝ)) :
    RationalHistoryInvariant W (lo:ℝ) (hi:ℝ) (rationalHistoryInitial w0 hi) := by
  have hc : realMatrix (rationalHistoryInitial w0 hi).covariance=(hi:ℝ) • (1:Precision d) :=
    realMatrix_scalar hi
  constructor
  · rw [hc]
    apply symmetric_quadratic_lower_posDef _ (hi:ℝ) hhi
    · intro i j
      simp [Matrix.one_apply,eq_comm]
    · intro x
      rw [scalar_matrix_quadratic]
  · intro x
    rw [hc,scalar_matrix_quadratic]
    exact mul_le_mul_of_nonneg_right hlohi (sq_nonneg _)
  · intro x
    rw [hc,scalar_matrix_quadratic]
  · exact hw

theorem rationalHistoryRun_from_initial {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (a b r p : ℕ) (hdim : (d:ℝ)≤(2:ℝ)^a) (lo hi : ℚ) (hlo : 0<(lo:ℝ))
    (hhi : (hi:ℝ)≤(2:ℝ)^b) (hgap : ((2:ℝ)^r)⁻¹≤(hi:ℝ)-(lo:ℝ))
    (w0 : Fin d→ℚ) (hw : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier)
    (lam : ℚ) (input : ℕ→RationalHistoryData d→(Fin d→ℚ)×(Fin d→ℚ)) :
    ∀ t,RationalHistoryInvariant W (lo:ℝ) (hi:ℝ)
      (rationalHistoryRun oracle (uniformHistoryParameters a b r p lo hi)
        (rationalHistoryInitial w0 hi) lam input t) := by
  have hpos : 0<((2:ℝ)^r)⁻¹ := by positivity
  have hhi0 : 0<(hi:ℝ) := by linarith
  exact rationalHistoryRun_uniform hd W oracle hspec a b r p hdim lo hi hlo hhi hgap _
    (rationalHistoryInitial_invariant W w0 hw lo hi hhi0 (by linarith)) lam input

end Paper254
#print axioms Paper254.rationalHistoryRun_from_initial
