import LowRank.GaussianNextQuery
import LowRank.QueryBasisUpdate

/-! The top-coordinate kernel mass is exactly the sum of the quadratic
kernel masses of the actual queries. This is a deterministic telescoping
identity, followed by its almost-sure connection to the Gaussian factors. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section
universe u

theorem coordinates_diagonal_quadratic {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (B : Matrix a b ℝ) (K : Matrix a a ℝ) (i : b) :
    (Bᵀ * K * B) i i = (fun j => B j i) ⬝ᵥ (K *ᵥ fun j => B j i) := by
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using
    (quadratic_coordinates B K (Pi.single i 1)).symm

def exposedKernelMass {d q r : ℕ} (vis : VisibleFactorData d q r)
    (K : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ((vis.2ᵀ * K * vis.2).submatrix Sum.inl Sum.inl).trace

theorem exposedKernelMass_eq_sum {d q r : ℕ} (vis : VisibleFactorData d q r)
    (K : Matrix (Fin d) (Fin d) ℝ) :
    exposedKernelMass vis K = ∑ j : Fin q,
      (fun i => vis.2 i (Sum.inl j)) ⬝ᵥ (K *ᵥ fun i => vis.2 i (Sum.inl j)) := by
  unfold exposedKernelMass Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro j _
  exact coordinates_diagonal_quadratic vis.2 K (Sum.inl j)

theorem exposedKernelMass_recover {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {d q r : ℕ}
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (u : Fin (r + 1) → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1) (vis : VisibleFactorData d q (r + 1))
    (reply : Fin d → ℝ) (K : Matrix (Fin d) (Fin d) ℝ) :
    exposedKernelMass (recoverVisibleFactorData b u vis reply) K =
      exposedKernelMass vis K + ambientQuery vis u ⬝ᵥ (K *ᵥ ambientQuery vis u) := by
  simp only [exposedKernelMass_eq_sum, Fin.sum_univ_succ,
    recoverVisibleFactorData_query_column b u hu, recoverVisibleFactorData_old_column]
  exact add_comm _ _

def visibleQueryMass (d r : ℕ) : (n q : ℕ) → {S : Type u} → [MeasurableSpace S] →
    VisibleOraclePolicy d r n q S → Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ →
    S × VisibleFactorData d q (r + n) → ℝ
  | 0, _, _, _, _, _, _, _ => 0
  | n + 1, q, _, _, policy, W, K, p =>
      ambientQuery p.2 (policy.1.1 p) ⬝ᵥ (K *ᵥ ambientQuery p.2 (policy.1.1 p)) +
        visibleQueryMass d r n (q + 1) policy.2 W K
          (visibleOracleStep (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ) policy.1.1 W p)

theorem runVisibleOracle_kernel_mass (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : VisibleOraclePolicy d r n q S) (hunit : VisibleOraclePolicy.IsUnit d r n q policy)
    (W K : Matrix (Fin d) (Fin d) ℝ) (p : S × VisibleFactorData d q (r + n)) :
    exposedKernelMass (runVisibleOracle d r n q policy W p).2 K =
      exposedKernelMass p.2 K + visibleQueryMass d r n q policy W K p := by
  induction n generalizing q S with
  | zero => exact (add_zero _).symm
  | succ n ih =>
    simp only [runVisibleOracle, visibleQueryMass]
    rw [ih (q + 1) policy.2 hunit.2]
    change exposedKernelMass (recoverVisibleFactorData _ (policy.1.1 p) p.2 _) K + _ = _
    rw [exposedKernelMass_recover _ _ (hunit.1 p)]
    exact add_assoc _ _ _

theorem exposedKernelMass_initial (d t : ℕ) (K : Matrix (Fin d) (Fin d) ℝ) :
    exposedKernelMass (visibleFactorData (initialFactorData d t)) K = 0 := by
  simp [exposedKernelMass_eq_sum]

theorem gramOracleQueryMass_eq_queries_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      gramOracleQueryMass r s n policy p =
        visibleQueryMass (r + n) r n 0 policy (p.2 * p.2ᵀ) (leftKernelProjector p.2)
          (p.1, visibleFactorData (initialFactorData (r + n) (s + n))) := by
  filter_upwards [gramOracle_factorization_ae r s n ν policy hunit hv] with p hp
  change exposedKernelMass (visibleFactorData (gramOracleFactors r s n policy p))
    (leftKernelProjector p.2) = _
  rw [hp.2.2.2]
  change exposedKernelMass (runVisibleOracle _ _ _ _ _ _ _).2 _ = _
  rw [runVisibleOracle_kernel_mass _ _ _ _ policy hunit, exposedKernelMass_initial, zero_add]

end
end LowRank
