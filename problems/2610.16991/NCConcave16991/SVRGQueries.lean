import NCConcave16991.SVRGParameters

/-!
# The actual finite query tape of projected SVRG

Each epoch first evaluates all components at its anchor, and each stochastic
step evaluates the selected component at the current point and at the anchor.
The final residual uses two full passes.  Counting this literal tape gives a
deterministic budget, independent of the sample values and the unknown operator.
-/

noncomputable section

open Set
open scoped BigOperators

namespace NCConcave16991.SVRG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
  (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- A literal full pass over component identities at the specified point. -/
def fullPassQueries (z : E) : List (Fin n × E) := List.ofFn (fun i => (i, z))

theorem fullPassQueries_length (z : E) : (fullPassQueries (n := n) z).length = n := by
  simp [fullPassQueries]

/-- The average used by SVRG is computed by summing exactly these full-pass responses. -/
theorem fullPassQueries_average (G : Fin n → E → E) (z : E) :
    (n : ℝ)⁻¹ • ((fullPassQueries (n := n) z).map (fun q => G q.1 q.2)).sum =
      averageMap G z := by
  simp [fullPassQueries, List.map_ofFn, List.sum_ofFn, averageMap]

/-- All queries of the actual finite-seed epoch, listed in chronological order. -/
def epochQueries (G : Fin n → E → E) (anchor : S) (η : ℝ) :
    (k : ℕ) → InnerAlgorithm.Seed n k → List (Fin n × E)
  | 0, _ => fullPassQueries (anchor : E)
  | k + 1, ω => epochQueries G anchor η k ω.1 ++
      [(ω.2, (epochIterate S hne hclosed hconvex G anchor η k ω.1 : E)), (ω.2, (anchor : E))]

theorem epochQueries_length (G : Fin n → E → E) (anchor : S) (η : ℝ) (k : ℕ)
    (ω : InnerAlgorithm.Seed n k) :
    (epochQueries S hne hclosed hconvex G anchor η k ω).length = n + 2 * k := by
  induction k with
  | zero => simp [epochQueries, fullPassQueries]
  | succ k ih => simp [epochQueries, ih]; omega

/-- Query tapes of successive epochs use the actual previous epoch endpoint. -/
def epochsQueries (G : Fin n → E → E) (anchor : S) (ell μ : ℝ) :
    (J : ℕ) → FiniteProcess.History (InnerAlgorithm.Seed n (epochLength ell μ)) J →
      List (Fin n × E)
  | 0, _ => []
  | J + 1, ω => epochsQueries G anchor ell μ J ω.1 ++
      epochQueries S hne hclosed hconvex G
        (epochsIterate S hne hclosed hconvex G anchor ell μ J ω.1)
        (epochStepSize ell μ) (epochLength ell μ) ω.2

theorem epochsQueries_length (G : Fin n → E → E) (anchor : S) (ell μ : ℝ)
    (J : ℕ) (ω : FiniteProcess.History (InnerAlgorithm.Seed n (epochLength ell μ)) J) :
    (epochsQueries S hne hclosed hconvex G anchor ell μ J ω).length =
      J * (n + 2 * epochLength ell μ) := by
  induction J with
  | zero => simp [epochsQueries]
  | succ J ih => simp [epochsQueries, epochQueries_length, ih]; ring

/-- The two full passes that actually evaluate the explicit final residual. -/
def residualQueries (G : Fin n → E → E) (ell : ℝ) (z : S) : List (Fin n × E) :=
  fullPassQueries (z : E) ++
    fullPassQueries (fullStep S hne hclosed hconvex (averageMap G) ell z : E)

theorem residualQueries_length (G : Fin n → E → E) (ell : ℝ) (z : S) :
    (residualQueries S hne hclosed hconvex G ell z).length = 2 * n := by
  simp [residualQueries, fullPassQueries]
  omega

/-- The complete actual evaluation tape, including the observable residual check. -/
def residualEngineQueries (G : Fin n → E → E) (anchor : S) (ell μ : ℝ) (J : ℕ)
    (ω : FiniteProcess.History (InnerAlgorithm.Seed n (epochLength ell μ)) J) :
    List (Fin n × E) :=
  epochsQueries S hne hclosed hconvex G anchor ell μ J ω ++
    residualQueries S hne hclosed hconvex G ell
      (epochsIterate S hne hclosed hconvex G anchor ell μ J ω)

/-- A public deterministic budget for the actual finite tape (without caching anchor components). -/
def residualQueryBudget (n : ℕ) (ell μ : ℝ) (J : ℕ) : ℕ :=
  J * (n + 2 * epochLength ell μ) + 2 * n

theorem residualEngineQueries_length (G : Fin n → E → E) (anchor : S) (ell μ : ℝ)
    (J : ℕ) (ω : FiniteProcess.History (InnerAlgorithm.Seed n (epochLength ell μ)) J) :
    (residualEngineQueries S hne hclosed hconvex G anchor ell μ J ω).length =
      residualQueryBudget n ell μ J := by
  simp only [residualEngineQueries, List.length_append, epochsQueries_length,
    residualQueries_length, residualQueryBudget]

/-- Explicit arithmetic bound for the actual fixed query budget. -/
theorem residualQueryBudget_bound {ell μ : ℝ} (hell : 0 < ell) (hμ : 0 < μ)
    (J : ℕ) :
    (residualQueryBudget n ell μ J : ℝ) ≤
      (J : ℝ) * ((n : ℝ) + 24 * ell ^ 2 * Real.log 6 / μ ^ 2 + 2) + 2 * n := by
  have hm := (epochLength_bound hell hμ).le
  have hj := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 2 * J by positivity)
  simp only [residualQueryBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have heq : 24 * ell ^ 2 * Real.log 6 / μ ^ 2 =
      2 * (12 * ell ^ 2 * Real.log 6 / μ ^ 2) := by ring
  rw [heq]
  nlinarith

end NCConcave16991.SVRG
