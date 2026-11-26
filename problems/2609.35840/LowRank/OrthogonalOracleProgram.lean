import LowRank.QueryNormalization
import LowRank.OracleProgram

/-! Orthogonalize an entire finite adaptive linear-oracle program. Redundant
queries are answered from the cache; informative queries are normalized and
orthogonal to all previous informative queries. This file proves exact output
and query-budget preservation pointwise; stochastic measurability is separate. -/

namespace LowRank
open scoped InnerProductSpace
noncomputable section
namespace OracleProgram

variable {E O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance : DecidableEq E := Classical.decEq E

def orthogonalize : OracleProgram E E O → (K : Submodule ℝ E) → (E →ₗ[ℝ] E) → OracleProgram E E O
  | .done o, _, _ => .done o
  | .ask v next, K, C =>
      if queryResidual K v = 0 then
        (next (C (K.orthogonalProjection v))).orthogonalize K C
      else
        .ask (normalizedResidual K v) (fun w =>
          (next (C (K.orthogonalProjection v) + ‖queryResidual K v‖ • w)).orthogonalize
            (K ⊔ ℝ ∙ normalizedResidual K v) (extendQueryCache C (normalizedResidual K v) w))

def OrthogonalQueries : OracleProgram E E O → Submodule ℝ E → Prop
  | .done _, _ => True
  | .ask u next, K => ‖u‖ = 1 ∧ u ∈ Kᗮ ∧ ∀ w, (next w).OrthogonalQueries (K ⊔ ℝ ∙ u)

theorem orthogonalize_queries (p : OracleProgram E E O) (K : Submodule ℝ E) (C : E →ₗ[ℝ] E) :
    (p.orthogonalize K C).OrthogonalQueries K := by
  induction p generalizing K C with
  | done o => trivial
  | ask v next ih =>
    simp only [orthogonalize]
    split_ifs with hz
    · exact ih _ K C
    · exact ⟨normalizedResidual_norm K v hz, normalizedResidual_mem_orthogonal K v,
        fun w => ih _ _ _⟩

theorem eval_orthogonalize (W : E →ₗ[ℝ] E) (p : OracleProgram E E O)
    (K : Submodule ℝ E) (C : E →ₗ[ℝ] E) (hC : QueryCacheCorrect K C W) :
    (p.orthogonalize K C).eval W = p.eval W := by
  induction p generalizing K C with
  | done o => rfl
  | ask v next ih =>
    simp only [orthogonalize]
    split_ifs with hz
    · rw [ih _ K C hC, cached_query_reply_of_residual_zero K C W hC v hz]
      rfl
    · simp only [eval]
      rw [ih _ _ _ (extendQueryCache_correct K C W hC _
        (normalizedResidual_norm K v hz) (normalizedResidual_mem_orthogonal K v))]
      rw [cached_query_reply K C W hC v]

theorem calls_orthogonalize_le (W : E →ₗ[ℝ] E) (p : OracleProgram E E O)
    (K : Submodule ℝ E) (C : E →ₗ[ℝ] E) (hC : QueryCacheCorrect K C W) :
    (p.orthogonalize K C).calls W ≤ p.calls W := by
  induction p generalizing K C with
  | done o => exact le_rfl
  | ask v next ih =>
    simp only [orthogonalize]
    split_ifs with hz
    · have h := ih (C (K.orthogonalProjection v)) K C hC
      rw [cached_query_reply_of_residual_zero K C W hC v hz] at h ⊢
      exact h.trans (Nat.le_succ _)
    · simp only [calls]
      have h := ih (C (K.orthogonalProjection v) + ‖queryResidual K v‖ • W (normalizedResidual K v))
        _ _ (extendQueryCache_correct K C W hC _
          (normalizedResidual_norm K v hz) (normalizedResidual_mem_orthogonal K v))
      rw [cached_query_reply K C W hC v] at h ⊢
      exact Nat.add_le_add_right h 1

theorem hasBudget_succ {Q R O : Type*} (q : ℕ) (p : OracleProgram Q R O)
    (hp : p.HasBudget q) : p.HasBudget (q + 1) := by
  induction q generalizing p with
  | zero => cases p <;> simp_all [HasBudget]
  | succ q ih =>
    cases p with
    | done o => trivial
    | ask v next => exact fun r => ih _ (hp r)

theorem budget_orthogonalize (q : ℕ) (p : OracleProgram E E O) (hp : p.HasBudget q)
    (K : Submodule ℝ E) (C : E →ₗ[ℝ] E) : (p.orthogonalize K C).HasBudget q := by
  induction q generalizing p K C with
  | zero => cases p <;> simp_all [HasBudget, orthogonalize]
  | succ q ih =>
    cases p with
    | done o => trivial
    | ask v next =>
      simp only [orthogonalize]
      split_ifs with hz
      · exact hasBudget_succ q _ (ih _ (hp _) K C)
      · exact fun w => ih _ (hp _) _ _

theorem orthogonal_program_simulation (W : E →ₗ[ℝ] E) (p : OracleProgram E E O) :
    (p.orthogonalize ⊥ 0).eval W = p.eval W ∧
    (p.orthogonalize ⊥ 0).calls W ≤ p.calls W ∧
    (p.orthogonalize ⊥ 0).OrthogonalQueries ⊥ :=
  ⟨eval_orthogonalize W p ⊥ 0 (empty_query_cache_correct W),
    calls_orthogonalize_le W p ⊥ 0 (empty_query_cache_correct W), orthogonalize_queries p ⊥ 0⟩

end OracleProgram
end
end LowRank
