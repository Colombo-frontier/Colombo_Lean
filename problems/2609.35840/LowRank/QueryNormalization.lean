import LowRank.GaussianOrthogonal

/-! Exact normalization of a query using a cached linear action on the
already queried subspace. A zero residual requires no oracle call. -/

namespace LowRank
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def queryResidual (K : Submodule ℝ E) (v : E) : E := v - (K.orthogonalProjection v : E)

def normalizedResidual (K : Submodule ℝ E) (v : E) : E :=
  ‖queryResidual K v‖⁻¹ • queryResidual K v

def QueryCacheCorrect (K : Submodule ℝ E) (C W : E →ₗ[ℝ] E) : Prop :=
  K ≤ LinearMap.eqLocus C W

def extendQueryCache (C : E →ₗ[ℝ] E) (u w : E) : E →ₗ[ℝ] E :=
  C + ((innerSL ℝ u).toLinearMap).smulRight (w - C u)

theorem extendQueryCache_apply (C : E →ₗ[ℝ] E) (u w x : E) :
    extendQueryCache C u w x = C x + ⟪u, x⟫_ℝ • (w - C u) := rfl

theorem normalizedResidual_mem_orthogonal (K : Submodule ℝ E) (v : E) :
    normalizedResidual K v ∈ Kᗮ :=
  Kᗮ.smul_mem _ (Submodule.sub_orthogonalProjection_mem_orthogonal v)

theorem normalizedResidual_norm (K : Submodule ℝ E) (v : E) (hv : queryResidual K v ≠ 0) :
    ‖normalizedResidual K v‖ = 1 := by
  rw [normalizedResidual, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem scaled_normalizedResidual (K : Submodule ℝ E) (v : E) :
    ‖queryResidual K v‖ • normalizedResidual K v = queryResidual K v := by
  by_cases hv : queryResidual K v = 0
  · simp [normalizedResidual, hv]
  · rw [normalizedResidual, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

theorem query_split (K : Submodule ℝ E) (v : E) :
    (K.orthogonalProjection v : E) + ‖queryResidual K v‖ • normalizedResidual K v = v := by
  rw [scaled_normalizedResidual, queryResidual]
  abel

theorem cached_query_reply (K : Submodule ℝ E) (C W : E →ₗ[ℝ] E)
    (hC : QueryCacheCorrect K C W) (v : E) :
    C (K.orthogonalProjection v) + ‖queryResidual K v‖ • W (normalizedResidual K v) = W v := by
  have hc : C (K.orthogonalProjection v) = W (K.orthogonalProjection v) :=
    hC (K.orthogonalProjection v).property
  rw [hc, ← map_smul, ← map_add, query_split]

theorem cached_query_reply_of_residual_zero (K : Submodule ℝ E) (C W : E →ₗ[ℝ] E)
    (hC : QueryCacheCorrect K C W) (v : E) (hv : queryResidual K v = 0) :
    C (K.orthogonalProjection v) = W v := by
  have h := cached_query_reply K C W hC v
  simpa only [hv, norm_zero, zero_smul, add_zero] using h

theorem extendQueryCache_correct (K : Submodule ℝ E) (C W : E →ₗ[ℝ] E)
    (hC : QueryCacheCorrect K C W) (u : E) (hu : ‖u‖ = 1) (horth : u ∈ Kᗮ) :
    QueryCacheCorrect (K ⊔ ℝ ∙ u) (extendQueryCache C u (W u)) W := by
  apply sup_le
  · intro x hx
    change C x + ⟪u, x⟫_ℝ • (W u - C u) = W x
    rw [Submodule.inner_left_of_mem_orthogonal hx horth, zero_smul, add_zero]
    exact hC hx
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = u := Set.mem_singleton_iff.mp hx
    subst x
    change C u + ⟪u, u⟫_ℝ • (W u - C u) = W u
    rw [real_inner_self_eq_norm_sq, hu, one_pow, one_smul]
    abel

theorem empty_query_cache_correct (W : E →ₗ[ℝ] E) : QueryCacheCorrect ⊥ 0 W := by
  intro x hx
  have hx' : x = 0 := (Submodule.mem_bot ℝ).mp hx
  subst x
  simp

end
end LowRank
