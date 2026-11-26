import NCConcave16991.MixedHaarCanonicalBlock
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-! # The canonical Euclidean tail isometry onto the prefix complement -/

noncomputable section

namespace NCConcave16991.MixedHaar

open scoped InnerProductSpace

set_option maxHeartbeats 900000

def canonicalPrefixEmbedding (r d : ℕ) :
    EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r + d)) where
  toLinearMap := (canonicalSplitEquiv r d).symm.toLinearMap.comp (LinearMap.inl ℝ _ _)
  norm_map' u := by
    change ‖canonicalJoin r d u 0‖ = ‖u‖
    have hh := canonicalJoin_norm_sq r d u 0
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),add_zero] at hh
    nlinarith [norm_nonneg (canonicalJoin r d u 0),norm_nonneg u]

def canonicalTailEmbedding (r d : ℕ) :
    EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r + d)) where
  toLinearMap := (canonicalSplitEquiv r d).symm.toLinearMap.comp (LinearMap.inr ℝ _ _)
  norm_map' v := by
    change ‖canonicalJoin r d 0 v‖ = ‖v‖
    have hh := canonicalJoin_norm_sq r d 0 v
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add] at hh
    nlinarith [norm_nonneg (canonicalJoin r d 0 v),norm_nonneg v]

def canonicalPrefixSpan (r d : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (r + d))) :=
  (canonicalPrefixEmbedding r d).toLinearMap.range

theorem canonicalTail_mem_orthogonal (r d : ℕ) (v : EuclideanSpace ℝ (Fin d)) :
    canonicalTailEmbedding r d v ∈ (canonicalPrefixSpan r d)ᗮ := by
  apply ((canonicalPrefixSpan r d).mem_orthogonal _).mpr
  intro y hy
  obtain ⟨u,rfl⟩ := hy
  change ⟪canonicalJoin r d u 0,canonicalJoin r d 0 v⟫_ℝ = 0
  simp only [canonicalJoin_inner,inner_zero_right,inner_zero_left,zero_add]

theorem canonicalOrthogonal_head_eq_zero (r d : ℕ) (x : EuclideanSpace ℝ (Fin (r + d)))
    (hx : x ∈ (canonicalPrefixSpan r d)ᗮ) : canonicalHead r d x = 0 := by
  have hh := ((canonicalPrefixSpan r d).mem_orthogonal x).mp hx
    (canonicalPrefixEmbedding r d (canonicalHead r d x)) ⟨canonicalHead r d x,rfl⟩
  have he : ⟪canonicalPrefixEmbedding r d (canonicalHead r d x),x⟫_ℝ =
      ⟪canonicalHead r d x,canonicalHead r d x⟫_ℝ := by
    calc
      _ = ⟪canonicalJoin r d (canonicalHead r d x) 0,
          canonicalJoin r d (canonicalHead r d x) (canonicalTail r d x)⟫_ℝ := by
        rw [canonicalJoin_split]
        rfl
      _ = _ := by simp only [canonicalJoin_inner,inner_zero_left,add_zero]
  exact inner_self_eq_zero.mp (he.symm.trans hh)

def canonicalTailIsometry (r d : ℕ) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] (canonicalPrefixSpan r d)ᗮ where
  toFun v := ⟨canonicalTailEmbedding r d v,canonicalTail_mem_orthogonal r d v⟩
  invFun x := canonicalTail r d x.val
  left_inv v := canonicalTail_join r d 0 v
  right_inv x := by
    apply Subtype.ext
    change canonicalJoin r d 0 (canonicalTail r d x.val) = x.val
    rw [← canonicalOrthogonal_head_eq_zero r d x.val x.property,canonicalJoin_split]
  map_add' u v := by apply Subtype.ext; exact map_add (canonicalTailEmbedding r d) u v
  map_smul' a v := by apply Subtype.ext; exact map_smul (canonicalTailEmbedding r d) a v
  norm_map' v := (canonicalTailEmbedding r d).norm_map v

def rankCast {k : ℕ} (r : Fin (k + 1)) :
    EuclideanSpace ℝ (Fin (r.val + (k - r.val))) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (Nat.add_sub_of_le (by omega : r.val ≤ k)))

def prefixSpan {k : ℕ} (r : Fin (k + 1)) : Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
  (canonicalPrefixSpan r.val (k - r.val)).map (rankCast r).toLinearEquiv.toLinearMap

def tailIsometry {k : ℕ} (r : Fin (k + 1)) :
    EuclideanSpace ℝ (Fin (k - r.val)) ≃ₗᵢ[ℝ] (prefixSpan r)ᗮ :=
  ((canonicalTailIsometry r.val (k - r.val)).trans
    (LinearIsometryEquiv.submoduleMap (canonicalPrefixSpan r.val (k - r.val))ᗮ (rankCast r))).trans
      (LinearIsometryEquiv.ofEq _ _ ((canonicalPrefixSpan r.val (k - r.val)).map_orthogonal_equiv (rankCast r)))

theorem tailIsometry_coe {k : ℕ} (r : Fin (k + 1)) (v : EuclideanSpace ℝ (Fin (k - r.val))) :
    (tailIsometry r v : EuclideanSpace ℝ (Fin k)) = rankCast r (canonicalJoin r.val (k - r.val) 0 v) := rfl

end NCConcave16991.MixedHaar
