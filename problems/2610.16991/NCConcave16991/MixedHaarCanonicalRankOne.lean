import NCConcave16991.MixedHaarCanonicalTail

/-! # The rank-one prefix is the span of an explicit unit vector -/

noncomputable section

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 700000

def prefixVector {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) : EuclideanSpace ℝ (Fin k) :=
  rankCast r (canonicalPrefixEmbedding r.val (k - r.val)
    ((EuclideanSpace.basisFun (Fin r.val) ℝ) ⟨0,by omega⟩))

theorem prefixVector_unit {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) : ‖prefixVector r hr‖ = 1 := by
  rw [prefixVector,(rankCast r).norm_map,(canonicalPrefixEmbedding r.val (k - r.val)).norm_map]
  exact (EuclideanSpace.basisFun (Fin r.val) ℝ).orthonormal.1 _

theorem prefixVector_mem {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) : prefixVector r hr ∈ prefixSpan r := by
  exact ⟨_,⟨_,rfl⟩,rfl⟩

theorem prefixSpan_eq_span_prefixVector {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) :
    prefixSpan r = Submodule.span ℝ ({prefixVector r hr} : Set (EuclideanSpace ℝ (Fin k))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    obtain ⟨u,rfl⟩ := hy
    let i₀ : Fin r.val := ⟨0,by omega⟩
    have hu : u = (u i₀) • (EuclideanSpace.basisFun (Fin r.val) ℝ) i₀ := by
      ext i
      have hi : i = i₀ := Fin.ext (by have := i.isLt; dsimp [i₀]; omega)
      subst i
      simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single]
    rw [hu,map_smul,map_smul]
    exact (Submodule.span ℝ ({prefixVector r hr} : Set (EuclideanSpace ℝ (Fin k)))).smul_mem _
      (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro x hx
    obtain rfl : x = prefixVector r hr := by simpa only [Set.mem_singleton_iff] using hx
    exact prefixVector_mem r hr

end NCConcave16991.MixedHaar
