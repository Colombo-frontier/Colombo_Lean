import NCConcave16991.MixedHaarCanonicalTail

/-! # Literal coordinates and increasing canonical prefix spaces -/

noncomputable section

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 800000

def tailIndex {k : ℕ} (r : Fin (k + 1)) (j : Fin (k - r.val)) : Fin k :=
  ⟨r.val + j.val,by have := j.isLt; have := r.isLt; omega⟩

@[simp] theorem rankCast_symm_tail {k : ℕ} (r : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin k)) (j : Fin (k - r.val)) :
    canonicalTail r.val (k - r.val) ((rankCast r).symm x) j = x (tailIndex r j) := rfl

theorem mem_prefixSpan_iff_tail_zero {k : ℕ} (r : Fin (k + 1)) (x : EuclideanSpace ℝ (Fin k)) :
    x ∈ prefixSpan r ↔ canonicalTail r.val (k - r.val) ((rankCast r).symm x) = 0 := by
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := hx
    obtain ⟨u,rfl⟩ := hy
    change canonicalTail r.val (k - r.val) ((rankCast r).symm (rankCast r (canonicalJoin r.val (k - r.val) u 0))) = 0
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact canonicalTail_join r.val (k - r.val) u 0
  · intro hx
    let y := (rankCast r).symm x
    refine ⟨canonicalPrefixEmbedding r.val (k - r.val) (canonicalHead r.val (k - r.val) y),⟨_,rfl⟩,?_⟩
    apply (rankCast r).symm.injective
    change (rankCast r).symm (rankCast r (canonicalJoin r.val (k - r.val) (canonicalHead r.val (k - r.val) y) 0)) = y
    rw [LinearIsometryEquiv.symm_apply_apply]
    change canonicalJoin r.val (k - r.val) (canonicalHead r.val (k - r.val) y) 0 = y
    rw [← hx]
    exact canonicalJoin_split _ _ y

theorem mem_prefixSpan_iff_coordinates {k : ℕ} (r : Fin (k + 1)) (x : EuclideanSpace ℝ (Fin k)) :
    x ∈ prefixSpan r ↔ ∀ i : Fin k, r.val ≤ i.val → x i = 0 := by
  rw [mem_prefixSpan_iff_tail_zero]
  constructor
  · intro hx i hi
    let j : Fin (k - r.val) := ⟨i.val - r.val,by have := i.isLt; omega⟩
    have he : tailIndex r j = i := Fin.ext (Nat.add_sub_of_le hi)
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin (k - r.val)) ↦ v j) hx
    simpa only [rankCast_symm_tail,he,PiLp.zero_apply] using hh
  · intro hx
    ext j
    simpa only [rankCast_symm_tail,PiLp.zero_apply] using hx (tailIndex r j) (by change r.val ≤ r.val + j.val; omega)

theorem prefixSpan_mono {k : ℕ} (r s : Fin (k + 1)) (hrs : r.val ≤ s.val) : prefixSpan r ≤ prefixSpan s := by
  intro x hx
  apply (mem_prefixSpan_iff_coordinates s x).mpr
  intro i hi
  exact (mem_prefixSpan_iff_coordinates r x).mp hx i (hrs.trans hi)

theorem tailIsometry_tailIndex {k : ℕ} (r : Fin (k + 1))
    (v : EuclideanSpace ℝ (Fin (k - r.val))) (j : Fin (k - r.val)) :
    (tailIsometry r v).val (tailIndex r j) = v j := by
  have hh := rankCast_symm_tail r (tailIsometry r v).val j
  rw [tailIsometry_coe,LinearIsometryEquiv.symm_apply_apply,canonicalTail_join] at hh
  exact hh.symm

def nextRank {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) : Fin (k + 1) := ⟨r.val + 1,by omega⟩

def firstTailVector {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) : EuclideanSpace ℝ (Fin (k - r.val)) :=
  (EuclideanSpace.basisFun (Fin (k - r.val)) ℝ) ⟨0,by omega⟩

theorem firstTailVector_unit {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) : ‖firstTailVector r hr‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (k - r.val)) ℝ).orthonormal.1 _

theorem firstTailVector_mem_next {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    (tailIsometry r (firstTailVector r hr)).val ∈ prefixSpan (nextRank r hr) := by
  apply (mem_prefixSpan_iff_coordinates _ _).mpr
  intro i hi
  have hri : r.val ≤ i.val := by change r.val + 1 ≤ i.val at hi; omega
  let j : Fin (k - r.val) := ⟨i.val - r.val,by have := i.isLt; omega⟩
  have he : tailIndex r j = i := Fin.ext (Nat.add_sub_of_le hri)
  rw [← he,tailIsometry_tailIndex]
  have hj : j ≠ ⟨0,by omega⟩ := by
    intro hj
    have hh := congrArg Fin.val hj
    change r.val + 1 ≤ i.val at hi
    dsimp [j] at hh
    omega
  simp [firstTailVector,EuclideanSpace.basisFun_apply,EuclideanSpace.single,hj]

end NCConcave16991.MixedHaar
