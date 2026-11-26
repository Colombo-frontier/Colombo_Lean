import NCConcave16991.MixedHaarCanonicalCoordinates

/-! # Adding the first tail axis gives exactly the next canonical prefix -/

noncomputable section

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 800000

def prefixIndex {k : ℕ} (r : Fin (k + 1)) (i : Fin r.val) : Fin k := ⟨i.val,by have := i.isLt; have := r.isLt; omega⟩

@[simp] theorem rankCast_symm_head {k : ℕ} (r : Fin (k + 1)) (x : EuclideanSpace ℝ (Fin k)) (i : Fin r.val) :
    canonicalHead r.val (k - r.val) ((rankCast r).symm x) i = x (prefixIndex r i) := rfl

theorem tailIsometry_prefixIndex {k : ℕ} (r : Fin (k + 1))
    (v : EuclideanSpace ℝ (Fin (k - r.val))) (i : Fin r.val) :
    (tailIsometry r v).val (prefixIndex r i) = 0 := by
  have hh := rankCast_symm_head r (tailIsometry r v).val i
  rw [tailIsometry_coe,LinearIsometryEquiv.symm_apply_apply,canonicalHead_join] at hh
  exact hh.symm

theorem firstTailVector_ambient_basis {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    (tailIsometry r (firstTailVector r hr)).val = (EuclideanSpace.basisFun (Fin k) ℝ) ⟨r.val,hr⟩ := by
  ext i
  by_cases hi : i.val < r.val
  · let j : Fin r.val := ⟨i.val,hi⟩
    have he : prefixIndex r j = i := Fin.ext rfl
    rw [← he,tailIsometry_prefixIndex]
    have hne : (prefixIndex r j).val ≠ r.val := by change i.val ≠ r.val; omega
    simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single,Fin.ext_iff,hne]
  · have hri : r.val ≤ i.val := by omega
    let j : Fin (k - r.val) := ⟨i.val - r.val,by have := i.isLt; omega⟩
    have he : tailIndex r j = i := Fin.ext (Nat.add_sub_of_le hri)
    rw [← he,tailIsometry_tailIndex]
    simp [firstTailVector,EuclideanSpace.basisFun_apply,EuclideanSpace.single,Fin.ext_iff,tailIndex]

theorem prefixSpan_next {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    prefixSpan (nextRank r hr) = prefixSpan r ⊔ Submodule.span ℝ
      ({(tailIsometry r (firstTailVector r hr)).val} : Set (EuclideanSpace ℝ (Fin k))) := by
  let a := (tailIsometry r (firstTailVector r hr)).val
  have ha : a ∈ prefixSpan (nextRank r hr) := firstTailVector_mem_next r hr
  apply le_antisymm
  · intro x hx
    let c := x ⟨r.val,hr⟩
    let x₀ := x - c • a
    have hx₀ : x₀ ∈ prefixSpan r := by
      apply (mem_prefixSpan_iff_coordinates r x₀).mpr
      intro i hi
      by_cases he : i = ⟨r.val,hr⟩
      · subst i
        simp [x₀,a,c,firstTailVector_ambient_basis,EuclideanSpace.basisFun_apply,EuclideanSpace.single]
      · have hi' : (nextRank r hr).val ≤ i.val := by
          have hne : i.val ≠ r.val := by intro h; exact he (Fin.ext h)
          change r.val + 1 ≤ i.val
          omega
        have hxi := (mem_prefixSpan_iff_coordinates (nextRank r hr) x).mp hx i hi'
        simp [x₀,a,hxi,firstTailVector_ambient_basis,EuclideanSpace.basisFun_apply,EuclideanSpace.single,he]
    have hax : a ∈ prefixSpan r ⊔ Submodule.span ℝ ({a} : Set (EuclideanSpace ℝ (Fin k))) :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
    have hh := (prefixSpan r ⊔ Submodule.span ℝ ({a} : Set (EuclideanSpace ℝ (Fin k)))).add_mem
      (Submodule.mem_sup_left hx₀) ((prefixSpan r ⊔ Submodule.span ℝ ({a} : Set (EuclideanSpace ℝ (Fin k)))).smul_mem c hax)
    simpa only [x₀,sub_add_cancel] using hh
  · apply sup_le
    · exact prefixSpan_mono r (nextRank r hr) (by change r.val ≤ r.val + 1; omega)
    · apply Submodule.span_le.mpr
      intro x hx
      have he : x = a := by simpa only [Set.mem_singleton_iff] using hx
      exact he ▸ ha

end NCConcave16991.MixedHaar
