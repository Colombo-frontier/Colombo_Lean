import SecondOrder.StoppedEpochAddress

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

def stoppedEpochPath {Ω E : Type*} {N : ℕ} (start finish : Fin N → Ω → ℕ)
    (x : Ω → ℕ → E) (e : Fin N) (w : Ω) (t : ℕ) : E :=
  x w (min (start e w+t) (finish e w))

theorem stoppedEpochIncrement_eq {Ω E : Type*} [AddCommMonoid E] {M N : ℕ}
    (start finish : Fin N → Ω → ℕ) (hpart : StoppedEpochPartition M N start finish)
    (g : Fin M → Ω → E) (e : Fin N) (k : Fin M) (w : Ω) (hcap : finish e w≤M) :
    reindexedMartingale g (stoppedEpochAddress start finish hpart) (e,k) w=
      if hi : start e w+k.val<finish e w then
        g ⟨start e w+k.val,hi.trans_le hcap⟩ w else 0 := by
  by_cases hi : start e w+k.val<finish e w
  · rw [dif_pos hi]
    let i : Fin M := ⟨start e w+k.val,hi.trans_le hcap⟩
    have hlabel : stoppedEpochAddress start finish hpart i w=(e,k) := by
      apply (stoppedEpochAddress_iff start finish hpart i w e k).mpr
      exact ⟨by dsimp [i]; omega,hi,by dsimp [i]; omega⟩
    unfold reindexedMartingale
    rw [Finset.sum_eq_single i]
    · simp only [selectedMartingaleIncrement,hlabel,↓reduceIte]
      rfl
    · intro j _ hji
      have hj : stoppedEpochAddress start finish hpart j w≠(e,k) := by
        intro he
        exact hji (stoppedEpochAddress_injective start finish hpart w (he.trans hlabel.symm))
      simp only [selectedMartingaleIncrement,if_neg hj]
    · simp
  · rw [dif_neg hi]
    unfold reindexedMartingale
    apply Finset.sum_eq_zero
    intro i _
    have hn : stoppedEpochAddress start finish hpart i w≠(e,k) := by
      intro he
      have hh := (stoppedEpochAddress_iff start finish hpart i w e k).mp he
      omega
    simp only [selectedMartingaleIncrement,if_neg hn]

/-- Stopping an epoch freezes its path at the last physical endpoint.
Its local displacement is precisely the predictable reindexing of the
original drift and martingale displacement. -/
theorem stoppedEpochPath_displacement {Ω E : Type*} [AddCommGroup E] {M N : ℕ}
    (start finish : Fin N → Ω → ℕ) (hpart : StoppedEpochPartition M N start finish)
    (x : Ω → ℕ → E) (a m : Fin M → Ω → E)
    (hx : ∀ w i, x w (i.val+1)-x w i.val=a i w+m i w)
    (hcap : ∀ e w, finish e w≤M) (e : Fin N) (w : Ω) (k : Fin M) :
    stoppedEpochPath start finish x e w (k.val+1)-stoppedEpochPath start finish x e w k.val=
      reindexedMartingale a (stoppedEpochAddress start finish hpart) (e,k) w+
      reindexedMartingale m (stoppedEpochAddress start finish hpart) (e,k) w := by
  rw [stoppedEpochIncrement_eq start finish hpart a e k w (hcap e w),
    stoppedEpochIncrement_eq start finish hpart m e k w (hcap e w)]
  by_cases hi : start e w+k.val<finish e w
  · rw [dif_pos hi,dif_pos hi]
    have ht := hx w ⟨start e w+k.val,hi.trans_le (hcap e w)⟩
    simpa only [stoppedEpochPath,min_eq_left hi.le,
      min_eq_left (show start e w+(k.val+1)≤finish e w by omega),Nat.add_assoc] using ht
  · rw [dif_neg hi,dif_neg hi]
    simp only [stoppedEpochPath,min_eq_right (by omega : finish e w≤start e w+(k.val+1)),
      min_eq_right (by omega : finish e w≤start e w+k.val),sub_self,zero_add]

end
end SecondOrder
