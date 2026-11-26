import HaarRebalancingAction

open Set MeasureTheory
open scoped Matrix

namespace Task006.AdaptiveSphereBlock

noncomputable section

open Task006.HaarRebalancing

def indexSplit (d r : ℕ) (hr : r ≤ d) : Fin r ⊕ Fin (d - r) ≃ Fin d :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hr))

def blockRaw (r m : ℕ) (g : OrthogonalGroup m) :
    Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) ℝ :=
  Matrix.fromBlocks 1 0 0 (g : Matrix (Fin m) (Fin m) ℝ)

lemma blockRaw_unitary (r m : ℕ) (g : OrthogonalGroup m) :
    star (blockRaw r m g) * blockRaw r m g = 1 ∧
      blockRaw r m g * star (blockRaw r m g) = 1 := by
  constructor
  · change (blockRaw r m g)ᴴ * blockRaw r m g = 1
    have hg : (g : Matrix (Fin m) (Fin m) ℝ)ᴴ * g = 1 := g.property.1
    unfold blockRaw
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hg]
    simp
  · change blockRaw r m g * (blockRaw r m g)ᴴ = 1
    have hg : (g : Matrix (Fin m) (Fin m) ℝ) * (g : Matrix (Fin m) (Fin m) ℝ)ᴴ = 1 := g.property.2
    unfold blockRaw
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hg]
    simp

lemma reindex_star {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℝ) :
    star (Matrix.reindexAlgEquiv ℝ ℝ e A) =
      Matrix.reindexAlgEquiv ℝ ℝ e (star A) := by
  rfl

def blockOrthogonal (d r : ℕ) (hr : r ≤ d) (g : OrthogonalGroup (d - r)) :
    OrthogonalGroup d :=
  ⟨Matrix.reindexAlgEquiv ℝ ℝ (indexSplit d r hr) (blockRaw r (d-r) g), by
    constructor
    · rw [reindex_star, ← map_mul]
      rw [(blockRaw_unitary r (d-r) g).1, map_one]
    · rw [reindex_star, ← map_mul]
      rw [(blockRaw_unitary r (d-r) g).2, map_one]⟩

lemma blockRaw_one (r m : ℕ) : blockRaw r m (1 : OrthogonalGroup m) = 1 := by
  simp [blockRaw]

lemma blockRaw_mul (r m : ℕ) (g h : OrthogonalGroup m) :
    blockRaw r m (g*h) = blockRaw r m g * blockRaw r m h := by
  simp [blockRaw, Matrix.fromBlocks_multiply]

lemma blockOrthogonal_one (d r : ℕ) (hr : r ≤ d) :
    blockOrthogonal d r hr 1 = 1 := by
  apply Subtype.ext
  change Matrix.reindexAlgEquiv ℝ ℝ _ (blockRaw r (d-r) 1) = 1
  rw [blockRaw_one, map_one]

lemma blockOrthogonal_mul (d r : ℕ) (hr : r ≤ d)
    (g h : OrthogonalGroup (d-r)) :
    blockOrthogonal d r hr (g*h) = blockOrthogonal d r hr g * blockOrthogonal d r hr h := by
  apply Subtype.ext
  change Matrix.reindexAlgEquiv ℝ ℝ _ (blockRaw r (d-r) (g*h)) = _
  rw [blockRaw_mul, map_mul]
  rfl


lemma indexSplit_left_val (d r : ℕ) (hr : r ≤ d) (i : Fin r) :
    (indexSplit d r hr (Sum.inl i)).val = i.val := rfl

lemma indexSplit_right_val (d r : ℕ) (hr : r ≤ d) (i : Fin (d-r)) :
    (indexSplit d r hr (Sum.inr i)).val = r + i.val := rfl

lemma blockOrthogonal_entry (d r : ℕ) (hr : r ≤ d) (g : OrthogonalGroup (d-r))
    (i j : Fin r ⊕ Fin (d-r)) :
    (blockOrthogonal d r hr g : Matrix (Fin d) (Fin d) ℝ)
      (indexSplit d r hr i) (indexSplit d r hr j) = blockRaw r (d-r) g i j := by
  change blockRaw r (d-r) g
    ((indexSplit d r hr).symm ((indexSplit d r hr) i))
    ((indexSplit d r hr).symm ((indexSplit d r hr) j)) = _
  simp

lemma blockOrthogonal_entry_first (d r : ℕ) (hr : r ≤ d) (g : OrthogonalGroup (d-r))
    (i : Fin d) (j : Fin r) :
    (blockOrthogonal d r hr g : Matrix (Fin d) (Fin d) ℝ)
      i (indexSplit d r hr (Sum.inl j)) =
      if i = indexSplit d r hr (Sum.inl j) then 1 else 0 := by
  obtain ⟨a, rfl⟩ := (indexSplit d r hr).surjective i
  rw [blockOrthogonal_entry]
  simp only [(indexSplit d r hr).injective.eq_iff]
  cases a with
  | inl a => simp [blockRaw, Matrix.fromBlocks, Matrix.one_apply]
  | inr a => simp [blockRaw, Matrix.fromBlocks]

lemma blockOrthogonal_entry_residual (d r : ℕ) (hr : r ≤ d)
    (g : OrthogonalGroup (d-r)) (i j : Fin (d-r)) :
    (blockOrthogonal d r hr g : Matrix (Fin d) (Fin d) ℝ)
      (indexSplit d r hr (Sum.inr i)) (indexSplit d r hr (Sum.inr j)) = g i j := by
  rw [blockOrthogonal_entry]
  rfl

lemma blockOrthogonal_continuous (d r : ℕ) (hr : r ≤ d) :
    Continuous (blockOrthogonal d r hr) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun g : OrthogonalGroup (d-r) =>
    blockRaw r (d-r) g ((indexSplit d r hr).symm i) ((indexSplit d r hr).symm j))
  cases (indexSplit d r hr).symm i with
  | inl i => cases (indexSplit d r hr).symm j <;> exact continuous_const
  | inr i =>
    cases (indexSplit d r hr).symm j with
    | inl j => exact continuous_const
    | inr j =>
      change Continuous (fun g : OrthogonalGroup (d-r) =>
        (g : Matrix (Fin (d-r)) (Fin (d-r)) ℝ) i j)
      have hc : Continuous (fun M : Matrix (Fin (d-r)) (Fin (d-r)) ℝ => M i j) :=
        (continuous_apply j).comp (continuous_apply i)
      exact hc.comp continuous_subtype_val

lemma blockOrthogonal_measurable (d r : ℕ) (hr : r ≤ d) :
    Measurable (blockOrthogonal d r hr) := (blockOrthogonal_continuous d r hr).measurable

lemma blockOrthogonal_fixed_first (d r : ℕ) (hr : r ≤ d)
    (g : OrthogonalGroup (d-r)) (j : Fin r) :
    action (blockOrthogonal d r hr g)
      ((EuclideanSpace.basisFun (Fin d) ℝ) (indexSplit d r hr (Sum.inl j))) =
      (EuclideanSpace.basisFun (Fin d) ℝ) (indexSplit d r hr (Sum.inl j)) := by
  apply WithLp.ofLp_injective 2
  funext i
  change (∑ k : Fin d,
    (blockOrthogonal d r hr g : Matrix (Fin d) (Fin d) ℝ) i k *
      (EuclideanSpace.basisFun (Fin d) ℝ (indexSplit d r hr (Sum.inl j))) k) = _
  simp [EuclideanSpace.basisFun_apply, blockOrthogonal_entry_first]


def castOrthogonal {m n : ℕ} (h : m = n) (g : OrthogonalGroup m) : OrthogonalGroup n := h ▸ g

lemma castOrthogonal_apply {m n : ℕ} (h : m = n) (g : OrthogonalGroup m)
    (i j : Fin n) :
    (castOrthogonal h g : Matrix (Fin n) (Fin n) ℝ) i j =
      g (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  cases h
  rfl

lemma indexSplit_first_eq (d r : ℕ) (hr : r ≤ d) (j : Fin d) (hj : j.val < r) :
    indexSplit d r hr (Sum.inl ⟨j.val,hj⟩) = j := by
  apply Fin.ext
  rfl

lemma indexSplit_residual_eq (d r : ℕ) (hr : r ≤ d) (j : Fin d) (hj : ¬ j.val < r) :
    indexSplit d r hr (Sum.inr ⟨j.val-r,by omega⟩) = j := by
  apply Fin.ext
  change r + (j.val-r) = j.val
  omega

lemma blockOrthogonal_apply (d r : ℕ) (hr : r ≤ d) (g : OrthogonalGroup (d-r))
    (i j : Fin d) :
    (blockOrthogonal d r hr g : Matrix (Fin d) (Fin d) ℝ) i j =
      if hj : j.val < r then (if i = j then 1 else 0)
      else if hi : i.val < r then 0
      else g ⟨i.val-r,by omega⟩ ⟨j.val-r,by omega⟩ := by
  by_cases hj : j.val < r
  · rw [dif_pos hj]
    simpa only [indexSplit_first_eq d r hr j hj] using
      blockOrthogonal_entry_first d r hr g i (⟨j.val,hj⟩ : Fin r)
  · rw [dif_neg hj]
    by_cases hi : i.val < r
    · rw [dif_pos hi]
      rw [← indexSplit_first_eq d r hr i hi, ← indexSplit_residual_eq d r hr j hj,
        blockOrthogonal_entry]
      rfl
    · rw [dif_neg hi]
      conv_lhs =>
        rw [← indexSplit_residual_eq d r hr i hi, ← indexSplit_residual_eq d r hr j hj,
          blockOrthogonal_entry]
      rfl

/-- Nested stabilizer blocks agree with the next-rank block, including all
residual-dimension casts. -/
lemma blockOrthogonal_nested (d r : ℕ) (hr : r + 1 ≤ d)
    (g : OrthogonalGroup (d - (r+1))) :
    blockOrthogonal d r (by omega)
      (blockOrthogonal (d-r) 1 (by omega)
        (castOrthogonal (by omega : d-(r+1) = (d-r)-1) g)) =
      blockOrthogonal d (r+1) hr g := by
  apply Subtype.ext
  ext i j
  rw [blockOrthogonal_apply]
  by_cases hj : j.val < r
  · rw [dif_pos hj, blockOrthogonal_apply, dif_pos (by omega : j.val < r+1)]
  · rw [dif_neg hj]
    by_cases hi : i.val < r
    · rw [dif_pos hi, blockOrthogonal_apply]
      by_cases hj1 : j.val < r+1
      · rw [dif_pos hj1, if_neg (by intro he; have := congrArg Fin.val he; omega)]
      · rw [dif_neg hj1, dif_pos (by omega : i.val < r+1)]
    · rw [dif_neg hi, blockOrthogonal_apply, blockOrthogonal_apply]
      by_cases hj0 : j.val = r
      · have hsmall : j.val-r < 1 := by omega
        rw [dif_pos hsmall, dif_pos (by omega : j.val < r+1)]
        congr 1
        apply propext
        constructor
        · intro h
          have hh := congrArg Fin.val h
          change i.val-r = j.val-r at hh
          apply Fin.ext
          omega
        · intro h
          have hh := congrArg Fin.val h
          apply Fin.ext
          change i.val-r = j.val-r
          omega
      · have hbig : ¬ j.val-r < 1 := by omega
        rw [dif_neg hbig, dif_neg (by omega : ¬ j.val < r+1)]
        by_cases hi0 : i.val = r
        · rw [dif_pos (by omega : i.val-r < 1), dif_pos (by omega : i.val < r+1)]
        · rw [dif_neg (by omega : ¬ i.val-r < 1), dif_neg (by omega : ¬ i.val < r+1), castOrthogonal_apply]
          congr 1 <;> apply Fin.ext <;> simp only [Fin.coe_cast, Fin.val_mk] <;> omega

end
end Task006.AdaptiveSphereBlock
