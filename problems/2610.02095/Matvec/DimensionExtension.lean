import Matvec.Simplex

/-!
# Exact dimension extension by duplication and zero padding

The aggregation maps are finite fiber sums. All oracle identities hold for
arbitrary real queries. For simplex games, surjective duplication preserves
the full gap exactly and aggregation preserves feasible strategies. These
are the concrete transformations in `lem:dimension-extension`.
-/

namespace Matvec
namespace DimensionExtension

noncomputable section
open Matrix

variable {a b m n M N : Type*}
  [Fintype a] [Fintype b] [Fintype m] [Fintype n] [Fintype M] [Fintype N]

/-- Sum a vector over each fiber of a coordinate map. -/
def aggregate (f : a → b) (x : a → ℝ) : b → ℝ := by
  classical
  exact fun j => ∑ i, if f i = j then x i else 0

theorem aggregate_sum (f : a → b) (x : a → ℝ) :
    ∑ j, aggregate f x j = ∑ i, x i := by
  classical
  unfold aggregate
  rw [Finset.sum_comm]
  simp

omit [Fintype b] in
theorem aggregate_nonneg (f : a → b) (x : a → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ j, 0 ≤ aggregate f x j := by
  classical
  intro j
  apply Finset.sum_nonneg
  intro i hi
  dsimp
  split_ifs
  · exact hx i
  · norm_num

theorem aggregate_simplex (f : a → b) (x : a → ℝ) (hx : InSimplex x) :
    InSimplex (aggregate f x) := by
  exact ⟨aggregate_nonneg f x hx.1, by rw [aggregate_sum]; exact hx.2⟩

theorem aggregate_weighted_sum (f : a → b) (x : a → ℝ) (g : b → ℝ) :
    ∑ j, g j * aggregate f x j = ∑ i, g (f i) * x i := by
  classical
  unfold aggregate
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

omit [Fintype b] in
theorem continuous_aggregate (f : a → b) : Continuous (aggregate f) := by
  classical
  unfold aggregate
  apply continuous_pi
  intro j
  apply continuous_finset_sum _ (fun i _ => ?_)
  by_cases h : f i = j
  · simp only [h, if_true]
    exact continuous_apply i
  · simp only [h, if_false]
    exact continuous_const

theorem measurable_aggregate (f : a → b) : Measurable (aggregate f) :=
  (continuous_aggregate f).measurable

omit [Fintype a] [Fintype b] in
theorem continuous_duplicate_vector (f : a → b) :
    Continuous (fun x : b → ℝ => fun i => x (f i)) := by
  fun_prop

/-- Duplicate rows and columns along the prescribed index maps. -/
def duplicateMatrix (A : Matrix m n ℝ) (ρ : M → m) (χ : N → n) : Matrix M N ℝ :=
  fun i j => A (ρ i) (χ j)

omit [Fintype m] [Fintype M] in
theorem duplicate_mulVec (A : Matrix m n ℝ) (ρ : M → m) (χ : N → n)
    (x : N → ℝ) :
    duplicateMatrix A ρ χ *ᵥ x = fun i => (A *ᵥ aggregate χ x) (ρ i) := by
  funext i
  exact (aggregate_weighted_sum χ x (fun j => A (ρ i) j)).symm

omit [Fintype n] [Fintype N] in
theorem duplicate_transpose_mulVec (A : Matrix m n ℝ) (ρ : M → m) (χ : N → n)
    (y : M → ℝ) :
    (duplicateMatrix A ρ χ).transpose *ᵥ y =
      fun j => (A.transpose *ᵥ aggregate ρ y) (χ j) := by
  funext j
  exact (aggregate_weighted_sum ρ y (fun i => A i (χ j))).symm

omit [Fintype m] [Fintype n] [Fintype M] [Fintype N] in
theorem duplicate_entries_bounded (A : Matrix m n ℝ) (ρ : M → m) (χ : N → n)
    (hA : ∀ i j, |A i j| ≤ 1) : ∀ i j, |duplicateMatrix A ρ χ i j| ≤ 1 := by
  intro i j
  exact hA (ρ i) (χ j)

/-- Surjections ensure that no original pure row or column disappears.
No feasibility assumption is needed for this exact full-gap identity. -/
theorem duplicate_fullGap_iff (A : Matrix m n ℝ) (ρ : M → m) (χ : N → n)
    (hρ : Function.Surjective ρ) (hχ : Function.Surjective χ)
    (x : N → ℝ) (y : M → ℝ) (ε : ℝ) :
    FullGapAtMost (duplicateMatrix A ρ χ) x y ε ↔
      FullGapAtMost A (aggregate χ x) (aggregate ρ y) ε := by
  unfold FullGapAtMost
  rw [duplicate_mulVec, duplicate_transpose_mulVec]
  constructor
  · intro h i j
    obtain ⟨i', hi⟩ := hρ i
    obtain ⟨j', hj⟩ := hχ j
    simpa only [hi, hj] using h i' j'
  · intro h i j
    exact h (ρ i) (χ j)

theorem duplicate_simplexGap [Nonempty m] [Nonempty n] [Nonempty M] [Nonempty N]
    (A : Matrix m n ℝ) (ρ : M → m) (χ : N → n)
    (hρ : Function.Surjective ρ) (hχ : Function.Surjective χ)
    (x : N → ℝ) (y : M → ℝ) :
    simplexGap (duplicateMatrix A ρ χ) x y =
      simplexGap A (aggregate χ x) (aggregate ρ y) := by
  apply le_antisymm
  · apply (fullGapAtMost_iff _ _ _ _).mp
    apply (duplicate_fullGap_iff A ρ χ hρ hχ x y _).mpr
    exact (fullGapAtMost_iff _ _ _ _).mpr le_rfl
  · apply (fullGapAtMost_iff _ _ _ _).mp
    apply (duplicate_fullGap_iff A ρ χ hρ hχ x y _).mp
    exact (fullGapAtMost_iff _ _ _ _).mpr le_rfl

/-- An explicit surjection from a larger finite index set onto a nonempty
hard-core index set. Extra coordinates repeat coordinate zero. -/
def coreProjection {k K : ℕ} (hk : 0 < k) (_hsize : k ≤ K) : Fin K → Fin k :=
  fun i => if h : i.val < k then ⟨i.val, h⟩ else ⟨0, hk⟩

theorem coreProjection_surjective {k K : ℕ} (hk : 0 < k) (hsize : k ≤ K) :
    Function.Surjective (coreProjection hk hsize) := by
  intro j
  refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hsize⟩, ?_⟩
  simp [coreProjection, j.isLt]

theorem padded_column_count {k K : ℕ} (hsize : k ≤ K) :
    Fintype.card (Fin k ⊕ Fin (K - k)) = K := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Both query replies are simulated by one original two-sided query. -/
theorem duplicate_twoSided (A : Matrix m n ℝ) (ρ : M → m) (χ : N → n)
    (x : N → ℝ) (y : M → ℝ) :
    (duplicateMatrix A ρ χ *ᵥ x, (duplicateMatrix A ρ χ).transpose *ᵥ y) =
    ((fun i => (A *ᵥ aggregate χ x) (ρ i)),
      (fun j => (A.transpose *ᵥ aggregate ρ y) (χ j))) := by
  rw [duplicate_mulVec, duplicate_transpose_mulVec]

section Ball

variable {e : Type*} [Fintype e]

/-- The ball geometry duplicates rows and appends zero columns, instead of
duplicating columns, to preserve the Euclidean strategy constraint. -/
def padBallMatrix (A : Matrix m n ℝ) (ρ : M → m) : Matrix M (n ⊕ e) ℝ :=
  fun i => Sum.elim (A (ρ i)) (fun _ => 0)

omit [Fintype m] [Fintype M] in
theorem padBall_mulVec (A : Matrix m n ℝ) (ρ : M → m) (x : n ⊕ e → ℝ) :
    padBallMatrix A ρ *ᵥ x = fun i => (A *ᵥ (fun j => x (Sum.inl j))) (ρ i) := by
  funext i
  simp [padBallMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

omit [Fintype n] [Fintype e] in
theorem padBall_transpose_mulVec (A : Matrix m n ℝ) (ρ : M → m) (y : M → ℝ) :
    (padBallMatrix A ρ : Matrix M (n ⊕ e) ℝ).transpose *ᵥ y =
      Sum.elim (A.transpose *ᵥ aggregate ρ y) (fun _ => 0) := by
  funext j
  cases j with
  | inl j => exact (aggregate_weighted_sum ρ y (fun i => A i j)).symm
  | inr j => simp [padBallMatrix, Matrix.mulVec, Matrix.transpose_apply, dotProduct]

omit [Fintype m] [Fintype M] in
theorem padBall_row_sq (A : Matrix m n ℝ) (ρ : M → m) (i : M) :
    ∑ j : n ⊕ e, (padBallMatrix A ρ i j) ^ 2 = ∑ j, (A (ρ i) j) ^ 2 := by
  simp [padBallMatrix, Fintype.sum_sum_type]

omit [Fintype m] [Fintype M] in
theorem padBall_normalized (A : Matrix m n ℝ) (ρ : M → m)
    (hA : ∀ i, ∑ j, (A i j) ^ 2 ≤ 1) :
    ∀ i, ∑ j : n ⊕ e, (padBallMatrix A ρ i j) ^ 2 ≤ 1 := by
  intro i
  rw [padBall_row_sq]
  exact hA (ρ i)

theorem projected_ball_feasible (x : n ⊕ e → ℝ) (hx : ∑ j, (x j) ^ 2 ≤ 1) :
    ∑ j, (x (Sum.inl j)) ^ 2 ≤ 1 := by
  rw [Fintype.sum_sum_type] at hx
  have hnonneg : 0 ≤ ∑ j : e, (x (Sum.inr j)) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  linarith

theorem padBall_transpose_sq (A : Matrix m n ℝ) (ρ : M → m) (y : M → ℝ) :
    ∑ j : n ⊕ e, (((padBallMatrix A ρ).transpose *ᵥ y) j) ^ 2 =
      ∑ j, ((A.transpose *ᵥ aggregate ρ y) j) ^ 2 := by
  rw [padBall_transpose_mulVec]
  simp [Fintype.sum_sum_type]

/-- Rowwise form of the actual ball--simplex gap formula (l21-gap). -/
def BallGapAtMost (A : Matrix m n ℝ) (x : n → ℝ) (y : m → ℝ) (ε : ℝ) : Prop :=
  ∀ i, (A *ᵥ x) i + Real.sqrt (∑ j, ((A.transpose *ᵥ y) j) ^ 2) ≤ ε

def ballGap [Nonempty m] (A : Matrix m n ℝ) (x : n → ℝ) (y : m → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (A *ᵥ x) +
    Real.sqrt (∑ j, ((A.transpose *ᵥ y) j) ^ 2)

theorem ballGapAtMost_iff [Nonempty m] (A : Matrix m n ℝ)
    (x : n → ℝ) (y : m → ℝ) (ε : ℝ) :
    BallGapAtMost A x y ε ↔ ballGap A x y ≤ ε := by
  constructor
  · intro h
    have hs : Finset.univ.sup' Finset.univ_nonempty (A *ᵥ x) ≤
        ε - Real.sqrt (∑ j, ((A.transpose *ᵥ y) j) ^ 2) := by
      apply Finset.sup'_le
      intro i hi
      have := h i
      linarith
    dsimp [ballGap]
    linarith
  · intro h i
    have hs := Finset.le_sup' (A *ᵥ x) (Finset.mem_univ i)
    dsimp [ballGap] at h
    linarith

theorem padBall_fullGap_iff (A : Matrix m n ℝ) (ρ : M → m)
    (hρ : Function.Surjective ρ) (x : n ⊕ e → ℝ) (y : M → ℝ) (ε : ℝ) :
    BallGapAtMost (padBallMatrix A ρ) x y ε ↔
      BallGapAtMost A (fun j => x (Sum.inl j)) (aggregate ρ y) ε := by
  unfold BallGapAtMost
  rw [padBall_mulVec, padBall_transpose_sq]
  constructor
  · intro h i
    obtain ⟨i', hi⟩ := hρ i
    simpa only [hi] using h i'
  · intro h i
    exact h (ρ i)

theorem padBall_gap [Nonempty m] [Nonempty M] (A : Matrix m n ℝ) (ρ : M → m)
    (hρ : Function.Surjective ρ) (x : n ⊕ e → ℝ) (y : M → ℝ) :
    ballGap (padBallMatrix A ρ) x y =
      ballGap A (fun j => x (Sum.inl j)) (aggregate ρ y) := by
  apply le_antisymm
  · apply (ballGapAtMost_iff _ _ _ _).mp
    apply (padBall_fullGap_iff A ρ hρ x y _).mpr
    exact (ballGapAtMost_iff _ _ _ _).mpr le_rfl
  · apply (ballGapAtMost_iff _ _ _ _).mp
    apply (padBall_fullGap_iff A ρ hρ x y _).mp
    exact (ballGapAtMost_iff _ _ _ _).mpr le_rfl

end Ball

end
end DimensionExtension
end Matvec
