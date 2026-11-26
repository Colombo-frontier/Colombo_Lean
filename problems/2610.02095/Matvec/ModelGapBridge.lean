import Matvec.Model
import Matvec.Simplex
import Matvec.BallNormalization

/-! Bridges from the actual quantified algorithm success predicate to the
deterministic game-reduction gap predicates, including finite reindexing. -/
namespace Matvec
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem simplexFeasible_vertex {n : ℕ} (i : Fin n) :
    SimplexFeasible (Pi.single i 1) := by
  constructor
  · intro j; by_cases h : j = i <;> simp [h, Pi.single_apply]
  · simp

theorem gameSuccess_simplex_fullGap {m n : ℕ} (A : Payoff m n)
    (ε : ℝ) (out : Query m n) (h : GameSuccess .simplexSimplex A ε out) :
    InSimplex out.1 ∧ InSimplex out.2 ∧ FullGapAtMost A out.1 out.2 ε := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro i j
  have hg := h.2.2 (Pi.single j 1) (Pi.single i 1)
    (simplexFeasible_vertex j) (simplexFeasible_vertex i)
  simpa [payoff, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply, mul_comm] using hg

theorem payoff_transpose {m n : ℕ} (A : Payoff m n) (x : Vec n) (y : Vec m) :
    payoff A x y = x ⬝ᵥ (A.transpose *ᵥ y) := by
  rw [payoff, dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem simplex_weighted_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : InSimplex w)
    (f : ι → ℝ) (C : ℝ) (hf : ∀ i, f i ≤ C) : w ⬝ᵥ f ≤ C := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hf i) (hw.1 i))
  simpa only [← Finset.sum_mul, hw.2, one_mul] using h

theorem fullGapAtMost_gameSuccess {m n : ℕ} (A : Payoff m n)
    (x : Vec n) (y : Vec m) (ε : ℝ) (hx : InSimplex x) (hy : InSimplex y)
    (hgap : FullGapAtMost A x y ε) : GameSuccess .simplexSimplex A ε (x, y) := by
  refine ⟨hx, hy, ?_⟩
  intro x' y' hx' hy'
  have hxi : InSimplex x' := hx'
  have hyi : InSimplex y' := hy'
  have hi (i : Fin m) : (A *ᵥ x) i - payoff A x' y ≤ ε := by
    have h := simplex_weighted_le x' hxi
      (fun j => (A *ᵥ x) i - (A.transpose *ᵥ y) j) ε (hgap i)
    simp only [dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hxi.2, one_mul] at h
    rw [payoff_transpose]
    exact h
  have h := simplex_weighted_le y' hyi (fun i => (A *ᵥ x) i - payoff A x' y) ε hi
  simp only [dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hyi.2, one_mul] at h
  exact h

theorem payoff_reindex {m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (er : Fin m ≃ ι) (ec : Fin n ≃ κ) (A : Matrix ι κ ℝ) (x : κ → ℝ) (y : ι → ℝ) :
    payoff (A.submatrix er ec) (fun j => x (ec j)) (fun i => y (er i)) = y ⬝ᵥ (A *ᵥ x) := by
  simp only [payoff, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  calc
    _ = ∑ i : Fin m, y (er i) * ∑ j : κ, A (er i) j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ec.sum_comp (fun j => A (er i) j * x j)]
    _ = _ := er.sum_comp (fun i => y i * ∑ j, A i j * x j)

def signedRowEquiv (d : ℕ) : (Fin d × Bool) ≃ (Fin d ⊕ Fin d) where
  toFun := BallNormalization.signedRowIndex
  invFun := Sum.elim (fun i => (i, false)) (fun i => (i, true))
  left_inv := by rintro ⟨i, b⟩; cases b <;> rfl
  right_inv := by intro j; cases j <;> rfl

def modelBallMatrix {d m n : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (b : EuclideanSpace ℝ (Fin d)) (α β : ℝ)
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit)) : Payoff m n :=
  (-ballMatrix H (fun i => b i) α β).submatrix er ec

def modelBallPrimal {d n : ℕ} (ec : Fin n ≃ (Fin d ⊕ Unit))
    (z : EuclideanSpace ℝ (Fin d)) (s : ℝ) : Vec n :=
  fun j => Sum.elim (fun i => z i) (fun _ => s) (ec j)

def modelBallDual {d m : ℕ} (er : Fin m ≃ (Fin d ⊕ Fin d))
    (y : Fin d × Bool → ℝ) : Vec m :=
  fun i => y ((signedRowEquiv d).symm (er i))

theorem modelBallPrimal_feasible {d n : ℕ} (ec : Fin n ≃ (Fin d ⊕ Unit))
    (z : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    InBall (modelBallPrimal ec z s) ↔ BallReduction.Feasible z s := by
  unfold InBall modelBallPrimal
  rw [ec.sum_comp (fun j => (Sum.elim (fun i => z i) (fun _ => s) j) ^ 2)]
  exact BallNormalization.homogeneous_feasible_iff z s

theorem modelBallDual_feasible {d m : ℕ} (er : Fin m ≃ (Fin d ⊕ Fin d))
    (y : Fin d × Bool → ℝ) :
    SimplexFeasible (modelBallDual er y) ↔ BallReduction.RowSimplex y := by
  let he := er.trans (signedRowEquiv d).symm
  change ((∀ i, 0 ≤ y (he i)) ∧ ∑ i, y (he i) = 1) ↔
    ((∀ j, 0 ≤ y j) ∧ ∑ j, y j = 1)
  rw [he.sum_comp y]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨fun j => by simpa using h (he.symm j), hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨fun i => h (he i), hs⟩

theorem modelBall_payoff {d m n : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (b z : EuclideanSpace ℝ (Fin d)) (α β s : ℝ)
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit))
    (y : Fin d × Bool → ℝ) :
    payoff (modelBallMatrix H b α β er ec) (modelBallPrimal ec z s) (modelBallDual er y) =
      BallReduction.payoff (Matrix.toEuclideanLin H) b α β z s y := by
  have hp := payoff_reindex er ec (-ballMatrix H (fun i => b i) α β)
    (Sum.elim (fun i => z i) (fun _ => s)) (fun j => y ((signedRowEquiv d).symm j))
  change payoff (modelBallMatrix H b α β er ec) (modelBallPrimal ec z s)
    (modelBallDual er y) = _ at hp
  rw [hp]
  unfold dotProduct BallReduction.payoff
  rw [← (signedRowEquiv d).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Equiv.symm_apply_apply]
  change y j * (((-ballMatrix H (fun i => b i) α β) *ᵥ
    Sum.elim (fun i => z i) (fun _ => s)) (BallNormalization.signedRowIndex j)) = _
  rw [BallNormalization.matrix_rowPayoff]

theorem gameSuccess_ball_fullGap {d m n : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (b z : EuclideanSpace ℝ (Fin d)) (α β s ε : ℝ)
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit))
    (y : Fin d × Bool → ℝ)
    (h : GameSuccess .ballSimplex (modelBallMatrix H b α β er ec) ε
      (modelBallPrimal ec z s, modelBallDual er y)) :
    BallReduction.Feasible z s ∧ BallReduction.RowSimplex y ∧
      BallReduction.FullGapLE (Matrix.toEuclideanLin H) b α β z s y ε := by
  refine ⟨(modelBallPrimal_feasible ec z s).mp h.1,
    (modelBallDual_feasible er y).mp h.2.1, ?_⟩
  intro z' s' hz' y' hy'
  have hg := h.2.2 (modelBallPrimal ec z' s') (modelBallDual er y')
    ((modelBallPrimal_feasible ec z' s').mpr hz') ((modelBallDual_feasible er y').mpr hy')
  simpa only [modelBall_payoff] using hg

def decodeBallVector {d n : ℕ} (ec : Fin n ≃ (Fin d ⊕ Unit)) (x : Vec n) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => x (ec.symm (Sum.inl i)))

def decodeBallScalar {d n : ℕ} (ec : Fin n ≃ (Fin d ⊕ Unit)) (x : Vec n) : ℝ :=
  x (ec.symm (Sum.inr ()))

def decodeBallDual {d m : ℕ} (er : Fin m ≃ (Fin d ⊕ Fin d)) (y : Vec m) :
    Fin d × Bool → ℝ := fun j => y (er.symm (signedRowEquiv d j))

theorem modelBallPrimal_decode {d n : ℕ} (ec : Fin n ≃ (Fin d ⊕ Unit)) (x : Vec n) :
    modelBallPrimal ec (decodeBallVector ec x) (decodeBallScalar ec x) = x := by
  ext j
  change Sum.elim (fun i => x (ec.symm (Sum.inl i)))
    (fun _ => x (ec.symm (Sum.inr ()))) (ec j) = x j
  generalize hj : ec j = u
  cases u with
  | inl i =>
    change x (ec.symm (Sum.inl i)) = x j
    rw [← hj, Equiv.symm_apply_apply]
  | inr u =>
    cases u
    change x (ec.symm (Sum.inr ())) = x j
    rw [← hj, Equiv.symm_apply_apply]

theorem modelBallDual_decode {d m : ℕ} (er : Fin m ≃ (Fin d ⊕ Fin d)) (y : Vec m) :
    modelBallDual er (decodeBallDual er y) = y := by
  ext i
  simp [modelBallDual, decodeBallDual]

/-- Every actual successful model output yields the promised residual bound;
the homogeneous coordinate is proved positive before taking its reciprocal. -/
theorem gameSuccess_ball_residual {d m n : ℕ} (hd : 0 < d)
    (H : Matrix (Fin d) (Fin d) ℝ) (b : EuclideanSpace ℝ (Fin d))
    (α β : ℝ) (hβ : 0 < β) (hα : α = β / (8 * Real.sqrt d))
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit))
    (hH : ∀ z, ‖z‖ ≤ ‖Matrix.toEuclideanLin H z‖) (hb : ‖b‖ ≤ 1)
    (out : Query m n)
    (h : GameSuccess .ballSimplex (modelBallMatrix H b α β er ec) (α / 16) out) :
    0 < decodeBallScalar ec out.1 ∧
      ‖Matrix.toEuclideanLin H ((decodeBallScalar ec out.1)⁻¹ • decodeBallVector ec out.1) - b‖ < 1 / 2 := by
  have hg : GameSuccess .ballSimplex (modelBallMatrix H b α β er ec) (α / 16)
      (modelBallPrimal ec (decodeBallVector ec out.1) (decodeBallScalar ec out.1),
        modelBallDual er (decodeBallDual er out.2)) := by
    rwa [modelBallPrimal_decode, modelBallDual_decode, Prod.mk.eta]
  obtain ⟨hz, hy, hgap⟩ := gameSuccess_ball_fullGap H b (decodeBallVector ec out.1)
    α β (decodeBallScalar ec out.1) (α / 16) er ec (decodeBallDual er out.2) hg
  have hsource := BallNormalization.source_solution_of_matrix_lower_bound H b hH hb
  exact (BallReduction.fullGap_residual hd (Matrix.toEuclideanLin H) b
    (decodeBallVector ec out.1) (decodeBallDual er out.2) hβ hα hz hy hsource hgap).2

theorem simplexFeasible_reindex {n : ℕ} {ι : Type*} [Fintype ι]
    (e : Fin n ≃ ι) (x : ι → ℝ) :
    SimplexFeasible (fun i => x (e i)) ↔ InSimplex x := by
  unfold SimplexFeasible InSimplex
  rw [e.sum_comp x]
  constructor
  · rintro ⟨h, hs⟩; exact ⟨fun i => by simpa using h (e.symm i), hs⟩
  · rintro ⟨h, hs⟩; exact ⟨fun i => h (e i), hs⟩

theorem gameSuccess_reindex_simplex {m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (er : Fin m ≃ ι) (ec : Fin n ≃ κ) (A : Matrix ι κ ℝ)
    (x : κ → ℝ) (y : ι → ℝ) (ε : ℝ)
    (h : GameSuccess .simplexSimplex (A.submatrix er ec) ε
      ((fun j => x (ec j)), (fun i => y (er i)))) :
    InSimplex x ∧ InSimplex y ∧ FullGapAtMost A x y ε := by
  classical
  refine ⟨(simplexFeasible_reindex ec x).mp h.1, (simplexFeasible_reindex er y).mp h.2.1, ?_⟩
  intro i j
  have hxi : InSimplex (Pi.single j (1 : ℝ)) := by
    constructor
    · intro k; by_cases hk : k = j <;> simp [hk, Pi.single_apply]
    · simp
  have hyi : InSimplex (Pi.single i (1 : ℝ)) := by
    constructor
    · intro k; by_cases hk : k = i <;> simp [hk, Pi.single_apply]
    · simp
  have hx : PrimalFeasible .simplexSimplex (fun k => (Pi.single j (1 : ℝ) : κ → ℝ) (ec k)) :=
    (simplexFeasible_reindex ec _).mpr hxi
  have hy : SimplexFeasible (fun k => (Pi.single i (1 : ℝ) : ι → ℝ) (er k)) :=
    (simplexFeasible_reindex er _).mpr hyi
  have hg := h.2.2 _ _ hx hy
  rw [payoff_reindex, payoff_reindex] at hg
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply, mul_comm] using hg

end
end Matvec
