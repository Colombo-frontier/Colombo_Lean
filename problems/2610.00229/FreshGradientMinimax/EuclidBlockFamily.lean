import FreshGradientMinimax.EuclidBlocks
import Mathlib.Logic.Equiv.Fin.Basic

/-! A finite family of Euclidean blocks, flattened into one Euclidean space.
The norm is the Euclidean norm across all blocks. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

theorem sum_fin_blocks {k m : ℕ} (f : Fin (k * m) → ℝ) :
    ∑ j, f j = ∑ i : Fin k, ∑ a : Fin m, f (finProdFinEquiv (i, a)) := by
  rw [← (finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m)).sum_comp f, Fintype.sum_prod_type]

def euclidBlock {k m : ℕ} (i : Fin k) : Euclid (k * m) →L[ℝ] Euclid m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (WithLp.equiv 2 _).symm (fun a => x (finProdFinEquiv (i, a)))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

def euclidJoin {k m : ℕ} (x : Fin k → Euclid m) : Euclid (k * m) :=
  (WithLp.equiv 2 _).symm (fun j => x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

@[simp]
theorem euclidBlock_apply {k m : ℕ} (i : Fin k) (x : Euclid (k * m)) (a : Fin m) :
    euclidBlock i x a = x (finProdFinEquiv (i, a)) := rfl

@[simp]
theorem euclidJoin_apply {k m : ℕ} (x : Fin k → Euclid m) (i : Fin k) (a : Fin m) :
    euclidJoin x (finProdFinEquiv (i, a)) = x i a := by
  change x (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, a))).2 = x i a
  rw [Equiv.symm_apply_apply]

@[simp]
theorem euclidBlock_join {k m : ℕ} (x : Fin k → Euclid m) (i : Fin k) :
    euclidBlock i (euclidJoin x) = x i := by ext a; simp

theorem euclidJoin_blocks {k m : ℕ} (x : Euclid (k * m)) :
    euclidJoin (fun i => euclidBlock i x) = x := by
  ext j
  change x (finProdFinEquiv (finProdFinEquiv.symm j)) = x j
  rw [Equiv.apply_symm_apply]

theorem euclid_ext_blocks {k m : ℕ} {x y : Euclid (k * m)}
    (h : ∀ i, euclidBlock i x = euclidBlock i y) : x = y := by
  calc
    x = euclidJoin (fun i => euclidBlock i x) := (euclidJoin_blocks x).symm
    _ = euclidJoin (fun i => euclidBlock i y) := congrArg euclidJoin (funext h)
    _ = y := euclidJoin_blocks y

theorem euclid_norm_sq_blocks {k m : ℕ} (x : Euclid (k * m)) :
    ‖x‖ ^ 2 = ∑ i : Fin k, ‖euclidBlock i x‖ ^ 2 := by
  rw [euclid_norm_sq, sum_fin_blocks]
  simp only [euclid_norm_sq, euclidBlock_apply]

theorem euclidJoin_norm_sq {k m : ℕ} (x : Fin k → Euclid m) :
    ‖euclidJoin x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [euclid_norm_sq_blocks]
  simp only [euclidBlock_join]

theorem euclid_inner_family {k m : ℕ} (x y : Euclid (k * m)) :
    ⟪x, y⟫_ℝ = ∑ i : Fin k, ⟪euclidBlock i x, euclidBlock i y⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply, star_trivial]
  rw [sum_fin_blocks]
  rfl

theorem euclidJoin_sub {k m : ℕ} (x y : Fin k → Euclid m) :
    euclidJoin x - euclidJoin y = euclidJoin (fun i => x i - y i) := by
  apply euclid_ext_blocks
  intro i
  simp only [map_sub, euclidBlock_join]

theorem euclidJoin_norm_bound {k m : ℕ} {C : ℝ} (hC : 0 ≤ C) (x : Fin k → Euclid m)
    (hx : ∀ i, ‖x i‖ ≤ C) : ‖euclidJoin x‖ ≤ C * Real.sqrt k := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [euclidJoin_norm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  calc
    _ ≤ ∑ _ : Fin k, C ^ 2 := Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx i) 2)
    _ = _ := by simp [mul_comm]

end FreshGradientMinimax
