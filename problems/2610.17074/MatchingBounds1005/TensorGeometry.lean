import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Actual finite Hilbert tensor coordinates, with their Frobenius inner
product. No tensor-norm or projection estimate is postulated. -/
noncomputable section
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.TensorGeometry

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Tensor (d k : ℕ) := EuclideanSpace ℝ (Fin k → Fin d)

def productTensor {d k : ℕ} (v : Fin k → Vec d) : Tensor d k :=
  (WithLp.equiv 2 _).symm (fun idx => ∏ j, v j (idx j))

@[simp] theorem productTensor_apply {d k : ℕ} (v : Fin k → Vec d)
    (idx : Fin k → Fin d) : productTensor v idx = ∏ j, v j (idx j) := rfl

theorem productTensor_inner {d k : ℕ} (u v : Fin k → Vec d) :
    ⟪productTensor u, productTensor v⟫_ℝ = ∏ j, ⟪u j, v j⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, productTensor_apply,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (j : Fin k) (i : Fin d) => v j i * u j i)).symm

theorem productTensor_norm_sq {d k : ℕ} (v : Fin k → Vec d) :
    ‖productTensor v‖ ^ 2 = ∏ j, ‖v j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, productTensor_inner]
  simp only [real_inner_self_eq_norm_sq]

theorem productTensor_norm {d k : ℕ} (v : Fin k → Vec d) :
    ‖productTensor v‖ = ∏ j, ‖v j‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg (fun j _ => norm_nonneg (v j)))).mp
  rw [productTensor_norm_sq, Finset.prod_pow]

def rankOne {d : ℕ} (k : ℕ) (b : Vec d) : Tensor d k := productTensor (fun _ => b)

theorem rankOne_inner {d : ℕ} (k : ℕ) (a b : Vec d) :
    ⟪rankOne k a, rankOne k b⟫_ℝ = ⟪a, b⟫_ℝ ^ k := by
  simp only [rankOne, productTensor_inner, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem rankOne_norm {d : ℕ} (k : ℕ) (b : Vec d) : ‖rankOne k b‖ = ‖b‖ ^ k := by
  simp only [rankOne, productTensor_norm, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

def oneOutside {d k : ℕ} (w q : Vec d) (i : Fin k) : Tensor d k :=
  productTensor (Function.update (fun _ => w) i q)

theorem productTensor_inner_zero_of_factor {d k : ℕ} (u v : Fin k → Vec d)
    (i : Fin k) (hi : ⟪u i, v i⟫_ℝ = 0) :
    ⟪productTensor u, productTensor v⟫_ℝ = 0 := by
  rw [productTensor_inner]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem rankOne_oneOutside_inner {d k : ℕ} (w q : Vec d)
    (hq : ⟪w, q⟫_ℝ = 0) (i : Fin k) :
    ⟪rankOne k w, oneOutside w q i⟫_ℝ = 0 := by
  apply productTensor_inner_zero_of_factor _ _ i
  simpa only [Function.update_self] using hq

theorem oneOutside_pairwise {d k : ℕ} (w q : Vec d)
    (hq : ⟪w, q⟫_ℝ = 0) {i j : Fin k} (hij : i ≠ j) :
    ⟪oneOutside w q i, oneOutside w q j⟫_ℝ = 0 := by
  apply productTensor_inner_zero_of_factor _ _ j
  simpa only [Function.update_self, Function.update_of_ne hij.symm] using hq

theorem oneOutside_norm_sq {d k : ℕ} (w q : Vec d) (i : Fin k) :
    ‖oneOutside w q i‖ ^ 2 = ‖q‖ ^ 2 * (‖w‖ ^ 2) ^ (k - 1) := by
  rw [oneOutside, productTensor_norm_sq]
  have he : (fun j => ‖Function.update (fun _ : Fin k => w) i q j‖ ^ 2) =
      Function.update (fun _ : Fin k => ‖w‖ ^ 2) i (‖q‖ ^ 2) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.sdiff_singleton_eq_erase]

def firstOrderTensor {d : ℕ} (k : ℕ) (w q : Vec d) : Tensor d k :=
  rankOne k w + ∑ i, oneOutside w q i

theorem firstOrderTensor_norm_sq {d k : ℕ} (w q : Vec d) (hq : ⟪w, q⟫_ℝ = 0) :
    ‖firstOrderTensor k w q‖ ^ 2 =
      (‖w‖ ^ 2) ^ k + k * ‖q‖ ^ 2 * (‖w‖ ^ 2) ^ (k - 1) := by
  have hc : ⟪rankOne k w, ∑ i : Fin k, oneOutside w q i⟫_ℝ = 0 := by
    rw [inner_sum]
    exact Finset.sum_eq_zero (fun i _ => rankOne_oneOutside_inner w q hq i)
  have hs : ‖∑ i : Fin k, oneOutside w q i‖ ^ 2 =
      ∑ i : Fin k, ‖oneOutside w q i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum, Finset.sum_eq_single i]
    · exact real_inner_self_eq_norm_sq _
    · intro j _ hji
      exact oneOutside_pairwise w q hq hji.symm
    · simp
  rw [firstOrderTensor, norm_add_sq_real, hc, hs, rankOne_norm]
  simp only [oneOutside_norm_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_zero, add_zero]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
  ring

theorem oneOutside_inner {d k : ℕ} (w q : Vec d) (i : Fin k) (v : Fin k → Vec d) :
    ⟪oneOutside w q i, productTensor v⟫_ℝ =
      ⟪q, v i⟫_ℝ * ∏ j ∈ Finset.univ.erase i, ⟪w, v j⟫_ℝ := by
  rw [oneOutside, productTensor_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem firstOrderTensor_inner_eq {d k : ℕ} (w q : Vec d) (v : Fin k → Vec d)
    (i : Fin k) (hv : ∀ j, j ≠ i → ⟪q, v j⟫_ℝ = 0) :
    ⟪rankOne k (w + q), productTensor v⟫_ℝ =
      ⟪firstOrderTensor k w q, productTensor v⟫_ℝ := by
  have hsum : (∑ j : Fin k, ⟪oneOutside w q j, productTensor v⟫_ℝ) =
      ⟪oneOutside w q i, productTensor v⟫_ℝ := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [oneOutside_inner, hv j hji, zero_mul]
    · simp
  rw [firstOrderTensor, inner_add_left, sum_inner, hsum, oneOutside_inner,
    rankOne, rankOne, productTensor_inner, productTensor_inner]
  rw [← Finset.mul_prod_erase _ (fun j : Fin k => ⟪w + q, v j⟫_ℝ) (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j : Fin k => ⟪w, v j⟫_ℝ) (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, ⟪w + q, v j⟫_ℝ) =
      ∏ j ∈ Finset.univ.erase i, ⟪w, v j⟫_ℝ := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [inner_add_left, hv j (Finset.mem_erase.mp hj).1, add_zero]
  rw [he, inner_add_left]
  ring

/-- All full tensor observation rows with at most one factor outside W.
Symmetric value/gradient observation spaces are subspaces of this space. -/
def observationSpace {d : ℕ} (k : ℕ) (W : Submodule ℝ (Vec d)) :
    Submodule ℝ (Tensor d k) := Submodule.span ℝ
      {t | ∃ (v : Fin k → Vec d) (i : Fin k),
        (∀ j, j ≠ i → v j ∈ W) ∧ t = productTensor v}

theorem rankOne_sub_firstOrder_orthogonal {d k : ℕ} (W : Submodule ℝ (Vec d))
    (w q : Vec d) (hq : q ∈ Wᗮ) :
    rankOne k (w + q) - firstOrderTensor k w q ∈ (observationSpace k W)ᗮ := by
  let r := rankOne k (w + q) - firstOrderTensor k w q
  have hle : observationSpace k W ≤ LinearMap.ker (innerSL ℝ r).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro t ⟨v, i, hv, rfl⟩
    change ⟪r, productTensor v⟫_ℝ = 0
    change ⟪rankOne k (w + q) - firstOrderTensor k w q, productTensor v⟫_ℝ = 0
    rw [inner_sub_left, firstOrderTensor_inner_eq w q v i
      (fun j hj => W.inner_left_of_mem_orthogonal (hv j hj) hq), sub_self]
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro y hy
  exact hle hy

attribute [local irreducible] Submodule.orthogonalProjection

/-- The source rank-one estimate, for every subspace of the actual tensor
observation envelope. In particular, no extra factor of the query count is
introduced by taking the whole history's observation span. -/
theorem rankOne_projection_bound {d k : ℕ} (hk : 1 ≤ k)
    (W : Submodule ℝ (Vec d)) (V : Submodule ℝ (Tensor d k))
    (hV : V ≤ observationSpace k W) (b : Vec d) (hb : ‖b‖ = 1) :
    ‖V.orthogonalProjection (rankOne k b)‖ ^ 2 ≤
      k * (‖W.orthogonalProjection b‖ ^ 2) ^ (k - 1) := by
  let w : Vec d := W.orthogonalProjection b
  let q : Vec d := b - w
  have hw : w ∈ W := (W.orthogonalProjection b).property
  have hq : q ∈ Wᗮ := W.sub_orthogonalProjection_mem_orthogonal b
  have horth : ⟪w, q⟫_ℝ = 0 := W.inner_right_of_mem_orthogonal hw hq
  have hsum : w + q = b := by dsimp only [q]; abel
  have hr : rankOne k b - firstOrderTensor k w q ∈ Vᗮ := by
    have ho := rankOne_sub_firstOrder_orthogonal (k := k) W w q hq
    rw [hsum] at ho
    exact (Submodule.mem_orthogonal' _ _).mpr
      (fun y hy => (Submodule.mem_orthogonal' _ _).mp ho y (hV hy))
  have hp : V.orthogonalProjection (rankOne k b) =
      V.orthogonalProjection (firstOrderTensor k w q) := by
    have hz := Submodule.orthogonalProjection_eq_zero_iff.mpr hr
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  have hnorm : ‖V.orthogonalProjection (rankOne k b)‖ ≤ ‖firstOrderTensor k w q‖ := by
    rw [hp]
    exact (V.orthogonalProjection.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right V.orthogonalProjection_norm_le (norm_nonneg _)).trans_eq
        (one_mul _))
  have hpy : ‖w‖ ^ 2 + ‖q‖ ^ 2 = 1 := by
    have h := norm_add_sq_real w q
    rw [hsum, hb, horth] at h
    nlinarith
  have hpow : (‖w‖ ^ 2) ^ k = (‖w‖ ^ 2) ^ (k - 1) * ‖w‖ ^ 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk).symm]
    rw [pow_succ]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  calc
    _ ≤ ‖firstOrderTensor k w q‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
    _ = (‖w‖ ^ 2) ^ k + k * ‖q‖ ^ 2 * (‖w‖ ^ 2) ^ (k - 1) :=
      firstOrderTensor_norm_sq w q horth
    _ ≤ k * (‖w‖ ^ 2) ^ (k - 1) := by
      rw [hpow]
      have hnon := mul_nonneg (sub_nonneg.mpr hkR)
        (mul_nonneg (sq_nonneg ‖w‖) (pow_nonneg (sq_nonneg ‖w‖) (k - 1)))
      rw [show ‖q‖ ^ 2 = 1 - ‖w‖ ^ 2 by linarith]
      calc
        _ = k * (‖w‖ ^ 2) ^ (k - 1) -
            (k - 1 : ℝ) * (‖w‖ ^ 2 * (‖w‖ ^ 2) ^ (k - 1)) := by ring
        _ ≤ _ := sub_le_self _ hnon
    _ = _ := rfl

end MatchingBounds1005.TensorGeometry
