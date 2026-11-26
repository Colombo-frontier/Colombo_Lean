import GradientHessian.LatchLocalDerivatives
import GradientHessian.LocalizedProductDerivatives

noncomputable section
namespace GradientHessian.LatchDerivativeSums

open scoped InnerProductSpace
open EuclideanRegisters LatchActivation LatchChain LatchLocalDerivatives Profiles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def selfTerm (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (U : Registers E (k + 1)) : ℝ := selfResidual (r i) (v i) (U i)

def edgeTerm (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin k) (U : Registers E (k + 1)) : ℝ :=
  incoming (r i.succ) (v i.succ) (U i.succ) *
    chi (u (r i.castSucc) (v i.castSucc) (U i.castSucc))

def selfSum (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (U : Registers E (k + 1)) : ℝ := ∑ i, selfTerm k v r i U

def edgeSum (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (U : Registers E (k + 1)) : ℝ := ∑ i, edgeTerm k v r i U

theorem selfSum_succ (k : ℕ) (v : Fin (k + 2) → E) (r : Fin (k + 2) → ℝ)
    (U : Registers E (k + 2)) : selfSum (k + 1) v r U =
    selfResidual (r 0) (v 0) (U 0) +
      selfSum k (fun i => v i.succ) (fun i => r i.succ) (tail E (k + 1) U) := by
  rw [selfSum, Fin.sum_univ_succ]
  rfl

theorem edgeSum_succ (k : ℕ) (v : Fin (k + 2) → E) (r : Fin (k + 2) → ℝ)
    (U : Registers E (k + 2)) : edgeSum (k + 1) v r U =
    incoming (r 1) (v 1) (U 1) * chi (u (r 0) (v 0) (U 0)) +
      edgeSum k (fun i => v i.succ) (fun i => r i.succ) (tail E (k + 1) U) := by
  rw [edgeSum, Fin.sum_univ_succ]
  rfl

theorem atom_eq_quadratic_residual {r : ℝ} (hr : r ≠ 0) (a : ℝ) (v x : E) :
    atom a r v x = (4 / r) * ‖x‖ ^ 2 + selfResidual r v x - a * incoming r v x := by
  have h := atom_residual_eq hr a v x
  unfold selfResidual incoming
  linarith only [h]

theorem self_eq_sums (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (hr : ∀ i, r i ≠ 0) (a : ℝ) (U : Registers E (k + 1)) :
    self k v r a U = publicQuadratic k r U + selfSum k v r U - edgeSum k v r U -
      a * incoming (r 0) (v 0) (U 0) := by
  induction k generalizing a with
  | zero =>
    simpa [self, publicQuadratic, selfSum, selfTerm, edgeSum] using
      atom_eq_quadratic_residual (hr 0) a (v 0) (U 0)
  | succ k ih =>
    rw [self, ih _ _ (fun i => hr i.succ), publicQuadratic_succ, selfSum_succ, edgeSum_succ,
      atom_eq_quadratic_residual (hr 0)]
    simp only [tail_apply, Fin.succ_zero_eq_one]
    ring

theorem residual_eq_sums (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (hr : ∀ i, r i ≠ 0) : residual k v r = fun U => selfSum k v r U - edgeSum k v r U := by
  funext U
  rw [LatchChain.residual, self_eq_sums k v r hr]
  ring

theorem projection_norm_le {k : ℕ} (i : Fin k) :
    ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => E) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro U
  simpa only [one_mul] using PiLp.norm_apply_le U i

theorem derivative_projection_le {k : ℕ} (i : Fin k) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {n : ℕ} (hn : n ≤ 3) (U : Registers E k) :
    ‖iteratedFDeriv ℝ n (fun X : Registers E k => f (X i)) U‖ ≤
      ‖iteratedFDeriv ℝ n f (U i)‖ := by
  let A : Registers E k →L[ℝ] E := PiLp.proj 2 _ i
  change ‖iteratedFDeriv ℝ n (f ∘ A) U‖ ≤ _
  rw [A.iteratedFDeriv_comp_right hf U (by exact_mod_cast hn)]
  apply (show ‖(iteratedFDeriv ℝ n f (A U)).compContinuousLinearMap (fun _ => A)‖ ≤
      ‖iteratedFDeriv ℝ n f (A U)‖ * ‖A‖ ^ n from by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ n f (A U)).norm_compContinuousLinearMap_le (fun _ => A)).trans
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg A) (projection_norm_le i))

theorem selfTerm_contDiff (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) : ContDiff ℝ 3 (selfTerm k v r i) :=
  (selfResidual_contDiff (r i) (v i)).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => E) i).contDiff

theorem edgeTerm_contDiff (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin k) : ContDiff ℝ 3 (edgeTerm k v r i) :=
  ((incoming_contDiff (r i.succ) (v i.succ)).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => E) i.succ).contDiff).mul
      ((contDiff_chi.comp (u_contDiff (r i.castSucc) (v i.castSucc))).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => E) i.castSucc).contDiff)

theorem selfTerm_derivative_bound (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hr : 0 < r i) (hv : ‖v i‖ = 1) {n : ℕ} (hn : n ≤ 3)
    (U : Registers E (k + 1)) :
    ‖iteratedFDeriv ℝ n (selfTerm k v r i) U‖ ≤ (8 * localConstant n) * (r i) ^ (1 - (n : ℤ)) :=
  (derivative_projection_le i (selfResidual_contDiff _ _) hn U).trans
    (selfResidual_derivative_bound hr _ _ hv hn)

theorem lifted_incoming_derivative_bound (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hr : 0 < r i) (hv : ‖v i‖ = 1) {n : ℕ} (hn : n ≤ 3)
    (U : Registers E (k + 1)) :
    ‖iteratedFDeriv ℝ n (fun X : Registers E (k + 1) => incoming (r i) (v i) (X i)) U‖ ≤
      (8 * localConstant n) * (r i) ^ (1 - (n : ℤ)) :=
  (derivative_projection_le i (incoming_contDiff _ _) hn U).trans
    (incoming_derivative_bound hr _ _ hv hn)

theorem lifted_gate_derivative_bound (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hr : 0 < r i) (hv : ‖v i‖ = 1) {n : ℕ} (hn : n ≤ 3)
    (U : Registers E (k + 1)) :
    ‖iteratedFDeriv ℝ n (fun X : Registers E (k + 1) => chi (u (r i) (v i) (X i))) U‖ ≤
      localConstant n / (r i) ^ n := by
  apply (derivative_projection_le i (contDiff_chi.comp (u_contDiff _ _)) hn U).trans
  simpa only [scalarProfile, Fin.reduceFinMk, ↓reduceIte] using
    scaled_composite_derivative_bound 2 hr (v i) (U i) hv hn

def edgeConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (8 * localConstant i) * localConstant (n - i) * 2 ^ (n - i)

theorem edgeConstant_nonneg (n : ℕ) : 0 ≤ edgeConstant n := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by have h := localConstant_pos i; positivity))
    (localConstant_pos _).le) (by positivity)

theorem edgeTerm_derivative_bound (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin k) (hr : ∀ j, 0 < r j) (hv : ∀ j, ‖v j‖ = 1)
    (hscale : r i.succ = 2 * r i.castSucc) {n : ℕ} (hn : n ≤ 3)
    (U : Registers E (k + 1)) :
    ‖iteratedFDeriv ℝ n (edgeTerm k v r i) U‖ ≤ edgeConstant n * (r i.succ) ^ (1 - (n : ℤ)) := by
  have hB : ContDiff ℝ 3 (fun X : Registers E (k + 1) => incoming (r i.succ) (v i.succ) (X i.succ)) :=
    (incoming_contDiff _ _).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => E) i.succ).contDiff
  have hgate : ContDiff ℝ 3 (fun X : Registers E (k + 1) => chi (u (r i.castSucc) (v i.castSucc) (X i.castSucc))) :=
    (contDiff_chi.comp (u_contDiff _ _)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => E) i.castSucc).contDiff
  apply (norm_iteratedFDeriv_mul_le hB hgate U (by exact_mod_cast hn)).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * (8 * localConstant j) *
        localConstant (n - j) * 2 ^ (n - j)) * (r i.succ) ^ (1 - (n : ℤ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have h := mul_le_mul
        (mul_le_mul_of_nonneg_left (lifted_incoming_derivative_bound k v r i.succ
          (hr _) (hv _) (hjn.trans hn) U) (Nat.cast_nonneg (n.choose j)))
        (lifted_gate_derivative_bound k v r i.castSucc (hr _) (hv _)
          ((Nat.sub_le n j).trans hn) U) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg (n.choose j)) (mul_nonneg
          (mul_nonneg (by norm_num) (localConstant_pos j).le) (zpow_nonneg (hr i.succ).le _)))
      apply h.trans_eq
      rw [zpow_sub₀ (hr i.succ).ne', zpow_one, zpow_natCast,
        zpow_sub₀ (hr i.succ).ne', zpow_one, zpow_natCast]
      rw [hscale, mul_pow, mul_pow]
      have hp : (r i.castSucc) ^ n = (r i.castSucc) ^ j * (r i.castSucc) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_of_le hjn]
      have h2 : (2 : ℝ) ^ n = 2 ^ j * 2 ^ (n - j) := by rw [← pow_add, Nat.add_sub_of_le hjn]
      rw [hp, h2]
      field_simp [(hr i.castSucc).ne', pow_ne_zero (n - j) (by norm_num : (2 : ℝ) ≠ 0),
        pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem sourceScale_adjacent {k : ℕ} (s : ℝ) (i : Fin k) :
    sourceScale s i.succ = 2 * sourceScale s i.castSucc := by
  simp only [sourceScale, Fin.val_succ, Fin.coe_castSucc, pow_succ]
  ring

theorem source_weight_sum_le (k : ℕ) {s : ℝ} (hs : 0 < s) {n : ℕ}
    (hn2 : 2 ≤ n) (hn3 : n ≤ 3) :
    (∑ i : Fin (k + 1), (sourceScale s i) ^ (1 - (n : ℤ))) ≤ 2 * s ^ (1 - (n : ℤ)) := by
  induction k generalizing s with
  | zero =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, add_zero, sourceScale, Fin.val_zero, pow_zero, mul_one]
    have h := zpow_nonneg hs.le (1 - (n : ℤ))
    linarith
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    have he : (∑ i : Fin (k + 1), (sourceScale s i.succ) ^ (1 - (n : ℤ))) =
        ∑ i : Fin (k + 1), (sourceScale (2 * s) i) ^ (1 - (n : ℤ)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp only [sourceScale, Fin.val_succ, pow_succ]
      ring
    rw [he]
    simp only [sourceScale, Fin.val_zero, pow_zero, mul_one]
    have ht := ih (s := 2 * s) (mul_pos (by norm_num) hs)
    simp only [sourceScale] at ht
    have hratio : (2 * s) ^ (1 - (n : ℤ)) ≤ (1 / 2 : ℝ) * s ^ (1 - (n : ℤ)) := by
      rw [mul_zpow]
      interval_cases n <;> norm_num [zpow_neg]
      exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr (sq_nonneg s))
    nlinarith only [ht, hratio]

theorem successor_weight_sum_le (k : ℕ) (r : Fin (k + 1) → ℝ) (hr : ∀ i, 0 < r i) (n : ℕ) :
    (∑ i : Fin k, (r i.succ) ^ (1 - (n : ℤ))) ≤ ∑ i : Fin (k + 1), (r i) ^ (1 - (n : ℤ)) := by
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (zpow_nonneg (hr 0).le _)

theorem norm_derivative_sum_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} (f : Fin m → F → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) {n : ℕ} (hn : n ≤ 3) (X : F) :
    ‖iteratedFDeriv ℝ n (fun Y => ∑ i, f i Y) X‖ ≤ ∑ i, ‖iteratedFDeriv ℝ n (f i) X‖ := by
  have he := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (u := Finset.univ) (i := n)
    (fun i _ => (hf i).of_le (by exact_mod_cast hn))) X
  simp only [Finset.sum_apply] at he
  rw [he]
  exact norm_sum_le _ _

theorem residual_higher_derivative_bound (k : ℕ) (v : Fin (k + 1) → E) {s : ℝ}
    (hs : 0 < s) (hv : ∀ i, ‖v i‖ = 1) {n : ℕ} (hn2 : 2 ≤ n) (hn3 : n ≤ 3)
    (U : Registers E (k + 1)) :
    ‖iteratedFDeriv ℝ n (residual k v (sourceScale s)) U‖ ≤
      (2 * (8 * localConstant n + edgeConstant n)) * s ^ (1 - (n : ℤ)) := by
  let r : Fin (k + 1) → ℝ := sourceScale s
  have hr : ∀ i, 0 < r i := sourceScale_pos hs
  have hself : ContDiff ℝ 3 (selfSum k v r) :=
    ContDiff.sum (fun i _ => selfTerm_contDiff k v r i)
  have hedge : ContDiff ℝ 3 (edgeSum k v r) :=
    ContDiff.sum (fun i _ => edgeTerm_contDiff k v r i)
  rw [residual_eq_sums k v r (fun i => (hr i).ne')]
  have hadd := LocalizedProductDerivatives.norm_iteratedFDeriv_sub_le
    (hself.of_le (by exact_mod_cast hn3)).contDiffAt
    (hedge.of_le (by exact_mod_cast hn3)).contDiffAt (x := U)
  have hselfnorm : ‖iteratedFDeriv ℝ n (selfSum k v r) U‖ ≤
      (8 * localConstant n) * ∑ i, (r i) ^ (1 - (n : ℤ)) := by
    apply (norm_derivative_sum_le (selfTerm k v r) (selfTerm_contDiff k v r) hn3 U).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact selfTerm_derivative_bound k v r i (hr i) (hv i) hn3 U
  have hedgenorm : ‖iteratedFDeriv ℝ n (edgeSum k v r) U‖ ≤
      edgeConstant n * ∑ i : Fin (k + 1), (r i) ^ (1 - (n : ℤ)) := by
    apply (norm_derivative_sum_le (edgeTerm k v r) (edgeTerm_contDiff k v r) hn3 U).trans
    calc
      _ ≤ edgeConstant n * ∑ i : Fin k, (r i.succ) ^ (1 - (n : ℤ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        exact edgeTerm_derivative_bound k v r i hr hv (sourceScale_adjacent s i) hn3 U
      _ ≤ _ := mul_le_mul_of_nonneg_left (successor_weight_sum_le k r hr n) (edgeConstant_nonneg n)
  have hsum := source_weight_sum_le k hs hn2 hn3
  have hc : 0 ≤ 8 * localConstant n + edgeConstant n :=
    add_nonneg (by have h := localConstant_pos n; positivity) (edgeConstant_nonneg n)
  have hscale := mul_le_mul_of_nonneg_left hsum hc
  change (8 * localConstant n + edgeConstant n) * (∑ i, (r i) ^ (1 - (n : ℤ))) ≤ _ at hscale
  nlinarith only [hadd, hselfnorm, hedgenorm, hscale]

theorem port_derivative_bound (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (hr : 0 < r (Fin.last k)) (hv : ‖v (Fin.last k)‖ = 1) {n : ℕ} (hn : n ≤ 3)
    (U : Registers E (k + 1)) :
    ‖iteratedFDeriv ℝ n (port k v r) U‖ ≤ localConstant n / (r (Fin.last k)) ^ n := by
  apply (derivative_projection_le (Fin.last k) (contDiff_varpi.comp (u_contDiff _ _)) hn U).trans
  simpa only [scalarProfile, Fin.reduceFinMk, ↓reduceIte] using
    scaled_composite_derivative_bound 3 hr (v (Fin.last k)) (U (Fin.last k)) hv hn

end GradientHessian.LatchDerivativeSums
