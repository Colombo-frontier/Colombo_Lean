import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

import Mathlib.Tactic.Abel

noncomputable section

open scoped BigOperators InnerProductSpace

namespace NCConcave16991

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Definition 2.1: individual smoothness, expressed for the component gradient maps. -/
def IndividualSmooth {n : ℕ} (G : Fin n → E → F) (s : Set E) (L : ℝ) : Prop :=
  ∀ i, ∀ x ∈ s, ∀ y ∈ s, ‖G i x - G i y‖ ≤ L * ‖x - y‖

/-- Definition 2.1: mean-squared averaged smoothness of component gradient maps. -/
def AveragedSmooth {n : ℕ} (G : Fin n → E → F) (s : Set E) (L : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s,
    (n : ℝ)⁻¹ * ∑ i, ‖G i x - G i y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2

/-- The actual finite-sum average, with the same normalization as the paper. -/
def averageMap {n : ℕ} (G : Fin n → E → F) (x : E) : F :=
  (n : ℝ)⁻¹ • ∑ i, G i x

/-- Individual smoothness implies averaged smoothness with the same constant. -/
theorem IndividualSmooth.averagedSmooth {n : ℕ} {G : Fin n → E → F}
    {s : Set E} {L : ℝ} (hL : 0 ≤ L) (hG : IndividualSmooth G s L) :
    AveragedSmooth G s L := by
  intro x hx y hy
  have hsum : ∑ i, ‖G i x - G i y‖ ^ 2 ≤ (n : ℝ) * (L ^ 2 * ‖x - y‖ ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin n, L ^ 2 * ‖x - y‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hG i x hx y hy) 2
      _ = _ := by simp
  by_cases hn : n = 0
  · simpa [hn] using (mul_nonneg (sq_nonneg L) (sq_nonneg ‖x - y‖))
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnpos.le)
    simpa [← mul_assoc, inv_mul_cancel₀ hnpos.ne'] using h

/-- Jensen's inequality for the square of the norm of an actual finite average. -/
theorem norm_average_sq_le {n : ℕ} (hn : 0 < n) (v : Fin n → F) :
    ‖(n : ℝ)⁻¹ • ∑ i, v i‖ ^ 2 ≤ (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have htriangle : ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
  have hcs : (∑ i, ‖v i‖) ^ 2 ≤ (n : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => ‖v i‖))
  have hsum : ‖∑ i, v i‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖v i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans hcs
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnpos.le), mul_pow]
  have h := mul_le_mul_of_nonneg_left hsum (sq_nonneg ((n : ℝ)⁻¹))
  convert h using 1 <;> field_simp [hnpos.ne'] <;> ring

/-- Lemma A.1(i): AS makes the average gradient L-Lipschitz. -/
theorem AveragedSmooth.average_lipschitz {n : ℕ} (hn : 0 < n)
    {G : Fin n → E → F} {s : Set E} {L : ℝ}
    (hL : 0 ≤ L) (hG : AveragedSmooth G s L) :
    ∀ x ∈ s, ∀ y ∈ s, ‖averageMap G x - averageMap G y‖ ≤ L * ‖x - y‖ := by
  intro x hx y hy
  have hdiff : averageMap G x - averageMap G y =
      (n : ℝ)⁻¹ • ∑ i, (G i x - G i y) := by
    simp [averageMap, Finset.sum_sub_distrib, smul_sub]
  rw [hdiff]
  have hj := (norm_average_sq_le hn (fun i => G i x - G i y)).trans (hG x hx y hy)
  have hnonneg : 0 ≤ L * ‖x - y‖ := mul_nonneg hL (norm_nonneg _)
  nlinarith [norm_nonneg ((n : ℝ)⁻¹ • ∑ i, (G i x - G i y))]

end NCConcave16991

namespace NCConcave16991

/-- The two quadratic gradients from the separation example after Definition 2.1. -/
def quadraticGradient (L M : ℝ) (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then M * x else (2 * L - M) * x

/-- The corresponding actual component objectives. -/
def quadraticComponent (L M : ℝ) (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then M * x ^ 2 / 2 else (2 * L - M) * x ^ 2 / 2

/-- The example maps really are derivatives of the quadratic component objectives. -/
theorem quadraticComponent_hasDerivAt (L M : ℝ) (i : Fin 2) (x : ℝ) :
    HasDerivAt (quadraticComponent L M i) (quadraticGradient L M i x) x := by
  have hquad (c : ℝ) : HasDerivAt (fun u : ℝ => c * u ^ 2 / 2) (c * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul c).div_const 2 using 1 <;>
      simp [id_eq, Pi.pow_apply] <;> ring
  by_cases hi : i = 0
  · convert hquad M using 1
    · ext u
      simp [quadraticComponent, hi]
    · simp [quadraticGradient, hi]
  · convert hquad (2 * L - M) using 1
    · ext u
      simp [quadraticComponent, hi]
    · simp [quadraticGradient, hi]
/-- Cancellation makes the average gradient independent of the large parameter M. -/
theorem averageMap_quadraticGradient (L M x : ℝ) :
    averageMap (quadraticGradient L M) x = L * x := by
  simp [averageMap, quadraticGradient, Fin.sum_univ_two]
  ring

/-- The average of the two components remains L-smooth for every M. -/
theorem quadratic_average_lipschitz {L : ℝ} (hL : 0 ≤ L) (M x y : ℝ) :
    ‖averageMap (quadraticGradient L M) x -
      averageMap (quadraticGradient L M) y‖ ≤ L * ‖x - y‖ := by
  rw [averageMap_quadraticGradient, averageMap_quadraticGradient, ← mul_sub, norm_mul]
  simp [Real.norm_eq_abs, abs_of_nonneg hL]

/-- The exact mean squared gradient difference at 1 and 0. -/
theorem quadratic_mean_square (L M : ℝ) :
    (2 : ℝ)⁻¹ * ∑ i : Fin 2,
      ‖quadraticGradient L M i 1 - quadraticGradient L M i 0‖ ^ 2 =
        L ^ 2 + (M - L) ^ 2 := by
  simp [quadraticGradient, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  ring

/-- Smoothness of the average does not imply AS: every M ≠ L violates AS(L). -/
theorem quadratic_not_averagedSmooth (L M : ℝ) (hML : M ≠ L) :
    ¬ AveragedSmooth (quadraticGradient L M) Set.univ L := by
  intro h
  have h10 := h 1 (Set.mem_univ _) 0 (Set.mem_univ _)
  change (2 : ℝ)⁻¹ * ∑ i : Fin 2,
      ‖quadraticGradient L M i 1 - quadraticGradient L M i 0‖ ^ 2 ≤
      L ^ 2 * ‖(1 : ℝ) - 0‖ ^ 2 at h10
  rw [quadratic_mean_square] at h10
  norm_num at h10
  exact hML (sub_eq_zero.mp h10)

end NCConcave16991

namespace NCConcave16991

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cauchy-Schwarz also bounds the arithmetic average of component norms. -/
theorem mean_norm_le_of_mean_square_le {n : ℕ} (hn : 0 < n)
    (v : Fin n → F) {c : ℝ} (hc : 0 ≤ c)
    (hv : (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 ≤ c ^ 2) :
    (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ≤ c := by
  have hj := norm_average_sq_le hn (fun i => ‖v i‖)
  simp only [norm_norm, Real.norm_eq_abs, smul_eq_mul, sq_abs] at hj
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean : 0 ≤ (n : ℝ)⁻¹ * ∑ i, ‖v i‖ :=
    mul_nonneg (inv_nonneg.mpr hnpos.le) (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  nlinarith

/-- Finite-dimensional Minkowski estimate for adding the same vector to every component. -/
theorem mean_square_add_common_le {n : ℕ} (hn : 0 < n)
    (v : Fin n → F) (w : F) {c : ℝ} (hc : 0 ≤ c)
    (hv : (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 ≤ c ^ 2) :
    (n : ℝ)⁻¹ * ∑ i, ‖v i + w‖ ^ 2 ≤ (c + ‖w‖) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean := mean_norm_le_of_mean_square_le hn v hc hv
  have hsum : ∑ i, ‖v i + w‖ ^ 2 ≤
      ∑ i, (‖v i‖ ^ 2 + 2 * ‖w‖ * ‖v i‖ + ‖w‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (v i) w) 2
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnpos.le)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hnorm := mul_le_mul_of_nonneg_left hmean (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (norm_nonneg w))
  have hs' : (n : ℝ)⁻¹ * ∑ i, ‖v i + w‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 +
        2 * ‖w‖ * ((n : ℝ)⁻¹ * ∑ i, ‖v i‖) + ‖w‖ ^ 2 := by
    convert hs using 1
    field_simp [hnpos.ne']
    <;> ring
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lemma A.1(iii): common Lipschitz regularization changes AS(L) to AS(L+r).
The common offset cancels without requiring a bound on its magnitude. -/
theorem AveragedSmooth.regularize {n : ℕ} (hn : 0 < n)
    {G : Fin n → E → F} {s : Set E} {L r : ℝ} {R : E → F} (b₀ : F)
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hG : AveragedSmooth G s L)
    (hR : ∀ x ∈ s, ∀ y ∈ s, ‖R x - R y‖ ≤ r * ‖x - y‖) :
    AveragedSmooth (fun i x => G i x + R x + b₀) s (L + r) := by
  intro x hx y hy
  have hbase : (n : ℝ)⁻¹ * ∑ i, ‖G i x - G i y‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2 := by
    simpa [mul_pow] using hG x hx y hy
  have hm := mean_square_add_common_le hn (fun i => G i x - G i y)
    (R x - R y) (mul_nonneg hL (norm_nonneg _)) hbase
  have hd : 0 ≤ L * ‖x - y‖ + ‖R x - R y‖ :=
    add_nonneg (mul_nonneg hL (norm_nonneg _)) (norm_nonneg _)
  have hreg : L * ‖x - y‖ + ‖R x - R y‖ ≤ (L + r) * ‖x - y‖ := by
    nlinarith [hR x hx y hy]
  have hsq := pow_le_pow_left₀ hd hreg 2
  have heq : ∀ i : Fin n, G i x + R x + b₀ - (G i y + R y + b₀) =
      (G i x - G i y) + (R x - R y) := by intro i; abel
  simp only [heq]
  calc
    _ ≤ (L * ‖x - y‖ + ‖R x - R y‖) ^ 2 := hm
    _ ≤ ((L + r) * ‖x - y‖) ^ 2 := hsq
    _ = _ := by ring

end NCConcave16991





namespace NCConcave16991

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact centering identity for a uniform finite sample: the deterministic kernel
of the conditional variance identity in Lemma A.1(ii). -/
theorem finite_variance_identity {n : ℕ} (hn : 0 < n) (v : Fin n → H) :
    (n : ℝ)⁻¹ * ∑ i, ‖v i - (n : ℝ)⁻¹ • ∑ j, v j‖ ^ 2 =
      (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 - ‖(n : ℝ)⁻¹ • ∑ j, v j‖ ^ 2 := by
  let m : H := (n : ℝ)⁻¹ • ∑ j, v j
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ i, v i = (n : ℝ) • m := by
    dsimp [m]
    rw [smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul]
  have hinner : ∑ i, ⟪v i, m⟫_ℝ = (n : ℝ) * ‖m‖ ^ 2 := by
    rw [← sum_inner, hsum, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hexpand : ∑ i, ‖v i - m‖ ^ 2 =
      ∑ i, ‖v i‖ ^ 2 - 2 * ((n : ℝ) * ‖m‖ ^ 2) + (n : ℝ) * ‖m‖ ^ 2 := by
    simp_rw [norm_sub_sq_real]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hinner]
  change (n : ℝ)⁻¹ * ∑ i, ‖v i - m‖ ^ 2 =
    (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 - ‖m‖ ^ 2
  rw [hexpand]
  field_simp [hnpos.ne']
  <;> ring

/-- Centering cannot increase the mean square of a finite uniform family. -/
theorem finite_centered_mean_square_le {n : ℕ} (hn : 0 < n) (v : Fin n → H) :
    (n : ℝ)⁻¹ * ∑ i, ‖v i - (n : ℝ)⁻¹ • ∑ j, v j‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 := by
  rw [finite_variance_identity hn v]
  exact sub_le_self _ (sq_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The one-sample variance consequence of AS, without probabilistic abbreviations. -/
theorem AveragedSmooth.centered_difference_bound {n : ℕ} (hn : 0 < n)
    {G : Fin n → E → H} {s : Set E} {L : ℝ} (hG : AveragedSmooth G s L)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (n : ℝ)⁻¹ * ∑ i,
      ‖(G i x - G i y) - (averageMap G x - averageMap G y)‖ ^ 2 ≤
        L ^ 2 * ‖x - y‖ ^ 2 := by
  have hdiff : averageMap G x - averageMap G y =
      (n : ℝ)⁻¹ • ∑ i, (G i x - G i y) := by
    simp [averageMap, Finset.sum_sub_distrib, smul_sub]
  rw [hdiff]
  exact (finite_centered_mean_square_le hn (fun i => G i x - G i y)).trans (hG x hx y hy)

end NCConcave16991


namespace NCConcave16991

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- AS permits component Lipschitz constants up to sqrt(n) L, as stated after
Definition 2.1. The proof uses each nonnegative summand of the actual finite sum. -/
theorem AveragedSmooth.component_lipschitz {n : ℕ} (hn : 0 < n)
    {G : Fin n → E → F} {s : Set E} {L : ℝ}
    (hL : 0 ≤ L) (hG : AveragedSmooth G s L) :
    ∀ i, ∀ x ∈ s, ∀ y ∈ s,
      ‖G i x - G i y‖ ≤ Real.sqrt n * L * ‖x - y‖ := by
  intro i x hx y hy
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left (hG x hx y hy) hnpos.le
  have hsum : ∑ j, ‖G j x - G j y‖ ^ 2 ≤ (n : ℝ) * (L ^ 2 * ‖x - y‖ ^ 2) := by
    simpa [← mul_assoc, mul_inv_cancel₀ hnpos.ne'] using hm
  have hi : ‖G i x - G i y‖ ^ 2 ≤ ∑ j, ‖G j x - G j y‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖G j x - G j y‖) (Finset.mem_univ i)
  have hsquare : (Real.sqrt n * L * ‖x - y‖) ^ 2 =
      (n : ℝ) * (L ^ 2 * ‖x - y‖ ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le]
    ring
  have hbound : 0 ≤ Real.sqrt n * L * ‖x - y‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) (norm_nonneg _)
  nlinarith [hi.trans hsum, norm_nonneg (G i x - G i y)]

/-- AS is invariant under a common linear isometry. In particular the dual sign
change in the paper preserves the mean-squared smoothness constant exactly. -/
theorem AveragedSmooth.linearIsometry {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {n : ℕ} {G : Fin n → E → F} {s : Set E} {L : ℝ}
    (hG : AveragedSmooth G s L) (U : F →ₗᵢ[ℝ] H) :
    AveragedSmooth (fun i x => U (G i x)) s L := by
  intro x hx y hy
  simpa only [← U.map_sub, U.norm_map] using hG x hx y hy

end NCConcave16991




namespace NCConcave16991

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The finite uniform mean of the centered family is exactly zero. -/
theorem finite_centered_sum_eq_zero {n : ℕ} (hn : 0 < n) (v : Fin n → H) :
    ∑ i, (v i - (n : ℝ)⁻¹ • ∑ j, v j) = 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul, sub_self]

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- A dominated quadratic weight gives the weighted variance consequence of AS.
Taking U to be the square root of a positive semidefinite weight recovers its norm. -/
theorem AveragedSmooth.weighted_centered_difference_bound {n : ℕ} (hn : 0 < n)
    {G : Fin n → E → H} {s : Set E} {L κ : ℝ}
    (hG : AveragedSmooth G s L) (hκ : 0 ≤ κ)
    (U : H →ₗ[ℝ] K) (hU : ∀ v, ‖U v‖ ^ 2 ≤ κ * ‖v‖ ^ 2)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (n : ℝ)⁻¹ * ∑ i,
      ‖U ((G i x - G i y) - (averageMap G x - averageMap G y))‖ ^ 2 ≤
        κ * L ^ 2 * ‖x - y‖ ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin n) _ => hU ((G i x - G i y) - (averageMap G x - averageMap G y)))
  have hw := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnpos.le)
  have hc := mul_le_mul_of_nonneg_left (hG.centered_difference_bound hn hx hy) hκ
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i,
      κ * ‖(G i x - G i y) - (averageMap G x - averageMap G y)‖ ^ 2 := hw
    _ = κ * ((n : ℝ)⁻¹ * ∑ i,
      ‖(G i x - G i y) - (averageMap G x - averageMap G y)‖ ^ 2) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ κ * (L ^ 2 * ‖x - y‖ ^ 2) := hc
    _ = _ := by ring

end NCConcave16991
