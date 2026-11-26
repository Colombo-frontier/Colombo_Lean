import NoisyZO.AdaptiveKLSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Finite Assouad testing arithmetic

This module proves the finite hypercube pairing step independently of any
particular probability-space encoding.  `err s i` is the probability of a
wrong decision on coordinate `i` under vertex `s`, and `tv s i` is the total
variation distance across the corresponding directed edge.
-/

open scoped BigOperators

namespace NoisyZO

def flipHypercube {d : ℕ} (s : Hypercube d) (i : Fin d) : Hypercube d :=
  fun j => if j = i then !(s j) else s j

@[simp] theorem flipHypercube_same {d : ℕ} (s : Hypercube d) (i : Fin d) :
    flipHypercube s i i = !(s i) := by simp [flipHypercube]

theorem flipHypercube_involutive {d : ℕ} (i : Fin d) :
    Function.Involutive (fun s : Hypercube d => flipHypercube s i) := by
  intro s
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipHypercube]
  · simp [flipHypercube, hji]

def flipHypercubeEquiv {d : ℕ} (i : Fin d) : Hypercube d ≃ Hypercube d where
  toFun := fun s => flipHypercube s i
  invFun := fun s => flipHypercube s i
  left_inv := flipHypercube_involutive i
  right_inv := flipHypercube_involutive i

theorem sum_flipHypercube {d : ℕ} (i : Fin d) (f : Hypercube d → ℝ) :
    ∑ s : Hypercube d, f (flipHypercube s i) = ∑ s : Hypercube d, f s := by
  exact (flipHypercubeEquiv i).sum_comp f

/-- Pairing all directed hypercube edges. -/
theorem assouad_edge_pairing {d : ℕ}
    (err tv : Hypercube d → Fin d → ℝ) (τ : ℝ)
    (hedge : ∀ s i,
      1 - tv s i ≤ err s i + err (flipHypercube s i) i)
    (hTV : (∑ s : Hypercube d, ∑ i : Fin d, tv s i) ≤
      ((2 : ℝ) ^ d * d) * τ) :
    (((2 : ℝ) ^ d * d) / 2) * (1 - τ) ≤
      ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
  have hsum := Finset.sum_le_sum fun s (_hs : s ∈ Finset.univ) =>
    Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hedge s i
  have hflip :
      (∑ s : Hypercube d, ∑ i : Fin d, err (flipHypercube s i) i) =
        ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
    rw [Finset.sum_comm]
    calc
      ∑ i : Fin d, ∑ s : Hypercube d, err (flipHypercube s i) i =
          ∑ i : Fin d, ∑ s : Hypercube d, err s i := by
            apply Finset.sum_congr rfl
            intro i _
            exact sum_flipHypercube i (fun s => err s i)
      _ = ∑ s : Hypercube d, ∑ i : Fin d, err s i := Finset.sum_comm
  have hleft :
      (∑ s : Hypercube d, ∑ i : Fin d, (1 - tv s i)) =
        (2 : ℝ) ^ d * d - ∑ s : Hypercube d, ∑ i : Fin d, tv s i := by
    simp [Finset.sum_sub_distrib]
  have hright :
      (∑ s : Hypercube d,
        ∑ i : Fin d, (err s i + err (flipHypercube s i) i)) =
        2 * ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
    simp_rw [Finset.sum_add_distrib]
    rw [hflip]
    ring
  rw [hleft, hright] at hsum
  nlinarith

/-- Finite Pinsker averaging via Cauchy--Schwarz.  This is the Jensen step
used after applying Pinsker on every edge. -/
theorem pinsker_average_sum_bound {d : ℕ}
    (tv KL : Hypercube d → Fin d → ℝ)
    (hKL : ∀ s i, 0 ≤ KL s i)
    (hpinsker : ∀ s i, tv s i ≤ Real.sqrt (KL s i / 2)) :
    (∑ s : Hypercube d, ∑ i : Fin d, tv s i) ≤
      Real.sqrt (((2 : ℝ) ^ d * d) *
        (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2) := by
  let edgeSum : ℝ :=
    ∑ e : Hypercube d × Fin d, Real.sqrt (KL e.1 e.2 / 2)
  have htv : (∑ s : Hypercube d, ∑ i : Fin d, tv s i) ≤ edgeSum := by
    dsimp [edgeSum]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun s _ =>
      Finset.sum_le_sum fun i _ => hpinsker s i
  have hedge_nonneg : 0 ≤ edgeSum := by
    dsimp [edgeSum]
    positivity
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Hypercube d × Fin d)))
    (f := fun e => Real.sqrt (KL e.1 e.2 / 2))
  have hsquares :
      (∑ e : Hypercube d × Fin d, (Real.sqrt (KL e.1 e.2 / 2)) ^ 2) =
        (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Real.sq_sqrt (div_nonneg (hKL _ _) (by norm_num : (0 : ℝ) ≤ 2))]
    simp_rw [Finset.sum_div]
  have hcard :
      ((Fintype.card (Hypercube d × Fin d) : ℝ)) = (2 : ℝ) ^ d * d := by
    simp [Fintype.card_prod]
  have hedge_sq :
      edgeSum ^ 2 ≤ ((2 : ℝ) ^ d * d) *
        (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2 := by
    dsimp [edgeSum]
    simp only [Finset.card_univ] at hcauchy
    rw [hcard] at hcauchy
    rw [hsquares] at hcauchy
    nlinarith
  have hsumKL :
      0 ≤ (∑ s : Hypercube d, ∑ i : Fin d, KL s i) := by
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => hKL s i
  have htotal_nonneg :
      0 ≤ ((2 : ℝ) ^ d * d) *
        (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2 := by
    positivity
  have hsqrt_sq := Real.sq_sqrt htotal_nonneg
  have hsqrt_nonneg := Real.sqrt_nonneg
    (((2 : ℝ) ^ d * d) * (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2)
  have hedge_le : edgeSum ≤
      Real.sqrt (((2 : ℝ) ^ d * d) *
        (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2) := by
    nlinarith
  exact htv.trans hedge_le

/-- The manuscript's Assouad--Pinsker inequality in unnormalized finite-sum
form.  Dividing by `2^d` gives
`average Hamming error ≥ d/2 * (1 - sqrt(Kbar/2))`. -/
theorem assouad_pinsker_bound {d : ℕ}
    (err tv KL : Hypercube d → Fin d → ℝ) (Kbar : ℝ)
    (hKbar : 0 ≤ Kbar)
    (hKL : ∀ s i, 0 ≤ KL s i)
    (hedge : ∀ s i,
      1 - tv s i ≤ err s i + err (flipHypercube s i) i)
    (hpinsker : ∀ s i, tv s i ≤ Real.sqrt (KL s i / 2))
    (haverageKL : (∑ s : Hypercube d, ∑ i : Fin d, KL s i) ≤
      ((2 : ℝ) ^ d * d) * Kbar) :
    ((((2 : ℝ) ^ d * d) / 2) *
        (1 - Real.sqrt (Kbar / 2))) ≤
      ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
  let N : ℝ := (2 : ℝ) ^ d * d
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hsumKL :
      0 ≤ (∑ s : Hypercube d, ∑ i : Fin d, KL s i) := by
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => hKL s i
  have htv := pinsker_average_sum_bound tv KL hKL hpinsker
  have hinside :
      N * (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2 ≤
        (N * Real.sqrt (Kbar / 2)) ^ 2 := by
    have hsqrt := Real.sq_sqrt (div_nonneg hKbar (by norm_num : (0 : ℝ) ≤ 2))
    calc
      N * (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2 ≤
          N * (N * Kbar) / 2 := by
            dsimp [N]
            gcongr
      _ = (N * Real.sqrt (Kbar / 2)) ^ 2 := by
            calc
              N * (N * Kbar) / 2 = N ^ 2 * (Kbar / 2) := by ring
              _ = N ^ 2 * (Real.sqrt (Kbar / 2)) ^ 2 := by rw [hsqrt]
              _ = (N * Real.sqrt (Kbar / 2)) ^ 2 := by ring
  have hleft_nonneg :
      0 ≤ Real.sqrt (N *
        (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2) := Real.sqrt_nonneg _
  have hright_nonneg : 0 ≤ N * Real.sqrt (Kbar / 2) :=
    mul_nonneg hN (Real.sqrt_nonneg _)
  have htvN :
      (∑ s : Hypercube d, ∑ i : Fin d, tv s i) ≤
        N * Real.sqrt (Kbar / 2) := by
    have hinner_nonneg :
        0 ≤ N * (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2 := by
      positivity
    have hsqrt_sq := Real.sq_sqrt hinner_nonneg
    have hsqrt_le :
        Real.sqrt (N *
          (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2) ≤
          N * Real.sqrt (Kbar / 2) := by
      nlinarith
    have htv' :
        (∑ s : Hypercube d, ∑ i : Fin d, tv s i) ≤
          Real.sqrt (N *
            (∑ s : Hypercube d, ∑ i : Fin d, KL s i) / 2) := by
      simpa [N] using htv
    exact htv'.trans hsqrt_le
  have hpair := assouad_edge_pairing err tv (Real.sqrt (Kbar / 2)) hedge
    (by simpa [N] using htvN)
  simpa [N] using hpair

end NoisyZO
