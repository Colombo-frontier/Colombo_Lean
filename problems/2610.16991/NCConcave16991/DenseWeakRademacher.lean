import NCConcave16991.DenseWeakEventTransfer
import NCConcave16991.DenseWeakBiasColumn
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Finite Rademacher law and the actual alignment Chernoff bound -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

def rademacherLaw (D : ℕ) : FiniteLaw (Fin D → Fin 2) where
  mass := fun _ ↦ ∏ _j : Fin D, (1 / 2 : ℝ)
  nonneg := fun _ ↦ Finset.prod_nonneg (fun _ _ ↦ by norm_num)
  sum_one := by
    change (∑ θ : Fin D → Fin 2, ∏ j, (fun _b : Fin 2 ↦ (1 / 2 : ℝ)) (θ j)) = 1
    rw [← Fintype.prod_sum (fun (_j : Fin D) (_b : Fin 2) ↦ (1 / 2 : ℝ))]
    simp only [Fin.sum_univ_two]
    norm_num

def signedSum {D : ℕ} (v : Fin D → ℝ) (θ : Fin D → Fin 2) : ℝ :=
  ∑ j, hiddenSign (θ j) * v j

theorem binary_exp_average (z : ℝ) :
    (∑ b : Fin 2, (1 / 2 : ℝ) * Real.exp (hiddenSign b * z)) = Real.cosh z := by
  simp only [Fin.sum_univ_two, hiddenSign]
  norm_num [Real.cosh_eq]
  ring

theorem rademacher_exponentialMoment {D : ℕ} (v : Fin D → ℝ) (t : ℝ) :
    (rademacherLaw D).exponentialMoment (fun θ ↦ t * signedSum v θ) =
      ∏ j, Real.cosh (t * v j) := by
  have he (θ : Fin D → Fin 2) :
      (rademacherLaw D).mass θ * Real.exp (t * signedSum v θ) =
        ∏ j, (1 / 2 : ℝ) * Real.exp (hiddenSign (θ j) * (t * v j)) := by
    unfold signedSum rademacherLaw
    rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
    congr 1
    funext j
    congr 2
    ring
  unfold FiniteLaw.exponentialMoment
  rw [Finset.sum_congr rfl (fun θ _ ↦ he θ),
    ← Fintype.prod_sum (fun (j : Fin D) (b : Fin 2) ↦
      (1 / 2 : ℝ) * Real.exp (hiddenSign b * (t * v j)))]
  simp_rw [binary_exp_average]

theorem rademacher_exponentialMoment_le {D : ℕ} (v : Fin D → ℝ) (t : ℝ) :
    (rademacherLaw D).exponentialMoment (fun θ ↦ t * signedSum v θ) ≤
      Real.exp (t ^ 2 * (∑ j, v j ^ 2) / 2) := by
  rw [rademacher_exponentialMoment]
  calc
    _ ≤ ∏ j, Real.exp ((t * v j) ^ 2 / 2) :=
      Finset.prod_le_prod₀ (fun j _ ↦ (Real.cosh_pos _).le)
        (fun j _ ↦ Real.cosh_le_exp_half_sq _)
    _ = Real.exp (t ^ 2 * (∑ j, v j ^ 2) / 2) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [mul_pow, ← Finset.sum_div, ← Finset.mul_sum]

theorem finite_chernoff {I : Type*} [Fintype I] (P : FiniteLaw I) (X : I → ℝ)
    (a t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t * a) * P.eventMass {i | a ≤ X i} ≤
      P.exponentialMoment (fun i ↦ t * X i) := by
  classical
  rw [FiniteLaw.eventMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : a ≤ X i
  · simp only [Set.mem_setOf_eq, hi, ite_true]
    have hh := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi ht)
    nlinarith [P.nonneg i]
  · simp only [Set.mem_setOf_eq, hi, ite_false, mul_zero]
    exact mul_nonneg (P.nonneg i) (Real.exp_pos _).le

theorem rademacher_tail {D : ℕ} (v : Fin D → ℝ) (hv : (∑ j, v j ^ 2) ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) :
    (rademacherLaw D).eventMass {θ | a ≤ signedSum v θ} ≤ Real.exp (-a ^ 2 / 2) := by
  have hc := finite_chernoff (rademacherLaw D) (signedSum v) a a ha
  have hm := rademacher_exponentialMoment_le v a
  have he : Real.exp (a ^ 2 * (∑ j, v j ^ 2) / 2) ≤ Real.exp (a ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg a]
  have hbound := hc.trans (hm.trans he)
  have hratio : Real.exp (a ^ 2 / 2) / Real.exp (a * a) = Real.exp (-a ^ 2 / 2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [← hratio]
  exact (le_div_iff₀ (Real.exp_pos (a * a))).mpr (by simpa only [mul_comm] using hbound)

end NCConcave16991.DenseWeakHiding
