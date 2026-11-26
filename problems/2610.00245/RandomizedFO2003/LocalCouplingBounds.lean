import RandomizedFO2003.ScaledDerivativeBounds
import Mathlib.Analysis.NormedSpace.OperatorNorm.Prod

namespace RandomizedFO2003.Cascade

open Primitives Calculus
open scoped BigOperators

universe u

/-- The single adjacent-block interaction of the actual cascade. The
negative sign with which it enters the energy does not alter derivative norms. -/
noncomputable def localCoupling {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (B α D C₀ K : ℝ) (p : E × E) : ℝ :=
  radialGate a B α p.1 * forcing b D C₀ K p.2

noncomputable def couplingDerivativeConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * gateScaleConstant i * forceScaleConstant (n - i)

theorem couplingDerivativeConstant_pos (n : ℕ) : 0 < couplingDerivativeConstant n := by
  unfold couplingDerivativeConstant
  refine Finset.sum_pos' ?_ ?_
  · intro i _hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (gateScaleConstant_pos i).le)
      (forceScaleConstant_pos (n - i)).le
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simpa only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] using
      mul_pos (gateScaleConstant_pos 0) (forceScaleConstant_pos n)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem localCoupling_contDiff (a b : E) (B α D C₀ K : ℝ) (n : ℕ) :
    ContDiff ℝ n (localCoupling a b B α D C₀ K) :=
  ((radialGate_contDiff a B α n).comp contDiff_fst).mul
    ((forcing_contDiff b D C₀ K n).comp contDiff_snd)

/-- The full local product rule, with a numerical constant independent of
dimension, scales, or the number of blocks in which this edge appears. -/
theorem scaled_localCoupling_derivative_bound (n : ℕ) (a b : E) (ha : ‖a‖ ≤ 1)
    {h γ : ℝ} (hh : 0 < h) (hγ : 0 < γ) (hb : ‖b‖ ≤ h) (p : E × E) :
    ‖iteratedFDeriv ℝ n
      (localCoupling a b (radiusCoefficient * h / γ) (h / (64 * γ))
        (h ^ 2 / γ) forcingOffset saturationThreshold) p‖ ≤
      couplingDerivativeConstant n * (h ^ 2 / γ) * (γ / h) ^ n := by
  let g : E → ℝ := radialGate a (radiusCoefficient * h / γ) (h / (64 * γ))
  let f : E → ℝ := forcing b (h ^ 2 / γ) forcingOffset saturationThreshold
  have hg (i : ℕ) : ContDiff ℝ i g := radialGate_contDiff _ _ _ i
  have hf (i : ℕ) : ContDiff ℝ i f := forcing_contDiff _ _ _ _ i
  have hgb (i : ℕ) : ‖iteratedFDeriv ℝ i (fun q : E × E => g q.1) p‖ ≤
      gateScaleConstant i * (γ / h) ^ i :=
    (norm_iteratedFDeriv_comp_contraction_le (ContinuousLinearMap.fst ℝ E E)
      (ContinuousLinearMap.norm_fst_le ..) i (hg i) p).trans
      (scaled_gate_derivative_bound i a ha hh hγ p.1)
  have hfb (i : ℕ) : ‖iteratedFDeriv ℝ i (fun q : E × E => f q.2) p‖ ≤
      forceScaleConstant i * (h ^ 2 / γ) * (γ / h) ^ i :=
    (norm_iteratedFDeriv_comp_contraction_le (ContinuousLinearMap.snd ℝ E E)
      (ContinuousLinearMap.norm_snd_le ..) i (hf i) p).trans
      (scaled_forcing_derivative_bound i b hh hγ hb p.2)
  have hm := norm_iteratedFDeriv_mul_le ((hg n).comp contDiff_fst)
    ((hf n).comp contDiff_snd) p le_rfl
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q : E × E => g q.1) p‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun q : E × E => f q.2) p‖ := hm
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (gateScaleConstant i * (γ / h) ^ i) *
        (forceScaleConstant (n - i) * (h ^ 2 / γ) * (γ / h) ^ (n - i)) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hgb i) (Nat.cast_nonneg _)) (hfb (n - i))
        (norm_nonneg _) (by have hc := (gateScaleConstant_pos i).le; positivity)
    _ = couplingDerivativeConstant n * (h ^ 2 / γ) * (γ / h) ^ n := by
      unfold couplingDerivativeConstant
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hp : (γ / h) ^ i * (γ / h) ^ (n - i) = (γ / h) ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hin]
      calc
        _ = ((n.choose i : ℝ) * gateScaleConstant i * forceScaleConstant (n - i)) *
            (h ^ 2 / γ) * ((γ / h) ^ i * (γ / h) ^ (n - i)) := by ring
        _ = _ := by rw [hp]

/-- The Hessian scale in the source's local coupling lemma. -/
theorem localCoupling_second_derivative_bound (a b : E) (ha : ‖a‖ ≤ 1)
    {h γ : ℝ} (hh : 0 < h) (hγ : 0 < γ) (hb : ‖b‖ ≤ h) (p : E × E) :
    ‖iteratedFDeriv ℝ 2
      (localCoupling a b (radiusCoefficient * h / γ) (h / (64 * γ))
        (h ^ 2 / γ) forcingOffset saturationThreshold) p‖ ≤ couplingDerivativeConstant 2 * γ := by
  apply (scaled_localCoupling_derivative_bound 2 a b ha hh hγ hb p).trans_eq
  field_simp
  ring

/-- The third-derivative scale in the source's local coupling lemma. -/
theorem localCoupling_third_derivative_bound (a b : E) (ha : ‖a‖ ≤ 1)
    {h γ : ℝ} (hh : 0 < h) (hγ : 0 < γ) (hb : ‖b‖ ≤ h) (p : E × E) :
    ‖iteratedFDeriv ℝ 3
      (localCoupling a b (radiusCoefficient * h / γ) (h / (64 * γ))
        (h ^ 2 / γ) forcingOffset saturationThreshold) p‖ ≤ couplingDerivativeConstant 3 * γ ^ 2 / h := by
  apply (scaled_localCoupling_derivative_bound 3 a b ha hh hγ hb p).trans_eq
  field_simp
  ring

/-- The source's one-coupling smoothness lemma at the explicitly fixed
cascade scales. One positive numerical constant works for both derivative
orders and is selected before the underlying real inner product space. -/
theorem coupling_smooth : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V],
      ∀ (a b : V) (h γ : ℝ), ‖a‖ ≤ 1 → ‖b‖ ≤ h → 0 < h → 0 < γ → ∀ p : V × V,
        let G := -localCoupling a b (radiusCoefficient * h / γ) (h / (64 * γ))
          (h ^ 2 / γ) forcingOffset saturationThreshold
        ‖iteratedFDeriv ℝ 2 G p‖ ≤ C * γ ∧
        ‖iteratedFDeriv ℝ 3 G p‖ ≤ C * γ ^ 2 / h := by
  refine ⟨couplingDerivativeConstant 2 + couplingDerivativeConstant 3,
    add_pos (couplingDerivativeConstant_pos 2) (couplingDerivativeConstant_pos 3), ?_⟩
  intro V _ _ a b h γ ha hb hh hγ p
  dsimp only
  rw [iteratedFDeriv_neg_apply, norm_neg, iteratedFDeriv_neg_apply, norm_neg]
  constructor
  · apply (localCoupling_second_derivative_bound a b ha hh hγ hb p).trans
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (couplingDerivativeConstant_pos 3).le) hγ.le
  · apply (localCoupling_third_derivative_bound a b ha hh hγ hb p).trans
    apply div_le_div_of_nonneg_right _ hh.le
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (couplingDerivativeConstant_pos 2).le) (sq_nonneg γ)

end RandomizedFO2003.Cascade
