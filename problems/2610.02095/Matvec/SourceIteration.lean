import Matvec.AdaptiveIteration
import Matvec.Refinement


/-!
# Measurable verified corrections and adaptive iterative refinement

The base solver is jointly measurable in its right-hand side and random seed.
Every correction uses a fresh independent block of seeds. Uniform base success
on each fixed right-hand side therefore controls the actual adaptive residuals.
-/

namespace Matvec

open MeasureTheory

noncomputable section

theorem measurable_bestCandidate_param {P E : Type*}
    [MeasurableSpace P] [MeasurableSpace E]
    (score : P → E → ℝ)
    (hscore : Measurable (fun p : P × E => score p.1 p.2)) (R : ℕ) :
    Measurable (fun p : P × (Fin (R + 1) → E) => bestCandidate (score p.1) R p.2) := by
  induction R with
  | zero => exact (measurable_pi_apply 0).comp measurable_snd
  | succ R ih =>
      have hhead : Measurable (fun p : P × (Fin (R + 2) → E) => p.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable (fun p : P × (Fin (R + 2) → E) =>
          bestCandidate (score p.1) R (fun i => p.2 i.succ)) :=
        ih.comp (measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
          (measurable_pi_apply i.succ).comp measurable_snd))
      exact hhead.piecewise
        (measurableSet_le (hscore.comp (measurable_fst.prodMk hhead))
          (hscore.comp (measurable_fst.prodMk htail))) htail

variable {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Seed]

def verifiedSource (H : E →L[ℝ] E) (base : E → Seed → E) (R : ℕ)
    (r : E) (seeds : Fin (R + 1) → Seed) : E :=
  verifiedRepeat (fun x => ‖H x - r‖) (base r) R seeds

theorem measurable_verifiedSource (H : E →L[ℝ] E) (base : E → Seed → E)
    (hbase : Measurable (fun p : E × Seed => base p.1 p.2)) (R : ℕ) :
    Measurable (fun p : E × (Fin (R + 1) → Seed) => verifiedSource H base R p.1 p.2) := by
  have hs : Measurable (fun p : E × E => ‖H p.2 - p.1‖) :=
    ((H.continuous.measurable.comp measurable_snd).sub measurable_fst).norm
  exact (measurable_bestCandidate_param (fun r x : E => ‖H x - r‖) hs R).comp
    (measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
      hbase.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))))

theorem verifiedSource_failure (μ : Measure Seed) [IsProbabilityMeasure μ]
    (H : E →L[ℝ] E) (base : E → Seed → E)
    (hbase : Measurable (fun p : E × Seed => base p.1 p.2))
    (hsuccess : ∀ r, 3 / 5 ≤ μ.real {seed | ‖H (base r seed) - r‖ ≤ ‖r‖ / 2})
    (R : ℕ) (r : E) :
    (Measure.pi (fun _ : Fin (R + 1) => μ)).real
      {seeds | ‖r‖ / 2 < ‖H (verifiedSource H base R r seeds) - r‖} ≤
      (2 / 5 : ℝ) ^ (R + 1) := by
  exact (verified_residual_solver μ H r (base r)
    (hbase.comp (measurable_const.prodMk measurable_id)) R (hsuccess r)).2

def refinementStep (H : E →L[ℝ] E) (solve : E → Seed → E)
    (_ : ℕ) (state : E × E) (seed : Seed) : E × E :=
  let c := solve state.2 seed
  (state.1 + c, state.2 - H c)

def refinementGood (H : E →L[ℝ] E) (solve : E → Seed → E)
    (_ : ℕ) (state : E × E) (seed : Seed) : Prop :=
  ‖H (solve state.2 seed) - state.2‖ ≤ ‖state.2‖ / 2

def refinedSource (H : E →L[ℝ] E) (solve : E → Seed → E)
    (J : ℕ) (b : E) (seeds : SeedBlock Seed J) : E :=
  (adaptiveRun (refinementStep H solve) (0, b) J seeds).1

theorem measurable_refinementStep (H : E →L[ℝ] E) (solve : E → Seed → E)
    (hsolve : Measurable (fun p : E × Seed => solve p.1 p.2)) (n : ℕ) :
    Measurable (fun p : (E × E) × Seed => refinementStep H solve n p.1 p.2) := by
  have hc : Measurable (fun p : (E × E) × Seed => solve p.1.2 p.2) :=
    hsolve.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact ((measurable_fst.comp measurable_fst).add hc).prodMk
    ((measurable_snd.comp measurable_fst).sub (H.continuous.measurable.comp hc))

theorem measurableSet_refinementGood (H : E →L[ℝ] E) (solve : E → Seed → E)
    (hsolve : Measurable (fun p : E × Seed => solve p.1 p.2)) (n : ℕ) :
    MeasurableSet {p : (E × E) × Seed | refinementGood H solve n p.1 p.2} := by
  have hc : Measurable (fun p : (E × E) × Seed => solve p.1.2 p.2) :=
    hsolve.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact measurableSet_le
    ((H.continuous.measurable.comp hc).sub (measurable_snd.comp measurable_fst)).norm
    ((measurable_snd.comp measurable_fst).norm.div_const 2)

theorem measurable_refinedSource (H : E →L[ℝ] E) (solve : E → Seed → E)
    (hsolve : Measurable (fun p : E × Seed => solve p.1 p.2)) (J : ℕ) :
    Measurable (fun p : E × SeedBlock Seed J => refinedSource H solve J p.1 p.2) :=
  measurable_fst.comp
    ((measurable_adaptiveRun_initial _ (measurable_refinementStep H solve hsolve) J).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))

/-- Actual refinement updates give geometric residual decay on their own
successful-call event. -/
theorem refinedSource_residual (H : E →L[ℝ] E) (solve : E → Seed → E)
    (J : ℕ) (b : E) (seeds : SeedBlock Seed J)
    (hgood : ¬adaptiveFailure (refinementStep H solve) (refinementGood H solve) (0, b) J seeds) :
    ‖H (refinedSource H solve J b seeds) - b‖ ≤ (1 / 2 : ℝ) ^ J * ‖b‖ := by
  have hinv := adaptiveRun_invariant (refinementStep H solve) (refinementGood H solve) (0, b)
    (fun n state => state.2 = b - H state.1 ∧ ‖state.2‖ ≤ (1 / 2 : ℝ) ^ n * ‖b‖)
    (by simp) (fun n state seed hx hg => ?_) J seeds hgood
  · rw [refinedSource, norm_sub_rev, ← hinv.1]
    exact hinv.2
  · dsimp only [refinementStep]
    constructor
    · rw [map_add, hx.1]; abel
    · rw [norm_sub_rev]
      have h : ‖H (solve state.2 seed) - state.2‖ ≤ ‖state.2‖ / 2 := hg
      calc
        _ ≤ ‖state.2‖ / 2 := h
        _ ≤ ((1 / 2 : ℝ) ^ n * ‖b‖) / 2 := div_le_div_of_nonneg_right hx.2 (by norm_num)
        _ = _ := by ring

theorem refinedSource_error (H M : E →L[ℝ] E) (solve : E → Seed → E)
    (hinverse : ∀ x, M (H x) = x) (J : ℕ) (η : ℝ)
    (hJ : (1 / 2 : ℝ) ^ J ≤ η) (b : E) (seeds : SeedBlock Seed J)
    (hgood : ¬adaptiveFailure (refinementStep H solve) (refinementGood H solve) (0, b) J seeds) :
    ‖refinedSource H solve J b seeds - M b‖ ≤ η * ‖M‖ * ‖b‖ := by
  have hres := refinedSource_residual H solve J b seeds hgood
  have hid : refinedSource H solve J b seeds - M b =
      M (H (refinedSource H solve J b seeds) - b) := by rw [map_sub, hinverse]
  rw [hid]
  calc
    _ ≤ ‖M‖ * ‖H (refinedSource H solve J b seeds) - b‖ := M.le_opNorm _
    _ ≤ ‖M‖ * ((1 / 2 : ℝ) ^ J * ‖b‖) :=
      mul_le_mul_of_nonneg_left hres (norm_nonneg _)
    _ ≤ ‖M‖ * (η * ‖b‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- The right-hand sides of the correction calls are the actual random
residuals. Their failure probabilities follow from fresh product seeds. -/
theorem refinedSource_failure (μ : Measure Seed) [IsProbabilityMeasure μ]
    (H M : E →L[ℝ] E) (solve : E → Seed → E)
    (hsolve : Measurable (fun p : E × Seed => solve p.1 p.2))
    (hinverse : ∀ x, M (H x) = x) (δ : ℝ) (hδ : 0 ≤ δ)
    (hfailure : ∀ r, μ.real {seed | ‖r‖ / 2 < ‖H (solve r seed) - r‖} ≤ δ)
    (J : ℕ) (η : ℝ) (hJ : (1 / 2 : ℝ) ^ J ≤ η) (b : E) :
    (seedBlockLaw μ J).real
      {seeds | η * ‖M‖ * ‖b‖ < ‖refinedSource H solve J b seeds - M b‖} ≤
      (J : ℝ) * δ := by
  apply le_trans (measureReal_mono ?_)
    (adaptive_failure_probability μ (refinementStep H solve) (refinementGood H solve) (0, b)
      (measurable_refinementStep H solve hsolve) (measurableSet_refinementGood H solve hsolve)
      δ hδ (fun _ state => ?_) J)
  · intro seeds hs
    by_contra hn
    exact (not_lt_of_ge (refinedSource_error H M solve hinverse J η hJ b seeds hn)) hs
  · simpa only [refinementGood, not_le] using hfailure state.2

end
end Matvec

