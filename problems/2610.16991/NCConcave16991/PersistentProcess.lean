import NCConcave16991.WeightedEstimator
import NCConcave16991.FiniteProcess

/-!
# A chronological persistent-estimator process

Each step runs a finite independent inner seed, then updates the anchor
estimator with a fresh independent difference batch. Its variance bound is
proved for this recursive process, including exact refreshes and a partial
last epoch. The inner center map can be any function of the current state and
the new inner seed; in particular no independence of that center and the old
estimator error is assumed.
-/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.PersistentProcess

noncomputable section

structure State (dx dy : ℕ) where
  center : PrimalSpace dx
  estimate : JointSpace dx dy

variable {n b dx dy : ℕ} [NeZero n] [MeasurableSpace (Fin n)]
  [MeasurableSingletonClass (Fin n)]
  {J : Type*} [Finite J] [MeasurableSpace J] [MeasurableSingletonClass J]

def error (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (y0 : DualSpace dy) (z : State dx dy) : JointSpace dx dy :=
  z.estimate - averageMap G (jointPoint z.center y0)

def initial (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (y0 : DualSpace dy) (c : PrimalSpace dx) : State dx dy :=
  ⟨c, averageMap G (jointPoint c y0)⟩

def advance (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (y0 : DualSpace dy) (q : ℕ) (solve : State dx dy → J → PrimalSpace dx)
    (t : ℕ) (z : State dx dy) (ω : J × (Fin b → Fin n)) : State dx dy :=
  let c := solve z ω.1
  ⟨c, if (t + 1) % q = 0 then averageMap G (jointPoint c y0)
    else z.estimate + minibatchMean
      (fun i ↦ G i (jointPoint c y0) - G i (jointPoint z.center y0)) ω.2⟩

def process (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (y0 : DualSpace dy) (q : ℕ) (solve : State dx dy → J → PrimalSpace dx)
    (c : PrimalSpace dx) : (t : ℕ) →
      FiniteProcess.History (J × (Fin b → Fin n)) t → State dx dy :=
  FiniteProcess.trajectory (advance G y0 q solve) (initial G y0 c)

theorem advance_center (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (y0 : DualSpace dy) (q : ℕ) (solve : State dx dy → J → PrimalSpace dx)
    (t : ℕ) (z : State dx dy) (ω : J × (Fin b → Fin n)) :
    (advance G y0 q solve t z ω).center = solve z ω.1 := rfl

theorem process_refresh_error (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (y0 : DualSpace dy) (q : ℕ) (solve : State dx dy → J → PrimalSpace dx)
    (c : PrimalSpace dx) (t : ℕ) (ht : t % q = 0)
    (h : FiniteProcess.History (J × (Fin b → Fin n)) t) :
    error G y0 (process G y0 q solve c t h) = 0 := by
  cases t with
  | zero => simp [process, FiniteProcess.trajectory, initial, error]
  | succ t => simp [process, FiniteProcess.trajectory, advance, error, ht]

theorem anchor_distance (y0 : DualSpace dy) (x y : PrimalSpace dx) :
    ‖jointPoint x y0 - jointPoint y y0‖ = ‖x - y‖ := by
  change ‖WithLp.toLp 2 (x - y, y0 - y0)‖ = ‖x - y‖
  rw [sub_self, WithLp.norm_toLp_fst]

/-- The one-step weighted moment is derived from the actual fresh batch after
the new center has been computed, with the old bias held fixed. -/
theorem advance_variance_bound
    {G : Fin n → JointSpace dx dy → JointSpace dx dy} {s : Set (JointSpace dx dy)}
    {L κ : ℝ} (hG : AveragedSmooth G s L) (hκ : 1 ≤ κ) (hb : 0 < b)
    (y0 : DualSpace dy) (ha : ∀ x, jointPoint x y0 ∈ s)
    (q : ℕ) (solve : State dx dy → J → PrimalSpace dx)
    (σ : Measure J) [IsProbabilityMeasure σ] (t : ℕ) (ht : (t + 1) % q ≠ 0)
    (z : State dx dy) :
    (∫ ω, weightedErrorSq κ (error G y0 (advance G y0 q solve t z ω))
      ∂σ.prod (minibatchLaw n b)) ≤ weightedErrorSq κ (error G y0 z) +
        κ * (L ^ 2 / b) * ∫ ω, ‖(advance G y0 q solve t z ω).center - z.center‖ ^ 2
          ∂σ.prod (minibatchLaw n b) := by
  have hlocal (j : J) :
      (∫ I, weightedErrorSq κ (error G y0 (advance G y0 q solve t z (j, I)))
        ∂minibatchLaw n b) ≤ weightedErrorSq κ (error G y0 z) +
          κ * (L ^ 2 / b) * ‖solve z j - z.center‖ ^ 2 := by
    have hh := hG.weighted_persistent_increment_bound hκ hb
      (ha (solve z j)) (ha z.center) z.estimate
    rw [anchor_distance] at hh
    simpa only [error, advance, ite_eq_right ht] using hh
  rw [integral_prod _ Integrable.of_finite,
    integral_prod _ Integrable.of_finite]
  have hh := integral_mono (μ := σ) Integrable.of_finite Integrable.of_finite hlocal
  simpa only [advance_center, integral_const, integral_add Integrable.of_finite
    Integrable.of_finite, integral_const_mul, probReal_univ, one_mul, one_smul] using hh

/-- Source B.4's complete epoch variance inequality for this actual process. -/
theorem process_epoch_variance
    {G : Fin n → JointSpace dx dy → JointSpace dx dy} {s : Set (JointSpace dx dy)}
    {L κ : ℝ} (hG : AveragedSmooth G s L) (hκ : 1 ≤ κ) (hb : 0 < b)
    (y0 : DualSpace dy) (ha : ∀ x, jointPoint x y0 ∈ s)
    {q : ℕ} (hq : 0 < q) (solve : State dx dy → J → PrimalSpace dx)
    (σ : Measure J) [IsProbabilityMeasure σ] (c : PrimalSpace dx) (S : ℕ) :
    (∑ t ∈ Finset.range S, ∫ h,
      weightedErrorSq κ (error G y0 (process G y0 q solve c t h))
      ∂FiniteProcess.law (σ.prod (minibatchLaw n b)) t) ≤
      (q : ℝ) * (κ * (L ^ 2 / b)) * ∑ t ∈ Finset.range S, ∫ h,
        ‖(process G y0 q solve c (t + 1) h).center -
          (process G y0 q solve c t h.1).center‖ ^ 2
        ∂FiniteProcess.law (σ.prod (minibatchLaw n b)) (t + 1) := by
  apply FiniteProcess.epoch_variance_next _ hq
    (mul_nonneg (show 0 ≤ κ by linarith) (div_nonneg (sq_nonneg L) (Nat.cast_nonneg b)))
    (fun t h ↦ weightedErrorSq κ (error G y0 (process G y0 q solve c t h)))
    (fun t h ↦ ‖(process G y0 q solve c (t + 1) h).center -
      (process G y0 q solve c t h.1).center‖ ^ 2)
  · intro t h
    exact weightedErrorSq_nonneg (by linarith) _
  · intro t h
    exact sq_nonneg _
  · intro t ht h
    rw [process_refresh_error G y0 q solve c t ht h]
    simp [weightedErrorSq]
  · intro t ht h
    exact advance_variance_bound hG hκ hb y0 ha q solve σ t ht
      (process G y0 q solve c t h)

end

end NCConcave16991.PersistentProcess
