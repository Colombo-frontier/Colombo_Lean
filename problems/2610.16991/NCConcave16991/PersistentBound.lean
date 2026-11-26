import NCConcave16991.PersistentAnalysis

/-! # Persistent-error absorption for the actual finite-seed process -/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.PersistentProcess

noncomputable section

variable {n b dx dy : ℕ} [NeZero n] [MeasurableSpace (Fin n)]
  [MeasurableSingletonClass (Fin n)]
  {J : Type*} [Finite J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem mean_error_sum_bound
    {G : Fin n → JointSpace dx dy → JointSpace dx dy} {s : Set (JointSpace dx dy)}
    {L κ noise : ℝ} (hL : 0 < L) (hG : AveragedSmooth G s L) (hκ : 1 ≤ κ)
    (hb : 0 < b) (hn : 0 ≤ noise)
    (y0 : DualSpace dy) (ha : ∀ x, jointPoint x y0 ∈ s)
    {q : ℕ} (hq : 0 < q) (hbatch : κ * q / b ≤ 1 / 4096)
    (solve : State dx dy → J → PrimalSpace dx)
    (σ : Measure J) [IsProbabilityMeasure σ] (c : PrimalSpace dx)
    (prox : PrimalSpace dx → PrimalSpace dx)
    (hsolve : ∀ z, (∫ j, ‖solve z j - prox z.center‖ ^ 2 ∂σ) ≤
      (1 / 1024 : ℝ) * ‖prox z.center - z.center‖ ^ 2 +
        3 * weightedErrorSq κ (error G y0 z) / L ^ 2 + noise)
    (S : ℕ) :
    (∑ t ∈ Finset.range S,
      meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - prox z.center‖ ^ 2) t) ≤
      (∑ t ∈ Finset.range S,
        meanAt (b := b) G y0 q solve σ c (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t) / 128 +
          2 * S * noise := by
  let D := ∑ t ∈ Finset.range S,
    meanAt (b := b) G y0 q solve σ c (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t
  let E := ∑ t ∈ Finset.range S,
    meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - prox z.center‖ ^ 2) t
  let W := ∑ t ∈ Finset.range S,
    meanAt (b := b) G y0 q solve σ c (fun z ↦ weightedErrorSq κ (error G y0 z)) t
  let M := ∑ t ∈ Finset.range S,
    meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - z.center‖ ^ 2) t
  have hD : 0 ≤ D := Finset.sum_nonneg (fun t _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  have hE : 0 ≤ E := Finset.sum_nonneg (fun t _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  have hv : W ≤ (q : ℝ) * (κ * (L ^ 2 / b)) * M :=
    process_epoch_variance hG hκ hb y0 ha hq solve σ c S
  have hscaled : W / L ^ 2 ≤ (κ * q / b) * M := by
    apply (div_le_iff₀ (sq_pos_of_pos hL)).2
    calc
      W ≤ (q : ℝ) * (κ * (L ^ 2 / b)) * M := hv
      _ = (κ * q / b * M) * L ^ 2 := by ring
  have hm := Finset.sum_le_sum (s := Finset.range S)
    (fun t _ ↦ mean_movement_bound (b := b) G y0 q solve σ c prox t)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hm
  change M ≤ 2 * D + 2 * E at hm
  have hi := Finset.sum_le_sum (s := Finset.range S)
    (fun t _ ↦ mean_inner_error_bound (b := b) G y0 q solve σ c prox κ L
      (1 / 1024) noise hsolve t)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hi
  change E ≤ (1 / 1024 : ℝ) * D + 3 * W / L ^ 2 + S * noise at hi
  have hθ : 0 ≤ κ * q / b := div_nonneg
    (mul_nonneg (by linarith) (Nat.cast_nonneg q)) (Nat.cast_nonneg b)
  have hmove := mul_le_mul_of_nonneg_left hm hθ
  have he : E ≤ D / 1024 + 3 * (κ * q / b) * (2 * D + 2 * E) + S * noise := by
    rw [show 3 * W / L ^ 2 = 3 * (W / L ^ 2) by ring] at hi
    nlinarith only [hi, hscaled, hmove]
  have hh := persistent_error_absorption hD hE
    (mul_nonneg (Nat.cast_nonneg S) hn) hbatch he
  change E ≤ D / 128 + 2 * S * noise
  nlinarith only [hh]

/-- The source mean-displacement bound now follows for the actual process,
using its true envelope descent rather than a supplied trajectory certificate. -/
theorem mean_displacement_bound
    {G : Fin n → JointSpace dx dy → JointSpace dx dy} {s : Set (JointSpace dx dy)}
    {f : PrimalSpace dx → ℝ} {L κ noise Δ : ℝ}
    (hL : 0 < L) (hG : AveragedSmooth G s L) (hκ : 1 ≤ κ)
    (hb : 0 < b) (hn : 0 ≤ noise) (hf : BddBelow (range f))
    (y0 : DualSpace dy) (ha : ∀ x, jointPoint x y0 ∈ s)
    {q : ℕ} (hq : 0 < q) (hbatch : κ * q / b ≤ 1 / 4096)
    (solve : State dx dy → J → PrimalSpace dx)
    (σ : Measure J) [IsProbabilityMeasure σ] (c : PrimalSpace dx)
    (hgap : f c - sInf (range f) ≤ Δ)
    (prox : PrimalSpace dx → PrimalSpace dx)
    (hp : ∀ x, IsProxPoint f L x (prox x))
    (hsolve : ∀ z, (∫ j, ‖solve z j - prox z.center‖ ^ 2 ∂σ) ≤
      (1 / 1024 : ℝ) * ‖prox z.center - z.center‖ ^ 2 +
        3 * weightedErrorSq κ (error G y0 z) / L ^ 2 + noise)
    {S : ℕ} (hS : 0 < S) :
    (∑ t ∈ Finset.range S,
      meanAt (b := b) G y0 q solve σ c (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t) / S ≤
        (128 / 127 : ℝ) * (Δ / (L * S) + 2 * noise) := by
  let D := ∑ t ∈ Finset.range S,
    meanAt (b := b) G y0 q solve σ c (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t
  let E := ∑ t ∈ Finset.range S,
    meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - prox z.center‖ ^ 2) t
  have herr : E ≤ D / 128 + 2 * S * noise :=
    mean_error_sum_bound hL hG hκ hb hn y0 ha hq hbatch solve σ c prox hsolve S
  have ht := descent_telescopes
    (meanAt (b := b) G y0 q solve σ c (fun z ↦ moreauEnvelope f L z.center))
    (meanAt (b := b) G y0 q solve σ c (fun z ↦ ‖prox z.center - z.center‖ ^ 2))
    (meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - prox z.center‖ ^ 2)) L
    (mean_envelope_descent (b := b) G y0 q solve σ c hL.le hf prox hp) S
  have hlow : sInf (range f) ≤
      meanAt (b := b) G y0 q solve σ c (fun z ↦ moreauEnvelope f L z.center) S := by
    letI : IsProbabilityMeasure (FiniteProcess.law (σ.prod (minibatchLaw n b)) S) :=
      FiniteProcess.law_probability _ _
    have hh := integral_mono (μ := FiniteProcess.law (σ.prod (minibatchLaw n b)) S)
      (Integrable.of_finite (f := fun _ ↦ sInf (range f))) Integrable.of_finite
      (fun h ↦ inf_le_moreauEnvelope hL.le hf (process G y0 q solve c S h).center)
    simpa only [integral_const, probReal_univ, one_smul, meanAt] using hh
  have hinitial : meanAt (b := b) G y0 q solve σ c
      (fun z ↦ moreauEnvelope f L z.center) 0 ≤ f c := by
    simpa only [meanAt, process, FiniteProcess.trajectory, initial, FiniteProcess.law,
      integral_dirac] using moreauEnvelope_le_value hL.le hf c
  change _ + L * D ≤ _ + L * E at ht
  have hmain : (127 / 128 : ℝ) * L * D ≤ Δ + 2 * L * S * noise := by
    have he := mul_le_mul_of_nonneg_left herr hL.le
    nlinarith only [ht, hlow, hinitial, hgap, he]
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  apply (div_le_iff₀ hSr).2
  apply (mul_le_mul_iff_left₀ (mul_pos (by norm_num : (0 : ℝ) < 127 / 128) hL)).mp
  convert hmain using 1 <;> field_simp [hL.ne', hSr.ne'] <;> ring

end

end NCConcave16991.PersistentProcess
