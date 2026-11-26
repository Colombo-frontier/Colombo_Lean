import FullJet.MultiEpoch
import FullJet.FiniteFailureBound

open scoped BigOperators

namespace FullJet

abbrev RandomEpochSeed (H m B n : ℕ) :=
  (Fin H → Fin m → Fin B → Fin n) × (Fin H × Fin m)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n B m H : ℕ}

/-- The independently selected output is the next point of one uniformly
selected model step. The trajectory has no access to this selection. -/
noncomputable def multiEpochCandidate (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin H → Fin m → Fin B → Fin n)
    (index : Fin H × Fin m) : E :=
  epochPathPoint hp f (multiEpochStart hp f M r hr samples index.1.castSucc)
    M r hr (samples index.1) index.2.succ

noncomputable def multiEpochOutput (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (seed : RandomEpochSeed H m B n) : E :=
  multiEpochCandidate hp f M r hr seed.1 seed.2

theorem Admissible.multiEpoch_failure_indicator {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (hm : 0 < m)
    (M r ε : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r) (hε : 0 < ε)
    (hdet : (L + M / (p.factorial : ℝ) + (p : ℝ) * L * (m : ℝ) ^ (p - 1)) * r ^ p ≤ ε / 2)
    (samples : Fin H → Fin m → Fin B → Fin n) (index : Fin H × Fin m) :
    (if ε < ‖fderiv ℝ (average f) (multiEpochCandidate hp f M r hr samples index)‖ then (1 : ℝ) else 0) ≤
      (if ‖epochPathStep hp f (multiEpochStart hp f M r hr samples index.1.castSucc)
        M r hr (samples index.1) index.2‖ = r then 1 else 0) +
      (2 / ε) * multiEpochError hp f M r hr samples index.1 index.2 := by
  classical
  apply failure_indicator_le_boundary_error _ _ _ _ _ _ hε
    (multiEpochError_nonneg hp f M r hr samples index.1 index.2)
    (epochPathStep_norm_le hp f _ M r hr _ _) hdet
  intro hinterior
  exact hf.epochPath_stationarity hp hL hm _ M r hM hr _ _ hinterior

section Mean
variable [Nonempty (Fin n)] [Nonempty (Fin H)] [Nonempty (Fin m)]

theorem multiEpoch_chosen_boundary_mean (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) :
    uniformMean (fun seed : RandomEpochSeed H m B n =>
      if ‖epochPathStep hp f (multiEpochStart hp f M r hr seed.1 seed.2.1.castSucc)
        M r hr (seed.1 seed.2.1) seed.2.2‖ = r then (1 : ℝ) else 0) =
      uniformMean (fun samples : Fin H → Fin m → Fin B → Fin n =>
        multiEpochBoundaryCount hp f M r hr samples) / ((H : ℝ) * m) := by
  classical
  rw [uniformMean_prod]
  have hi (samples : Fin H → Fin m → Fin B → Fin n) :
      uniformMean (fun index : Fin H × Fin m =>
        if ‖epochPathStep hp f (multiEpochStart hp f M r hr samples index.1.castSucc)
          M r hr (samples index.1) index.2‖ = r then (1 : ℝ) else 0) =
        ((H : ℝ) * m)⁻¹ * multiEpochBoundaryCount hp f M r hr samples := by
    rw [uniformMean_fin_pair (fun e t =>
      if ‖epochPathStep hp f (multiEpochStart hp f M r hr samples e.castSucc)
        M r hr (samples e) t‖ = r then (1 : ℝ) else 0)]
    change multiEpochBoundaryCount hp f M r hr samples / ((H : ℝ) * m) = _
    rw [div_eq_mul_inv, mul_comm]
  simp only [hi, uniformMean_mul]
  rw [div_eq_mul_inv, mul_comm]

theorem multiEpoch_chosen_error_mean_le {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (hB : 0 < B) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (M r : ℝ) (hr : 0 ≤ r) :
    uniformMean (fun seed : RandomEpochSeed H m B n =>
      multiEpochError (p := k + 2) (by omega) f M r hr seed.1 seed.2.1 seed.2.2) ≤
        epochNoiseBound (k + 2) L m r B := by
  rw [uniformMean_prod, uniformMean_comm]
  apply uniformMean_le_const
  intro index
  exact multiEpochError_mean_le hf hB L hL hlip M r hr index.1 index.2

theorem Admissible.multiEpoch_failure_le_count_noise {f : Fin n → E → ℝ} {Δ L : ℝ} {k : ℕ}
    (hf : Admissible (k + 2) n Δ L f) (hB : 0 < B) (hL : 0 ≤ L) (hm : 0 < m)
    (M r ε : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r) (hε : 0 < ε)
    (hdet : (L + M / ((k + 2).factorial : ℝ) + ((k + 2 : ℕ) : ℝ) * L *
      (m : ℝ) ^ (k + 2 - 1)) * r ^ (k + 2) ≤ ε / 2) :
    ((PMF.uniformOfFintype (RandomEpochSeed H m B n)).toOuterMeasure
      {seed | ε < ‖fderiv ℝ (average f) (multiEpochOutput (p := k + 2) (by omega) f M r hr seed)‖}).toReal ≤
      uniformMean (fun samples : Fin H → Fin m → Fin B → Fin n =>
        multiEpochBoundaryCount (p := k + 2) (by omega) f M r hr samples) / ((H : ℝ) * m) +
      (2 / ε) * epochNoiseBound (k + 2) L m r B := by
  classical
  rw [pmf_event_eq_mean_indicator]
  change uniformMean (fun seed : RandomEpochSeed H m B n =>
    if ε < ‖fderiv ℝ (average f) (multiEpochCandidate (p := k + 2) (by omega) f M r hr seed.1 seed.2)‖
      then (1 : ℝ) else 0) ≤ _
  have hb := uniformMean_mono (fun seed : RandomEpochSeed H m B n =>
    hf.multiEpoch_failure_indicator (by omega) hL hm M r ε hM hr hε hdet seed.1 seed.2)
  rw [uniformMean_add, uniformMean_mul, multiEpoch_chosen_boundary_mean] at hb
  have he := multiEpoch_chosen_error_mean_le (H := H) (m := m) hf.smooth hB L hL hf.derivative_lipschitz M r hr
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 / ε by positivity)
  linarith

/-- The actual finite-sum algorithm's independently chosen candidate has a
quantitative failure bound. Parameter selection and oracle-cost compilation
are separate obligations; neither is assumed in this theorem. -/
theorem Admissible.multiEpoch_failure_bound {f : Fin n → E → ℝ} {Δ L : ℝ} {k : ℕ}
    (hf : Admissible (k + 2) n Δ L f) (hB : 0 < B) (hL : 0 ≤ L) (hm : 0 < m) (hH : 0 < H)
    (M r ε : ℝ) (hM : 0 ≤ M) (hr : 0 < r) (hε : 0 < ε)
    (hA : 0 < M / ((k + 2 + 1).factorial : ℝ) - L)
    (hdet : (L + M / ((k + 2).factorial : ℝ) + ((k + 2 : ℕ) : ℝ) * L *
      (m : ℝ) ^ (k + 2 - 1)) * r ^ (k + 2) ≤ ε / 2) :
    ((PMF.uniformOfFintype (RandomEpochSeed H m B n)).toOuterMeasure
      {seed | ε < ‖fderiv ℝ (average f)
        (multiEpochOutput (p := k + 2) (by omega) f M r hr.le seed)‖}).toReal ≤
      (Δ + (H : ℝ) * m * (r * epochNoiseBound (k + 2) L m r B +
        ((k + 2 : ℕ) : ℝ) * L * (m : ℝ) ^ (k + 2 - 1) * r ^ (k + 2 + 1))) /
        ((M / ((k + 2 + 1).factorial : ℝ) - L) * r ^ (k + 2 + 1) * ((H : ℝ) * m)) +
      (2 / ε) * epochNoiseBound (k + 2) L m r B := by
  have hp := hf.multiEpoch_failure_le_count_noise (H := H) hB hL hm M r ε hM hr.le hε hdet
  have hb := hf.multiEpoch_mean_boundary_budget (H := H) hB hL hm M r hr.le hA.le
  let A := (M / ((k + 2 + 1).factorial : ℝ) - L) * r ^ (k + 2 + 1)
  let N := (H : ℝ) * m
  let V := Δ + (H : ℝ) * m * (r * epochNoiseBound (k + 2) L m r B +
    ((k + 2 : ℕ) : ℝ) * L * (m : ℝ) ^ (k + 2 - 1) * r ^ (k + 2 + 1))
  have hAp : 0 < A := mul_pos hA (pow_pos hr _)
  have hNp : 0 < N := mul_pos (by exact_mod_cast hH) (by exact_mod_cast hm)
  have hc : uniformMean (fun samples : Fin H → Fin m → Fin B → Fin n =>
      multiEpochBoundaryCount (p := k + 2) (by omega) f M r hr.le samples) ≤ V / A := by
    apply (le_div_iff₀ hAp).mpr
    change A * uniformMean (fun samples : Fin H → Fin m → Fin B → Fin n =>
      multiEpochBoundaryCount (p := k + 2) (by omega) f M r hr.le samples) ≤ V at hb
    nlinarith
  apply hp.trans
  apply add_le_add_right
  exact (div_le_div_of_nonneg_right hc hNp.le).trans_eq (div_div V A N)

end Mean

end FullJet
