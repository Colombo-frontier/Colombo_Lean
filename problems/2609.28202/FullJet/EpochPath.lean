import FullJet.SnapshotModelError
import FullJet.UniformPrefixMean

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n B m : ℕ}

noncomputable def epochPathState (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin m → Fin B → Fin n) (t : Fin (m + 1)) : EpochState E :=
  modelEpochRun hp f center M r hr t.val (samplePrefix (Nat.le_of_lt_succ t.isLt) samples)

noncomputable def epochPathPoint (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin m → Fin B → Fin n) (t : Fin (m + 1)) : E :=
  center + (epochPathState hp f center M r hr samples t).offset

noncomputable def epochPathStep (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin m → Fin B → Fin n) (t : Fin m) : E :=
  epochModelStep hp (fun i => fullJet p (f i) center) M r hr
    (epochPathState hp f center M r hr samples t.castSucc)

noncomputable def epochPathError (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin m → Fin B → Fin n) (t : Fin m) : ℝ :=
  ‖(epochPathState hp f center M r hr samples t.castSucc).gradient -
    fderiv ℝ (average f) (epochPathPoint hp f center M r hr samples t.castSucc)‖

noncomputable def epochNoiseBound (p : ℕ) (L : ℝ) (m : ℕ) (r : ℝ) (B : ℕ) : ℝ :=
  Real.sqrt m * (L * ((m : ℝ) * r) ^ (p - 1) * r) / Real.sqrt B

theorem epochNoiseBound_nonneg (p : ℕ) (L : ℝ) (m : ℕ) (r : ℝ) (B : ℕ)
    (hL : 0 ≤ L) (hr : 0 ≤ r) : 0 ≤ epochNoiseBound p L m r B := by
  unfold epochNoiseBound
  positivity

section Path
variable (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E) (M r : ℝ) (hr : 0 ≤ r)
  (samples : Fin m → Fin B → Fin n)

theorem epochPathPoint_zero : epochPathPoint hp f center M r hr samples 0 = center := by
  simp [epochPathPoint, epochPathState, modelEpochRun]

theorem epochPathPoint_last : epochPathPoint hp f center M r hr samples (Fin.last m) =
    center + (modelEpochRun hp f center M r hr m samples).offset := rfl

theorem epochPathPoint_succ (t : Fin m) :
    epochPathPoint hp f center M r hr samples t.succ =
      epochPathPoint hp f center M r hr samples t.castSucc + epochPathStep hp f center M r hr samples t := by
  change center + ((epochPathState hp f center M r hr samples t.castSucc).offset +
    epochPathStep hp f center M r hr samples t) = _
  exact (add_assoc _ _ _).symm

theorem epochPathStep_norm_le (t : Fin m) : ‖epochPathStep hp f center M r hr samples t‖ ≤ r :=
  epochModelStep_norm_le hp _ M r hr _

theorem epochPathState_offset_bound (t : Fin (m + 1)) :
    ‖(epochPathState hp f center M r hr samples t).offset‖ ≤ (m : ℝ) * r := by
  apply (modelEpochRun_offset_bound hp f center M r hr t.val _).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ t.isLt) hr

theorem epochPathError_nonneg (t : Fin m) : 0 ≤ epochPathError hp f center M r hr samples t :=
  norm_nonneg _

end Path

theorem Admissible.epochPath_descent {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (hm : 0 < m)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (samples : Fin m → Fin B → Fin n) (t : Fin m) :
    average f (epochPathPoint hp f center M r hr samples t.succ) ≤
      average f (epochPathPoint hp f center M r hr samples t.castSucc) -
        (M / ((p + 1).factorial : ℝ) - L) * ‖epochPathStep hp f center M r hr samples t‖ ^ (p + 1) +
      r * epochPathError hp f center M r hr samples t +
        ((p : ℝ) * L * (m : ℝ) ^ (p - 1)) * r ^ (p + 1) := by
  rw [epochPathPoint_succ]
  exact hf.epochModelStep_descent hp hL center _ M m r (by exact_mod_cast hm) hr
    (epochPathState_offset_bound hp f center M r hr samples t.castSucc)

theorem Admissible.epochPath_stationarity {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (hm : 0 < m)
    (center : E) (M r : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (samples : Fin m → Fin B → Fin n) (t : Fin m)
    (hinterior : ‖epochPathStep hp f center M r hr samples t‖ < r) :
    ‖fderiv ℝ (average f) (epochPathPoint hp f center M r hr samples t.succ)‖ ≤
      (L + M / (p.factorial : ℝ) + (p : ℝ) * L * (m : ℝ) ^ (p - 1)) * r ^ p +
        epochPathError hp f center M r hr samples t := by
  rw [epochPathPoint_succ]
  exact hf.epochModelStep_stationarity hp hL center _ M m r hM (by exact_mod_cast hm) hr
    (epochPathState_offset_bound hp f center M r hr samples t.castSucc) hinterior

/-- Every prefix of the same fully sampled epoch has the same uniform error
bound, uniformly over the epoch center and all earlier epochs. -/
theorem epochPathError_mean_le [Nonempty (Fin n)] {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (hB : 0 < B) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (t : Fin m) :
    uniformMean (fun samples : Fin m → Fin B → Fin n =>
      epochPathError (p := k + 2) (by omega) f center M r hr samples t) ≤
        epochNoiseBound (k + 2) L m r B := by
  let X := fun past : Fin t.val → Fin B → Fin n =>
    ‖(modelEpochRun (p := k + 2) (by omega) f center M r hr t.val past).gradient -
      fderiv ℝ (average f)
        (center + (modelEpochRun (p := k + 2) (by omega) f center M r hr t.val past).offset)‖
  change uniformMean (fun samples => X (samplePrefix (Nat.le_of_lt t.isLt) samples)) ≤ _
  rw [uniformMean_samplePrefix]
  have hp : k + 2 - 1 = k + 1 := by omega
  unfold epochNoiseBound
  rw [hp]
  calc
    _ ≤ Real.sqrt t.val * (L * ((t.val : ℝ) * r) ^ (k + 1) * r) / Real.sqrt B :=
      modelEpochRun_mean_error hf hB L hL hlip center M r hr t.val
    _ ≤ _ := by gcongr <;> exact_mod_cast Nat.le_of_lt t.isLt

end FullJet
