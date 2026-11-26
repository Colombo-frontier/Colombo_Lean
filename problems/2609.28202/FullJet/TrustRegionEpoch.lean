import FullJet.EpochGradient

open scoped BigOperators

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n B : ℕ}

structure EpochState (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  offset : E
  gradient : E →L[ℝ] ℝ

/-- Higher derivatives come from the mean saved polynomial; the first derivative
is the recursively updated estimator. No fresh higher derivatives are used. -/
noncomputable def epochModelPacket (hp : 1 ≤ p) (S : Fin n → JetPacket p E)
    (state : EpochState E) : JetPacket p E :=
  replacePacketGradient hp (snapshotJet ((n : ℝ)⁻¹ • ∑ i, S i) state.offset) state.gradient

noncomputable def epochModelStep [FiniteDimensional ℝ E] (hp : 1 ≤ p)
    (S : Fin n → JetPacket p E) (M r : ℝ) (hr : 0 ≤ r) (state : EpochState E) : E :=
  regularizedJetStep (epochModelPacket hp S state) M r hr

theorem epochModelStep_norm_le [FiniteDimensional ℝ E] (hp : 1 ≤ p)
    (S : Fin n → JetPacket p E) (M r : ℝ) (hr : 0 ≤ r) (state : EpochState E) :
    ‖epochModelStep hp S M r hr state‖ ≤ r :=
  (regularizedJetStep_spec _ M r hr).1

/-- One trust-region epoch, interpreted with actual component-oracle replies.
The next point is chosen before the new batch, and the resulting replies update
the gradient used by the following step. -/
noncomputable def modelEpochRun [FiniteDimensional ℝ E] (hp : 1 ≤ p)
    (f : Fin n → E → ℝ) (center : E) (M r : ℝ) (hr : 0 ≤ r) :
    (t : ℕ) → (Fin t → Fin B → Fin n) → EpochState E
  | 0, _ => ⟨0, (n : ℝ)⁻¹ • ∑ i, packetGradient hp (fullJet p (f i) center)⟩
  | t + 1, samples =>
      let state := modelEpochRun hp f center M r hr t (Fin.init samples)
      let S := fun i => fullJet p (f i) center
      let b := state.offset + epochModelStep hp S M r hr state
      let batch := samples (Fin.last t)
      ⟨b, recursiveGradientUpdate hp S state.offset b state.gradient batch
        (fun j => fullJet p (f (batch j)) (center + state.offset))
        (fun j => fullJet p (f (batch j)) (center + b))⟩

noncomputable def modelEpochNext [FiniteDimensional ℝ E] (hp : 1 ≤ p)
    (f : Fin n → E → ℝ) (center : E) (M r : ℝ) (hr : 0 ≤ r)
    (t : ℕ) (past : Fin t → Fin B → Fin n) : E :=
  let state := modelEpochRun hp f center M r hr t past
  state.offset + epochModelStep hp (fun i => fullJet p (f i) center) M r hr state

section Correspondence
variable [FiniteDimensional ℝ E] (hp : 1 ≤ p) (f : Fin n → E → ℝ)
  (center : E) (M r : ℝ) (hr : 0 ≤ r)

theorem modelEpochRun_offset_eq (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    (modelEpochRun hp f center M r hr t samples).offset =
      epochOffset (modelEpochNext hp f center M r hr) t samples := by
  cases t <;> rfl

theorem modelEpochRun_gradient_eq (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    (modelEpochRun hp f center M r hr t samples).gradient =
      epochGradientEstimate hp f center (modelEpochNext hp f center M r hr) t samples := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change recursiveGradientUpdate hp (fun i => fullJet p (f i) center)
      (modelEpochRun hp f center M r hr t (Fin.init samples)).offset
      (modelEpochNext hp f center M r hr t (Fin.init samples))
      (modelEpochRun hp f center M r hr t (Fin.init samples)).gradient
      (samples (Fin.last t)) _ _ = _
    rw [epochGradientEstimate]
    change _ = recursiveGradientUpdate hp (fun i => fullJet p (f i) center)
      (epochOffset (modelEpochNext hp f center M r hr) t (Fin.init samples))
      (modelEpochNext hp f center M r hr t (Fin.init samples))
      (epochGradientEstimate hp f center (modelEpochNext hp f center M r hr) t (Fin.init samples))
      (samples (Fin.last t)) _ _
    rw [← modelEpochRun_offset_eq, ← ih]
    rfl

theorem modelEpochNext_step_bound (t : ℕ) (past : Fin t → Fin B → Fin n) :
    ‖modelEpochNext hp f center M r hr t past -
      epochOffset (modelEpochNext hp f center M r hr) t past‖ ≤ r := by
  rw [← modelEpochRun_offset_eq]
  simp only [modelEpochNext, add_sub_cancel_left]
  exact epochModelStep_norm_le hp _ M r hr _

theorem modelEpochRun_offset_bound (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    ‖(modelEpochRun hp f center M r hr t samples).offset‖ ≤ (t : ℝ) * r := by
  rw [modelEpochRun_offset_eq]
  exact epochOffset_norm_le _ r t (fun j _ => modelEpochNext_step_bound hp f center M r hr j) samples

end Correspondence

theorem epochModelPacket_snapshot {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (center : E) (state : EpochState E) :
    epochModelPacket hp (fun i => fullJet p (f i) center) state =
      replacePacketGradient hp (snapshotJet (fullJet p (average f) center) state.offset) state.gradient := by
  rw [epochModelPacket, average_fullJet hf]

theorem epochModelPacket_gradient_error {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (center : E) (state : EpochState E) :
    ‖fullJet p (average f) (center + state.offset) ⟨1, Nat.lt_succ_of_le hp⟩ -
      epochModelPacket hp (fun i => fullJet p (f i) center) state ⟨1, Nat.lt_succ_of_le hp⟩‖ =
      ‖fderiv ℝ (average f) (center + state.offset) - state.gradient‖ := by
  rw [epochModelPacket_snapshot hf, replacePacketGradient_first_error]

theorem Admissible.epochModelPacket_higher_error {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (center : E)
    (state : EpochState E) (j : Fin (p + 1)) (hj : j.val ≠ 1) :
    ‖fullJet p (average f) (center + state.offset) j -
      epochModelPacket hp (fun i => fullJet p (f i) center) state j‖ ≤
        L * ‖state.offset‖ ^ (p - j.val + 1) := by
  rw [epochModelPacket_snapshot hf.smooth, replacePacketGradient_other hp _ _ j hj]
  exact hf.snapshot_error hL center state.offset j

section Guarantees
variable [FiniteDimensional ℝ E] [Nonempty (Fin n)]

theorem modelEpochRun_unbiased {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (hB : 0 < B) (center : E) (M r : ℝ) (hr : 0 ≤ r) (T : ℕ) :
    uniformMean (fun samples : Fin T → Fin B → Fin n =>
      (modelEpochRun hp f center M r hr T samples).gradient -
        fderiv ℝ (average f) (center + (modelEpochRun hp f center M r hr T samples).offset)) = 0 := by
  simp only [modelEpochRun_gradient_eq, modelEpochRun_offset_eq]
  exact epochGradientEstimate_unbiased hf hp hB center _ T

/-- A bound for the actual model-driven epoch, with no assumed estimator
accuracy or step-size property left in the hypotheses. -/
theorem modelEpochRun_mean_error {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (hB : 0 < B) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (T : ℕ) :
    uniformMean (fun samples : Fin T → Fin B → Fin n =>
      ‖(modelEpochRun (p := k + 2) (by omega) f center M r hr T samples).gradient -
        fderiv ℝ (average f)
          (center + (modelEpochRun (p := k + 2) (by omega) f center M r hr T samples).offset)‖) ≤
      Real.sqrt T * (L * ((T : ℝ) * r) ^ (k + 1) * r) / Real.sqrt B := by
  simp only [modelEpochRun_gradient_eq, modelEpochRun_offset_eq]
  apply epochGradientEstimate_mean_error hf hB L r hL hr hlip center _ T
  intro t ht
  exact modelEpochNext_step_bound _ f center M r hr t

end Guarantees

end FullJet
