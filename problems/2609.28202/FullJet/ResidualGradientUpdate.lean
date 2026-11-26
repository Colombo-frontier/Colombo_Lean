import FullJet.PacketGradient
import FullJet.FiniteDualMoments
import FullJet.TaylorControlVariate

open scoped BigOperators

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n B : ℕ}

/-- The mean polynomial gradient is evaluated from the saved component packets. -/
noncomputable def snapshotMeanGradient (S : Fin n → JetPacket p E) (h : E) : E →L[ℝ] ℝ :=
  (n : ℝ)⁻¹ • ∑ i, fderiv ℝ (packetPolynomial (S i)) h

/-- One two-point residual increment, using a saved snapshot and two oracle replies. -/
noncomputable def residualReplyIncrement (hp : 1 ≤ p) (snapshot : JetPacket p E)
    (a b : E) (oldReply newReply : JetPacket p E) : E →L[ℝ] ℝ :=
  packetGradient hp newReply - packetGradient hp oldReply -
    (fderiv ℝ (packetPolynomial snapshot) b - fderiv ℝ (packetPolynomial snapshot) a)

/-- A batch update contains only stored data, query replies, and free internal computation. -/
noncomputable def recursiveGradientUpdate (hp : 1 ≤ p) (S : Fin n → JetPacket p E)
    (a b : E) (g : E →L[ℝ] ℝ) (samples : Fin B → Fin n)
    (oldReplies newReplies : Fin B → JetPacket p E) : E →L[ℝ] ℝ :=
  g + (snapshotMeanGradient S b - snapshotMeanGradient S a) +
    (B : ℝ)⁻¹ • ∑ j, residualReplyIncrement hp (S (samples j)) a b (oldReplies j) (newReplies j)

theorem residualReplyIncrement_actual (hp : 1 ≤ p) (f : E → ℝ) (center a b : E) :
    residualReplyIncrement hp (fullJet p f center) a b
      (fullJet p f (center + a)) (fullJet p f (center + b)) =
      componentGradientResidual f p center b - componentGradientResidual f p center a := by
  simp only [residualReplyIncrement, packetGradient_fullJet, componentGradientResidual]
  abel

theorem fderiv_average {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (x : E) :
    fderiv ℝ (average f) x = (n : ℝ)⁻¹ • ∑ i, fderiv ℝ (f i) x := by
  have hc (g : E → ℝ) : continuousMultilinearCurryFin1 ℝ E ℝ (iteratedFDeriv ℝ 1 g x) =
      fderiv ℝ g x := packetGradient_fullJet (p := 1) le_rfl g x
  have h := congrArg (continuousMultilinearCurryFin1 ℝ E ℝ)
    (average_iteratedFDeriv hf 1 hp x)
  simpa only [map_smul, map_sum, hc] using h

theorem uniformMean_component_gradient [Nonempty (Fin n)] {f : Fin n → E → ℝ}
    (hf : ∀ i, ContDiff ℝ p (f i)) (hp : 1 ≤ p) (x : E) :
    uniformMean (fun i => fderiv ℝ (f i) x) = fderiv ℝ (average f) x := by
  rw [uniformMean_eq, Fintype.card_fin, fderiv_average hf hp]

theorem snapshotMeanGradient_eq_uniformMean [Nonempty (Fin n)]
    (S : Fin n → JetPacket p E) (h : E) :
    snapshotMeanGradient S h = uniformMean (fun i => fderiv ℝ (packetPolynomial (S i)) h) := by
  rw [uniformMean_eq, Fintype.card_fin]
  rfl

/-- The exact expectation of the sampled residual increment restores the missing
part of the true finite-sum gradient change. -/
theorem componentGradientResidual_mean_increment [Nonempty (Fin n)] {f : Fin n → E → ℝ}
    (hf : ∀ i, ContDiff ℝ p (f i)) (hp : 1 ≤ p) (center a b : E) :
    uniformMean (fun i => componentGradientResidual (f i) p center b -
      componentGradientResidual (f i) p center a) =
      fderiv ℝ (average f) (center + b) - fderiv ℝ (average f) (center + a) -
        (snapshotMeanGradient (fun i => fullJet p (f i) center) b -
          snapshotMeanGradient (fun i => fullJet p (f i) center) a) := by
  simp only [componentGradientResidual, uniformMean_sub, uniformMean_component_gradient hf hp,
    snapshotMeanGradient_eq_uniformMean]
  abel

/-- Substituting actual oracle replies in the update yields precisely the
centered random increment used by the martingale calculation. -/
theorem recursiveGradientUpdate_error [Nonempty (Fin n)] {f : Fin n → E → ℝ}
    (hf : ∀ i, ContDiff ℝ p (f i)) (hp : 1 ≤ p) (center a b : E)
    (g : E →L[ℝ] ℝ) (samples : Fin B → Fin n) :
    recursiveGradientUpdate hp (fun i => fullJet p (f i) center) a b g samples
      (fun j => fullJet p (f (samples j)) (center + a))
      (fun j => fullJet p (f (samples j)) (center + b)) - fderiv ℝ (average f) (center + b) =
      (g - fderiv ℝ (average f) (center + a)) +
        (batchMean (fun i => componentGradientResidual (f i) p center b -
          componentGradientResidual (f i) p center a) samples -
          uniformMean (fun i => componentGradientResidual (f i) p center b -
            componentGradientResidual (f i) p center a)) := by
  simp only [recursiveGradientUpdate, residualReplyIncrement_actual,
    componentGradientResidual_mean_increment hf hp, batchMean]
  abel

/-- The initial exact gradient is obtainable from the n snapshot replies. -/
theorem snapshot_initial_gradient {f : Fin n → E → ℝ}
    (hf : ∀ i, ContDiff ℝ p (f i)) (hp : 1 ≤ p) (center : E) :
    (n : ℝ)⁻¹ • ∑ i, packetGradient hp (fullJet p (f i) center) =
      fderiv ℝ (average f) center := by
  simp only [packetGradient_fullJet, fderiv_average hf hp]

end FullJet
