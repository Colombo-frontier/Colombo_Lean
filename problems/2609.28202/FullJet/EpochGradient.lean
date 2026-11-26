import FullJet.ResidualGradientUpdate

open scoped BigOperators

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n B : ℕ}

/-- The next point is fixed from the past, before drawing the new batch. -/
def epochOffset (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E) :
    (t : ℕ) → (Fin t → Fin B → Fin n) → E
  | 0, _ => 0
  | t + 1, samples => next t (Fin.init samples)

@[simp] theorem epochOffset_snoc (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E)
    (t : ℕ) (past : Fin t → Fin B → Fin n) (samples : Fin B → Fin n) :
    epochOffset next (t + 1) (Fin.snoc past samples) = next t past := by
  simp [epochOffset]

/-- Semantics of one epoch's recursive estimator, with all replies evaluated
at their actual queried points. The snapshot is shared across the epoch. -/
noncomputable def epochGradientEstimate (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E)
    (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E) :
    (t : ℕ) → (Fin t → Fin B → Fin n) → E →L[ℝ] ℝ
  | 0, _ => (n : ℝ)⁻¹ • ∑ i, packetGradient hp (fullJet p (f i) center)
  | t + 1, samples =>
      let past := Fin.init samples
      let batch := samples (Fin.last t)
      let a := epochOffset next t past
      let b := next t past
      recursiveGradientUpdate hp (fun i => fullJet p (f i) center) a b
        (epochGradientEstimate hp f center next t past) batch
        (fun j => fullJet p (f (batch j)) (center + a))
        (fun j => fullJet p (f (batch j)) (center + b))

noncomputable def epochResidualIncrement (f : Fin n → E → ℝ) (p : ℕ) (center : E)
    (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E)
    (t : ℕ) (past : Fin t → Fin B → Fin n) (i : Fin n) : E →L[ℝ] ℝ :=
  componentGradientResidual (f i) p center (next t past) -
    componentGradientResidual (f i) p center (epochOffset next t past)

theorem epochGradientEstimate_snoc (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E)
    (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E)
    (t : ℕ) (past : Fin t → Fin B → Fin n) (samples : Fin B → Fin n) :
    epochGradientEstimate hp f center next (t + 1) (Fin.snoc past samples) =
      recursiveGradientUpdate hp (fun i => fullJet p (f i) center)
        (epochOffset next t past) (next t past) (epochGradientEstimate hp f center next t past) samples
        (fun j => fullJet p (f (samples j)) (center + epochOffset next t past))
        (fun j => fullJet p (f (samples j)) (center + next t past)) := by
  simp [epochGradientEstimate]

/-- Equality with the centered adaptive sample process is proved from the
oracle reply formula, rather than assumed as a property of the estimator. -/
theorem epochGradientEstimate_error [Nonempty (Fin n)] {f : Fin n → E → ℝ}
    (hf : ∀ i, ContDiff ℝ p (f i)) (hp : 1 ≤ p) (center : E)
    (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E)
    (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    epochGradientEstimate hp f center next t samples -
      fderiv ℝ (average f) (center + epochOffset next t samples) =
        adaptiveBatchError (epochResidualIncrement f p center next) t samples := by
  induction t with
  | zero => simp [epochGradientEstimate, epochOffset, snapshot_initial_gradient hf hp]
  | succ t ih =>
    have hs : ∃ (past : Fin t → Fin B → Fin n) (batch : Fin B → Fin n),
        samples = Fin.snoc past batch :=
      ⟨Fin.init samples, samples (Fin.last t), (Fin.snoc_init_self samples).symm⟩
    obtain ⟨past, batch, rfl⟩ := hs
    rw [epochGradientEstimate_snoc, epochOffset_snoc, recursiveGradientUpdate_error hf hp,
      adaptiveBatchError_snoc, ih]
    rfl

/-- Bounded successive steps bound distance from the snapshot, for every history. -/
theorem epochOffset_norm_le
    (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E) (r : ℝ) (T : ℕ)
    (hstep : ∀ t < T, ∀ past, ‖next t past - epochOffset next t past‖ ≤ r)
    (samples : Fin T → Fin B → Fin n) : ‖epochOffset next T samples‖ ≤ (T : ℝ) * r := by
  induction T with
  | zero => simp [epochOffset]
  | succ t ih =>
    change ‖next t (Fin.init samples)‖ ≤ _
    have hb := ih (fun j hj => hstep j (by omega)) (Fin.init samples)
    have hs := hstep t (by omega) (Fin.init samples)
    have ht := norm_add_le (next t (Fin.init samples) - epochOffset next t (Fin.init samples))
      (epochOffset next t (Fin.init samples))
    rw [sub_add_cancel] at ht
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith

theorem epochNext_norm_le
    (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E) (r : ℝ) (T : ℕ)
    (hstep : ∀ t ≤ T, ∀ past, ‖next t past - epochOffset next t past‖ ≤ r)
    (past : Fin T → Fin B → Fin n) : ‖next T past‖ ≤ ((T : ℝ) + 1) * r := by
  have hb := epochOffset_norm_le next r T (fun j hj => hstep j (Nat.le_of_lt hj)) past
  have hs := hstep T le_rfl past
  have ht := norm_add_le (next T past - epochOffset next T past) (epochOffset next T past)
  rw [sub_add_cancel] at ht
  nlinarith

theorem epochResidualIncrement_bound {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (center : E) (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E) (T : ℕ)
    (hstep : ∀ t < T, ∀ past, ‖next t past - epochOffset next t past‖ ≤ r)
    (t : ℕ) (ht : t < T) (past : Fin t → Fin B → Fin n) (i : Fin n) :
    ‖epochResidualIncrement f (k + 2) center next t past i‖ ≤ L * ((T : ℝ) * r) ^ (k + 1) * r := by
  have ha : ‖epochOffset next t past‖ ≤ (T : ℝ) * r := by
    apply (epochOffset_norm_le next r t (fun j hj => hstep j (by omega)) past).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt ht) hr
  have hb : ‖next t past‖ ≤ (T : ℝ) * r := by
    apply (epochNext_norm_le next r t (fun j hj => hstep j (by omega)) past).trans
    apply mul_le_mul_of_nonneg_right _ hr
    exact_mod_cast ht
  exact (componentGradientResidual_increment (hf i) L ((T : ℝ) * r) hL (hlip i)
    center (epochOffset next t past) (next t past) ha hb).trans
      (mul_le_mul_of_nonneg_left (hstep t ht past) (by positivity))

section Moments
variable [Nonempty (Fin n)] [CompleteSpace E]

/-- Unbiasedness holds relative to the true gradient at the adaptively chosen point. -/
theorem epochGradientEstimate_unbiased {f : Fin n → E → ℝ}
    (hf : ∀ i, ContDiff ℝ p (f i)) (hp : 1 ≤ p) (hB : 0 < B) (center : E)
    (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E) (T : ℕ) :
    uniformMean (fun samples => epochGradientEstimate hp f center next T samples -
      fderiv ℝ (average f) (center + epochOffset next T samples)) = 0 := by
  simp only [epochGradientEstimate_error hf hp]
  exact dual_adaptiveBatchError_mean_zero _ hB T

/-- The epoch's actual gradient error has the required dimension-free second moment. -/
theorem epochGradientEstimate_second_moment {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (hB : 0 < B) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (center : E) (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E) (T : ℕ)
    (hstep : ∀ t < T, ∀ past, ‖next t past - epochOffset next t past‖ ≤ r) :
    uniformMean (fun samples => ‖epochGradientEstimate (p := k + 2) (by omega) f center next T samples -
      fderiv ℝ (average f) (center + epochOffset next T samples)‖ ^ 2) ≤
      (T : ℝ) * (L * ((T : ℝ) * r) ^ (k + 1) * r) ^ 2 / B := by
  simp only [epochGradientEstimate_error hf]
  exact dual_adaptiveBatchError_second_moment_upto _ hB _ T
    (epochResidualIncrement_bound hf L r hL hr hlip center next T hstep)

theorem epochGradientEstimate_mean_error {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (hB : 0 < B) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (center : E) (next : (t : ℕ) → (Fin t → Fin B → Fin n) → E) (T : ℕ)
    (hstep : ∀ t < T, ∀ past, ‖next t past - epochOffset next t past‖ ≤ r) :
    uniformMean (fun samples => ‖epochGradientEstimate (p := k + 2) (by omega) f center next T samples -
      fderiv ℝ (average f) (center + epochOffset next T samples)‖) ≤
      Real.sqrt T * (L * ((T : ℝ) * r) ^ (k + 1) * r) / Real.sqrt B := by
  simp only [epochGradientEstimate_error hf]
  exact dual_adaptiveBatchError_mean_norm_upto _ hB _ (by positivity) T
    (epochResidualIncrement_bound hf L r hL hr hlip center next T hstep)

end Moments

end FullJet
