import FullJet.TrustRegionEpoch

open scoped BigOperators

namespace FullJet

theorem inv_factorial_le_one (j : ℕ) : ((j.factorial : ℝ)⁻¹) ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact_mod_cast Nat.factorial_pos j

/-- Isolate the first-order error and give every other order a common bound. -/
theorem sum_error_first_bound {p : ℕ} (hp : 0 < p) (e : Fin p → ℝ) (ζ C : ℝ)
    (hC : 0 ≤ C) (hfirst : e ⟨0, hp⟩ ≤ ζ)
    (hrest : ∀ j, j.val ≠ 0 → e j ≤ C) :
    ∑ j, e j ≤ ζ + (p : ℝ) * C := by
  classical
  calc
    _ ≤ ∑ j : Fin p, ((if j = ⟨0, hp⟩ then ζ else 0) + C) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = ⟨0, hp⟩
      · subst j
        simp only [if_true]
        linarith
      · simp only [if_neg hj, zero_add]
        apply hrest j
        intro hz
        exact hj (Fin.ext hz)
    _ = _ := by simp [Finset.sum_add_distrib]

section Weighted
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

theorem jetGradientError_le_unweighted (J K : JetPacket p E) (r : ℝ) (hr : 0 ≤ r) :
    jetGradientError J K r ≤ ∑ j : Fin p, ‖J j.succ - K j.succ‖ * r ^ j.val := by
  apply Finset.sum_le_sum
  intro j _
  calc
    _ = (j.val.factorial : ℝ)⁻¹ * (‖J j.succ - K j.succ‖ * r ^ j.val) := by ring
    _ ≤ 1 * (‖J j.succ - K j.succ‖ * r ^ j.val) :=
      mul_le_mul_of_nonneg_right (inv_factorial_le_one _) (by positivity)
    _ = _ := one_mul _

theorem jetValueError_le_unweighted (J K : JetPacket p E) (r : ℝ) (hr : 0 ≤ r) :
    jetValueError J K r ≤ r * ∑ j : Fin p, ‖J j.succ - K j.succ‖ * r ^ j.val := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ = ((j.val + 1).factorial : ℝ)⁻¹ * (r * (‖J j.succ - K j.succ‖ * r ^ j.val)) := by
      rw [pow_succ]
      ring
    _ ≤ 1 * (r * (‖J j.succ - K j.succ‖ * r ^ j.val)) :=
      mul_le_mul_of_nonneg_right (inv_factorial_le_one _) (by positivity)
    _ = _ := one_mul _

/-- The powers of the step radius combine to p, while the snapshot-period
factor has exponent at most p-1 for every derivative order at least two. -/
theorem snapshot_scaled_power_le {p j : ℕ} (hj : 1 ≤ j) (hjp : j < p)
    (m r : ℝ) (hm : 1 ≤ m) (hr : 0 ≤ r) :
    (m * r) ^ (p - (j + 1) + 1) * r ^ j ≤ m ^ (p - 1) * r ^ p := by
  have he : p - (j + 1) + 1 + j = p := by omega
  rw [mul_pow, mul_assoc, ← pow_add, he]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hm (by omega)) (pow_nonneg hr p)

theorem Admissible.epochModelPacket_scaled_higher_error {n : ℕ} {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (center : E)
    (state : EpochState E) (m r : ℝ) (hm : 1 ≤ m) (hr : 0 ≤ r)
    (hstate : ‖state.offset‖ ≤ m * r) (j : Fin p) (hj : j.val ≠ 0) :
    ‖fullJet p (average f) (center + state.offset) j.succ -
      epochModelPacket hp (fun i => fullJet p (f i) center) state j.succ‖ * r ^ j.val ≤
        L * m ^ (p - 1) * r ^ p := by
  have hh := hf.epochModelPacket_higher_error hp hL center state j.succ (by simpa using hj)
  simp only [Fin.val_succ] at hh
  have hh' : ‖fullJet p (average f) (center + state.offset) j.succ -
      epochModelPacket hp (fun i => fullJet p (f i) center) state j.succ‖ ≤
        L * (m * r) ^ (p - (j.val + 1) + 1) := by
    apply hh.trans
    gcongr
  calc
    _ ≤ (L * (m * r) ^ (p - (j.val + 1) + 1)) * r ^ j.val :=
      mul_le_mul_of_nonneg_right hh' (pow_nonneg hr _)
    _ = L * ((m * r) ^ (p - (j.val + 1) + 1) * r ^ j.val) := by ring
    _ ≤ L * (m ^ (p - 1) * r ^ p) :=
      mul_le_mul_of_nonneg_left (snapshot_scaled_power_le (by omega) j.isLt m r hm hr) hL
    _ = _ := by ring

theorem Admissible.epochModelPacket_unweighted_error {n : ℕ} {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (center : E)
    (state : EpochState E) (m r : ℝ) (hm : 1 ≤ m) (hr : 0 ≤ r)
    (hstate : ‖state.offset‖ ≤ m * r) :
    (∑ j : Fin p, ‖fullJet p (average f) (center + state.offset) j.succ -
      epochModelPacket hp (fun i => fullJet p (f i) center) state j.succ‖ * r ^ j.val) ≤
        ‖state.gradient - fderiv ℝ (average f) (center + state.offset)‖ +
          (p : ℝ) * L * m ^ (p - 1) * r ^ p := by
  have h := sum_error_first_bound (show 0 < p by omega)
    (fun j : Fin p => ‖fullJet p (average f) (center + state.offset) j.succ -
      epochModelPacket hp (fun i => fullJet p (f i) center) state j.succ‖ * r ^ j.val)
    ‖state.gradient - fderiv ℝ (average f) (center + state.offset)‖
    (L * m ^ (p - 1) * r ^ p) (by positivity) ?_
    (fun j hj => hf.epochModelPacket_scaled_higher_error hp hL center state m r hm hr hstate j hj)
  · convert h using 1 <;> ring
  · simp only [pow_zero, mul_one]
    change ‖fullJet p (average f) (center + state.offset) ⟨1, Nat.lt_succ_of_le hp⟩ -
      epochModelPacket hp (fun i => fullJet p (f i) center) state ⟨1, Nat.lt_succ_of_le hp⟩‖ ≤ _
    rw [epochModelPacket_gradient_error hf.smooth hp]
    exact le_of_eq (norm_sub_rev _ _)

/-- Weighted model-gradient error for an actual stored snapshot and recursive gradient. -/
theorem Admissible.epochModelPacket_gradientError {n : ℕ} {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (center : E)
    (state : EpochState E) (m r : ℝ) (hm : 1 ≤ m) (hr : 0 ≤ r)
    (hstate : ‖state.offset‖ ≤ m * r) :
    jetGradientError (fullJet p (average f) (center + state.offset))
      (epochModelPacket hp (fun i => fullJet p (f i) center) state) r ≤
        ‖state.gradient - fderiv ℝ (average f) (center + state.offset)‖ +
          ((p : ℝ) * L * m ^ (p - 1)) * r ^ p :=
  (jetGradientError_le_unweighted _ _ r hr).trans
    (hf.epochModelPacket_unweighted_error hp hL center state m r hm hr hstate)

theorem Admissible.epochModelPacket_valueError {n : ℕ} {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (center : E)
    (state : EpochState E) (m r : ℝ) (hm : 1 ≤ m) (hr : 0 ≤ r)
    (hstate : ‖state.offset‖ ≤ m * r) :
    jetValueError (fullJet p (average f) (center + state.offset))
      (epochModelPacket hp (fun i => fullJet p (f i) center) state) r ≤
        r * ‖state.gradient - fderiv ℝ (average f) (center + state.offset)‖ +
          ((p : ℝ) * L * m ^ (p - 1)) * r ^ (p + 1) := by
  apply (jetValueError_le_unweighted _ _ r hr).trans
  apply (mul_le_mul_of_nonneg_left
    (hf.epochModelPacket_unweighted_error hp hL center state m r hm hr hstate) hr).trans_eq
  rw [pow_succ]
  ring

theorem Admissible.epochModelStep_descent [FiniteDimensional ℝ E]
    {n : ℕ} {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (center : E)
    (state : EpochState E) (M m r : ℝ) (hm : 1 ≤ m) (hr : 0 ≤ r)
    (hstate : ‖state.offset‖ ≤ m * r) :
    average f (center + state.offset + epochModelStep hp (fun i => fullJet p (f i) center) M r hr state) ≤
      average f (center + state.offset) - (M / ((p + 1).factorial : ℝ) - L) *
        ‖epochModelStep hp (fun i => fullJet p (f i) center) M r hr state‖ ^ (p + 1) +
      r * ‖state.gradient - fderiv ℝ (average f) (center + state.offset)‖ +
        ((p : ℝ) * L * m ^ (p - 1)) * r ^ (p + 1) := by
  have hd := hf.model_step_descent hL (center + state.offset)
    (epochModelPacket hp (fun i => fullJet p (f i) center) state) M r hr
  have he := hf.epochModelPacket_valueError hp hL center state m r hm hr hstate
  change average f (center + state.offset +
    epochModelStep hp (fun i => fullJet p (f i) center) M r hr state) ≤ average f (center + state.offset) -
    (M / ((p + 1).factorial : ℝ) - L) *
      ‖epochModelStep hp (fun i => fullJet p (f i) center) M r hr state‖ ^ (p + 1) + _ at hd
  linarith

theorem Admissible.epochModelStep_stationarity [FiniteDimensional ℝ E]
    {n : ℕ} {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (center : E)
    (state : EpochState E) (M m r : ℝ) (hM : 0 ≤ M) (hm : 1 ≤ m) (hr : 0 ≤ r)
    (hstate : ‖state.offset‖ ≤ m * r)
    (hinterior : ‖epochModelStep hp (fun i => fullJet p (f i) center) M r hr state‖ < r) :
    ‖fderiv ℝ (average f)
      (center + state.offset + epochModelStep hp (fun i => fullJet p (f i) center) M r hr state)‖ ≤
      (L + M / (p.factorial : ℝ) + (p : ℝ) * L * m ^ (p - 1)) * r ^ p +
        ‖state.gradient - fderiv ℝ (average f) (center + state.offset)‖ := by
  have hd := hf.model_step_stationarity (show 0 < p by omega) hL (center + state.offset)
    (epochModelPacket hp (fun i => fullJet p (f i) center) state) M r hM hr hinterior
  have he := hf.epochModelPacket_gradientError hp hL center state m r hm hr hstate
  change ‖fderiv ℝ (average f)
    (center + state.offset + epochModelStep hp (fun i => fullJet p (f i) center) M r hr state)‖ ≤ _ at hd
  nlinarith

end Weighted

end FullJet
