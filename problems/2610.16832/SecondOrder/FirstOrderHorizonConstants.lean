import SecondOrder.FirstOrderContinuationProbability

open scoped Classical

namespace SecondOrder
noncomputable section

theorem firstOrderActivationHorizon_log (D : ℝ) (n : ℕ) :
    Real.log ((n+1:ℕ)*(2*Real.exp (-D/128)))=Real.log (2*(n+1:ℕ))-D/128 := by
  have hc : (0:ℝ)<2*(n+1:ℕ) := by positivity
  rw [show (n+1:ℕ)*(2*Real.exp (-D/128))=(2*(n+1:ℕ))*Real.exp (-D/128) by ring,
    Real.log_mul hc.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem firstOrderActivationHorizon_small {D : ℝ} (hD : 0<D) (n : ℕ)
    (hsize : 256*Real.log (2*(n+1:ℕ))≤D) :
    (n+1:ℕ)*(2*Real.exp (-D/128))<1 ∧
      D/256≤Real.log (1/((n+1:ℕ)*(2*Real.exp (-D/128)))) := by
  have hl := firstOrderActivationHorizon_log D n
  constructor
  · apply (Real.log_neg_iff (by positivity)).mp
    rw [hl]
    linarith only [hD, hsize]
  · rw [one_div, Real.log_inv, hl]
    linarith only [hsize]

theorem firstOrderFarHorizon_small {D : ℝ} (n T : ℕ)
    (hsize : 128*Real.log (32*(n+1:ℕ)*(T+1:ℕ))≤D) :
    (n+1:ℕ)*((T+1:ℕ)*(2*Real.exp (-D/128)))≤1/16 := by
  let c : ℝ := 32*(n+1:ℕ)*(T+1:ℕ)
  have hc : 0<c := by dsimp [c]; positivity
  have hexp : Real.exp (-D/128)≤c⁻¹ := by
    rw [←Real.exp_log hc, ←Real.exp_neg]
    apply Real.exp_le_exp.mpr
    dsimp only [c]
    linarith only [hsize]
  have hh := mul_le_mul_of_nonneg_left hexp (le_of_lt hc)
  rw [mul_inv_cancel₀ hc.ne'] at hh
  dsimp only [c] at hh
  nlinarith only [hh]

variable {d T : ℕ} {S : Type*}

/-- Fully numeric conditions for the fixed-entry continuation's stage bound. -/
theorem firstOrderContinuation_activation_explicit (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (hd : 0<d) (A β R : ℝ) (hR : 2≤R)
    (start : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (hhorizon : 256*Real.log (2*(n+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384) :
    pmfEventProbability (firstOrderContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => decide (∃ t, 0<firstOrderBlockCompletion (finiteHistoryInitial n h).1
        (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t (finiteHistoryMapInitial Prod.snd n h))))≤1/32 := by
  have hD : (0:ℝ)<(d:ℝ) := by exact_mod_cast hd
  have hs := firstOrderActivationHorizon_small hD n hhorizon
  exact firstOrderContinuation_activation_one_thirty_second P Θ A β R hR start i cap dummy s₀ a₀ n
    (div_pos hD (by norm_num)) hs.1 hs.2 (by linarith only [hlarge, hcap])

end
end SecondOrder

