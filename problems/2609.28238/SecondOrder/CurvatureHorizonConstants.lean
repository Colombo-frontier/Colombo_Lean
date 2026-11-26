import SecondOrder.CurvatureContinuationProbability

open scoped Classical

namespace SecondOrder
noncomputable section

theorem curvatureActivationHorizon_log (D : ℝ) (n : ℕ) :
    Real.log ((n+1:ℕ)*(4*Real.exp (-D/512)))=Real.log (4*(n+1:ℕ))-D/512 := by
  have hc : (0:ℝ)<4*(n+1:ℕ) := by positivity
  rw [show (n+1:ℕ)*(4*Real.exp (-D/512))=(4*(n+1:ℕ))*Real.exp (-D/512) by ring,
    Real.log_mul hc.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem curvatureActivationHorizon_small {D : ℝ} (hD : 0<D) (n : ℕ)
    (hsize : 1024*Real.log (4*(n+1:ℕ))≤D) :
    (n+1:ℕ)*(4*Real.exp (-D/512))<1 ∧
      D/1024≤Real.log (1/((n+1:ℕ)*(4*Real.exp (-D/512)))) := by
  have hl := curvatureActivationHorizon_log D n
  constructor
  · apply (Real.log_neg_iff (by positivity)).mp
    rw [hl]
    linarith only [hD, hsize]
  · rw [one_div, Real.log_inv, hl]
    linarith only [hsize]

theorem curvatureFarHorizon_small {D : ℝ} (n T : ℕ)
    (hsize : 512*Real.log (64*(n+1:ℕ)*(T+1:ℕ))≤D) :
    (n+1:ℕ)*((T+1:ℕ)*(4*Real.exp (-D/512)))≤1/16 := by
  let c : ℝ := 64*(n+1:ℕ)*(T+1:ℕ)
  have hc : 0<c := by dsimp [c]; positivity
  have hexp : Real.exp (-D/512)≤c⁻¹ := by
    rw [←Real.exp_log hc, ←Real.exp_neg]
    apply Real.exp_le_exp.mpr
    dsimp only [c]
    linarith only [hsize]
  have hh := mul_le_mul_of_nonneg_left hexp (le_of_lt hc)
  rw [mul_inv_cancel₀ hc.ne'] at hh
  dsimp only [c] at hh
  nlinarith only [hh]

variable {m T : ℕ} {S : Type*}

/-- Fully numeric conditions for the fixed-entry continuation's stage bound. -/
theorem curvatureContinuation_activation_explicit (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m) (A β R : ℝ) (hR : 2≤R)
    (start : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (s₀ : S) (a₀ : CurvatureCoefficients m T R) (n : ℕ)
    (hhorizon : 1024*Real.log (4*(n+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536) :
    pmfEventProbability (curvatureContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => decide (∃ t, 0<periodicCompletion (finiteHistoryInitial n h).1
        (curvatureContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t (finiteHistoryMapInitial Prod.snd n h))))≤1/32 := by
  have hD : (0:ℝ)<((2*m:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos (by omega) hm
  have hs := curvatureActivationHorizon_small hD n hhorizon
  exact curvatureContinuation_activation_one_thirty_second P Θ A β R hR start i cap dummy s₀ a₀ n
    (div_pos hD (by norm_num)) hs.1 hs.2 (by linarith only [hlarge, hcap])

end
end SecondOrder
