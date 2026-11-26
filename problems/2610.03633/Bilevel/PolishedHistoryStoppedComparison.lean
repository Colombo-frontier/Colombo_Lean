import Bilevel.PolishedHistoryStoppedLimits

/-! Actual stopping cost and loss are determined by finite-time state laws
on absorbing paths. Finite expected cost is used only to discard the
nonterminating stopped-output fallback. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open HistoryProgram
set_option autoImplicit false
variable {S Q O Y H : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace H]
variable (A : BorelAdaptive.Program S Q O Y)

def liveIndicator (z : S × H) : ℝ≥0∞ := if A.halt z.1=true then 0 else 1

theorem liveIndicator_measurable : Measurable (liveIndicator A (H:=H)) :=
  measurable_const.ite ((A.halt_measurable.comp measurable_fst)
    (measurableSet_singleton true)) measurable_const

omit [MeasurableSpace H] in
theorem queryCount_cast_succ (n : ℕ) (w : HistoryProgram.Path S H) :
    (queryCount A (n+1) w:ℝ≥0∞)=(queryCount A n w:ℝ≥0∞)+liveIndicator A (w n) := by
  by_cases hh : A.halt (w n).1=true <;> simp [queryCount,liveIndicator,hh]

theorem queryCount_cast_measurable (n : ℕ) :
    Measurable (fun w : HistoryProgram.Path S H => (queryCount A n w:ℝ≥0∞)) :=
  (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (queryCount_measurable A n)

variable (μ ν : Measure (HistoryProgram.Path S H))
  (he : ∀ n,μ.map (fun w => w n)=ν.map (fun w => w n))

include he in
theorem queryCount_integral_eq (n : ℕ) :
    (∫⁻ w,(queryCount A n w:ℝ≥0∞) ∂μ)=∫⁻ w,(queryCount A n w:ℝ≥0∞) ∂ν := by
  induction n with
  | zero => simp [queryCount]
  | succ n ih =>
      have hl : (∫⁻ w,liveIndicator A (w n) ∂μ)=∫⁻ w,liveIndicator A (w n) ∂ν := by
        rw [← lintegral_map (liveIndicator_measurable A) (measurable_pi_apply n),he n,
          lintegral_map (liveIndicator_measurable A) (measurable_pi_apply n)]
      simp_rw [queryCount_cast_succ]
      rw [lintegral_add_left (queryCount_cast_measurable A n),
        lintegral_add_left (queryCount_cast_measurable A n),ih,hl]

include he in
theorem totalCalls_integral_eq
    (hμ : ∀ᵐ w ∂μ,HaltSticky A w) (hν : ∀ᵐ w ∂ν,HaltSticky A w) :
    (∫⁻ w,HistoryProgram.totalCalls A w ∂μ)=
      ∫⁻ w,HistoryProgram.totalCalls A w ∂ν := by
  have hm : Monotone (fun n => fun w : HistoryProgram.Path S H => (queryCount A n w:ℝ≥0∞)) := by
    intro n m hnm w
    exact Nat.cast_le.mpr (queryCount_mono A w hnm)
  calc
    _ = ∫⁻ w,⨆ n : ℕ,(queryCount A n w:ℝ≥0∞) ∂μ :=
      lintegral_congr_ae (hμ.mono (fun w hw => totalCalls_eq_iSup_queryCount A w hw))
    _ = ⨆ n : ℕ,∫⁻ w,(queryCount A n w:ℝ≥0∞) ∂μ :=
      lintegral_iSup (queryCount_cast_measurable A) hm
    _ = ⨆ n : ℕ,∫⁻ w,(queryCount A n w:ℝ≥0∞) ∂ν := by
      congr 1
      funext n
      exact queryCount_integral_eq A μ ν he n
    _ = ∫⁻ w,⨆ n : ℕ,(queryCount A n w:ℝ≥0∞) ∂ν :=
      (lintegral_iSup (queryCount_cast_measurable A) hm).symm
    _ = ∫⁻ w,HistoryProgram.totalCalls A w ∂ν :=
      lintegral_congr_ae (hν.mono (fun w hw => (totalCalls_eq_iSup_queryCount A w hw).symm))

theorem stoppedValue_integral_eq_iSup (v : S → ℝ) (hv : Measurable v)
    (hμ : ∀ᵐ w ∂μ,∀ n,pathStepGood A v n w)
    (ht : ∀ᵐ w ∂μ,HistoryProgram.Terminated A w) :
    (∫⁻ w,ENNReal.ofReal (v (w (HistoryProgram.stopTime A w)).1) ∂μ)=
      ⨆ n : ℕ,∫⁻ w,revealedLoss A v n w ∂μ := by
  calc
    _ = ∫⁻ w,⨆ n : ℕ,revealedLoss A v n w ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hμ,ht] with w hw hterm
      exact (iSup_revealedLoss A v w hw hterm).symm
    _ = _ := lintegral_iSup' (fun n => (revealedLoss_measurable A v hv n).aemeasurable)
      (hμ.mono (fun w hw => revealedLoss_mono A v w hw))

include he in
theorem stoppedValue_integral_eq (v : S → ℝ) (hv : Measurable v)
    (hμ : ∀ᵐ w ∂μ,∀ n,pathStepGood A v n w)
    (hν : ∀ᵐ w ∂ν,∀ n,pathStepGood A v n w)
    (hc : (∫⁻ w,HistoryProgram.totalCalls A w ∂μ)≠⊤) :
    (∫⁻ w,ENNReal.ofReal (v (w (HistoryProgram.stopTime A w)).1) ∂μ)=
      ∫⁻ w,ENNReal.ofReal (v (w (HistoryProgram.stopTime A w)).1) ∂ν := by
  have hsμ : ∀ᵐ w ∂μ,HaltSticky A w := hμ.mono (fun _ hw n hn => (hw n hn).1)
  have hsν : ∀ᵐ w ∂ν,HaltSticky A w := hν.mono (fun _ hw n hn => (hw n hn).1)
  have hcν : (∫⁻ w,HistoryProgram.totalCalls A w ∂ν)≠⊤ := by
    rw [← totalCalls_integral_eq A μ ν he hsμ hsν]
    exact hc
  rw [stoppedValue_integral_eq_iSup A μ v hv hμ
      (HistoryProgram.ae_terminated_of_cost_finite A μ hc),
    stoppedValue_integral_eq_iSup A ν v hv hν
      (HistoryProgram.ae_terminated_of_cost_finite A ν hcν)]
  have hg : Measurable (fun z : S × H =>
      if A.halt z.1=true then ENNReal.ofReal (v z.1) else 0) :=
    ((hv.comp measurable_fst).ennreal_ofReal).ite
      ((A.halt_measurable.comp measurable_fst) (measurableSet_singleton true)) measurable_const
  congr 1
  funext n
  change (∫⁻ w,(if A.halt (w n).1=true then ENNReal.ofReal (v (w n).1) else 0) ∂μ)=_
  rw [← lintegral_map hg (measurable_pi_apply n),he n,
    lintegral_map hg (measurable_pi_apply n)]
  rfl

end Bilevel.PolishedHistory
