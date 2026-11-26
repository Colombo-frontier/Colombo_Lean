import Bilevel.PolishedHistoryStationary
import Bilevel.IndependentStreamTail
import Bilevel.BorelAdaptiveRunShift

/-! Finite-time operational equivalence of the seed execution and the
history-kernel execution. Every absorbing halt and original call is retained.
No equality of stopped experiments is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open HistoryProgram
set_option autoImplicit false
variable {S Q O Y C : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace C]
variable (ν : Measure C) [IsProbabilityMeasure ν]
  (response : Q → C → O) (hr : Measurable (Function.uncurry response))

def freshOracle : HistoryProgram.Oracle Q O Unit where
  law := Stateful.KernelMap.dependent (Kernel.const (Q × Unit) ν)
    (fun z => response z.1.1 z.2)
  markov := Stateful.KernelMap.dependent_markov _ _
    (hr.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  update := fun _ => ()
  update_measurable := measurable_const

theorem freshOracle_law (q : Q) (h : Unit) :
    (freshOracle ν response hr).law (q,h)=ν.map (response q) :=
  Stateful.KernelMap.dependent_apply _ _
    (hr.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) (q,h)

variable (A : BorelAdaptive.Program S Q O Y)

def freshState (s : S) (n : ℕ) (draws : IndependentStream.Stream C) : S × Unit :=
  (BorelAdaptive.run A (fun _ : Unit => response) () draws s n,())

include hr in
theorem freshState_measurable (s : S) (n : ℕ) :
    Measurable (freshState response A s n) := by
  have hrep : Measurable (fun z : Unit × (Q × C) => response z.2.1 z.2.2) :=
    hr.comp measurable_snd
  exact ((BorelAdaptive.run_measurable A _ hrep n).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))).prodMk measurable_const

theorem freshOracle_step (s : S) :
    HistoryProgram.step A (freshOracle ν response hr) (s,())=
      ν.map (fun c => (BorelAdaptive.step A (fun _ : Unit => response) () c s,())) := by
  cases hh : A.halt s with
  | false =>
      rw [HistoryProgram.step_live _ _ _ hh,freshOracle_law]
      have hres : Measurable (response (A.query s)) :=
        hr.comp (measurable_const.prodMk measurable_id)
      have hadv : Measurable (fun o : O =>
          HistoryProgram.advance A (freshOracle ν response hr) ((s,()),o)) :=
        (HistoryProgram.advance_measurable A (freshOracle ν response hr)).comp
          (measurable_const.prodMk measurable_id)
      change (ν.map (response (A.query s))).map (fun o =>
        HistoryProgram.advance A (freshOracle ν response hr) ((s,()),o)) = _
      rw [Measure.map_map hadv hres]
      congr 1
      funext c
      simp only [BorelAdaptive.step,hh,Bool.false_eq_true,if_false]
      rfl
  | true =>
      rw [HistoryProgram.step_halted _ _ _ hh]
      simp only [BorelAdaptive.step,hh,if_true]
      rw [Measure.map_const,measure_univ,one_smul]

include hr in
theorem freshState_joint_measurable (n : ℕ) :
    Measurable (fun z : S × IndependentStream.Stream C => freshState response A z.1 n z.2) := by
  have hrep : Measurable (fun z : Unit × (Q × C) => response z.2.1 z.2.2) :=
    hr.comp measurable_snd
  exact ((BorelAdaptive.run_measurable A _ hrep n).comp
    (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).prodMk measurable_const

/-- Equality at every fixed horizon is derived from actual fresh draws and
kernel composition, including halted configurations. -/
theorem fresh_run_law (n : ℕ) (s : S) :
    (IndependentStream.law ν).map (freshState response A s n)=
      HistoryProgram.run A (freshOracle ν response hr) n (s,()) := by
  induction n generalizing s with
  | zero =>
      change (IndependentStream.law ν).map (fun _ => (s,()))=Kernel.id (s,())
      rw [Measure.map_const,measure_univ,one_smul,Kernel.id_apply]
  | succ n ih =>
      let R := freshOracle ν response hr
      have hfirst : HistoryProgram.run A R (n+1)=
          HistoryProgram.run A R n ∘ₖ HistoryProgram.step A R := by
        rw [Nat.add_comm n 1,HistoryProgram.run_add]
        simp only [HistoryProgram.run_succ,HistoryProgram.run_zero,Kernel.comp_id]
      have hrep : Measurable (fun z : Unit × (Q × C) => response z.2.1 z.2.2) :=
        hr.comp measurable_snd
      have hstep : Measurable (fun c => BorelAdaptive.step A
          (fun _ : Unit => response) () c s) :=
        (BorelAdaptive.step_measurable A (fun _ : Unit => response) hrep).comp
          (show Measurable (fun c : C => (((),c),s)) from
            (measurable_const.prodMk measurable_id).prodMk measurable_const)
      apply Measure.ext_of_lintegral
      intro f hf
      rw [lintegral_map hf (freshState_measurable response hr A s (n+1)),hfirst,
        Kernel.lintegral_comp _ _ _ hf,freshOracle_step ν response hr A s,
        lintegral_map hf.lintegral_kernel (hstep.prodMk measurable_const)]
      let F : C × IndependentStream.Stream C → ℝ≥0∞ :=
        fun z => f (freshState response A (BorelAdaptive.step A
          (fun _ : Unit => response) () z.1 s) n z.2)
      have hF : Measurable F := hf.comp ((freshState_joint_measurable response hr A n).comp
        ((hstep.comp measurable_fst).prodMk measurable_snd))
      calc
        _ = ∫⁻ draws,F (IndependentStream.split draws) ∂IndependentStream.law ν := by
          apply lintegral_congr
          intro draws
          change f (BorelAdaptive.run A _ () draws s (n+1),())=_
          rw [BorelAdaptive.run_succ_first]
          rfl
        _ = ∫⁻ z,F z ∂ν.prod (IndependentStream.law ν) :=
          (IndependentStream.split_preserves ν).lintegral_comp hF
        _ = ∫⁻ c,∫⁻ draws,F (c,draws) ∂IndependentStream.law ν ∂ν :=
          lintegral_prod _ hF.aemeasurable
        _ = _ := by
          apply lintegral_congr
          intro c
          rw [← ih (BorelAdaptive.step A (fun _ : Unit => response) () c s),
            lintegral_map hf (freshState_measurable response hr A _ n)]

/-- Arbitrary independent private initialization is integrated in exactly
the same way in the two finite-horizon executions. -/
theorem fresh_private_run_law {Private : Type*} [MeasurableSpace Private]
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (start : Private → S) (hs : Measurable start) (n : ℕ) :
    (ρ.prod (IndependentStream.law ν)).map
        (fun z => freshState response A (start z.1) n z.2)=
      HistoryProgram.runLaw A (freshOracle ν response hr) ρ start () n := by
  have hm : Measurable (fun z : Private × IndependentStream.Stream C =>
      freshState response A (start z.1) n z.2) :=
    (freshState_joint_measurable response hr A n).comp
      ((hs.comp measurable_fst).prodMk measurable_snd)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm]
  rw [lintegral_prod (fun z : Private × IndependentStream.Stream C =>
      f (freshState response A (start z.1) n z.2)) (hf.comp hm).aemeasurable,
    HistoryProgram.runLaw,Measure.comp_eq_comp_const_apply,
    Kernel.lintegral_comp _ _ _ hf,Kernel.const_apply,
    lintegral_map hf.lintegral_kernel (hs.prodMk measurable_const)]
  apply lintegral_congr
  intro r
  rw [← fresh_run_law ν response hr A n (start r),
    lintegral_map hf (freshState_measurable response hr A (start r) n)]

end Bilevel.PolishedHistory
