import NCConcave16991.ConditionalHaarConeMachineMeasurable
import NCConcave16991.ConeAdmissibility

/-! # Actual bounded query and arbitrary-output probes of the cone machine -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

def sourceProbe (j : Fin (M + 1)) (x : PrimalSpace (ConeProblem.primalDimension E M)) : E :=
  ConeRadial.zeta (((ConeProblem.primalCoordinates E M).symm x).fst j)

def clockProbe (j : Fin (M + 1)) (x : PrimalSpace (ConeProblem.primalDimension E M)) : E :=
  normalizedClockProbe (((ConeProblem.primalCoordinates E M).symm x).snd j)

theorem sourceProbe_continuous (j : Fin (M + 1)) : Continuous (sourceProbe E M j) :=
  ConeSmooth.zeta_contDiff.continuous.comp
    ((((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      (WithLp.fstL 2 ℝ (ConeValue.Blocks E M) (ConeValue.Blocks E M))).continuous).comp
        (ConeProblem.primalCoordinates E M).symm.continuous)

theorem clockProbe_continuous (j : Fin (M + 1)) : Continuous (clockProbe E M j) :=
  normalizedClockProbe_continuous.comp
    ((((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      (WithLp.sndL 2 ℝ (ConeValue.Blocks E M) (ConeValue.Blocks E M))).continuous).comp
        (ConeProblem.primalCoordinates E M).symm.continuous)

theorem sourceProbe_norm_le (j : Fin (M + 1)) (x : PrimalSpace (ConeProblem.primalDimension E M)) :
    ‖sourceProbe E M j x‖ ≤ 3 := ConeRadial.zeta_norm_bound _

theorem clockProbe_norm_le (j : Fin (M + 1)) (x : PrimalSpace (ConeProblem.primalDimension E M)) :
    ‖clockProbe E M j x‖ ≤ 1 := normalizedClockProbe_norm_le _

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M) Ω)

def nextQuery (seed : Ω) (hn : 0 < n) (s : State E n M R hR) : Query E n M R hR :=
  actionQuery E n M R hR hn (OracleSimulation.action (Domain E M R hR) P seed s.control)

def querySourceProbe (seed : Ω) (hn : 0 < n) (j : Fin (M + 1)) (s : State E n M R hR) : E :=
  sourceProbe E M j (nextQuery E n M R hR P seed hn s).2.1

def queryClockProbe (seed : Ω) (hn : 0 < n) (j : Fin (M + 1)) (s : State E n M R hR) : E :=
  clockProbe E M j (nextQuery E n M R hR P seed hn s).2.1

def finalSourceProbe (seed : Ω) (j : Fin (M + 1)) (s : State E n M R hR) : E :=
  (1 / 3 : ℝ) • sourceProbe E M j (output E n M R hR P seed s)

theorem querySourceProbe_norm_le (seed : Ω) (hn : 0 < n) (j : Fin (M + 1)) (s : State E n M R hR) :
    ‖querySourceProbe E n M R hR P seed hn j s‖ ≤ 3 := sourceProbe_norm_le E M j _

theorem queryClockProbe_norm_le (seed : Ω) (hn : 0 < n) (j : Fin (M + 1)) (s : State E n M R hR) :
    ‖queryClockProbe E n M R hR P seed hn j s‖ ≤ 1 := clockProbe_norm_le E M j _

theorem finalSourceProbe_norm_le (seed : Ω) (j : Fin (M + 1)) (s : State E n M R hR) :
    ‖finalSourceProbe E n M R hR P seed j s‖ ≤ 1 := by
  unfold finalSourceProbe
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  nlinarith [sourceProbe_norm_le E M j (output E n M R hR P seed s)]

section Measurable

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem nextQuery_measurable (hn : 0 < n) :
    Measurable (fun p : Ω × State E n M R hR ↦ nextQuery E n M R hR P p.1 hn p.2) :=
  (actionQuery_measurable E n M R hR hn).comp
    ((OracleSimulation.action_measurable (Domain E M R hR) P).comp
      (measurable_fst.prodMk ((control_measurable E n M R hR).comp measurable_snd)))

theorem querySourceProbe_measurable (hn : 0 < n) (j : Fin (M + 1)) :
    Measurable (fun p : Ω × State E n M R hR ↦ querySourceProbe E n M R hR P p.1 hn j p.2) :=
  (sourceProbe_continuous E M j).measurable.comp
    ((measurable_fst.comp measurable_snd).comp (nextQuery_measurable E n M R hR P hn))

theorem queryClockProbe_measurable (hn : 0 < n) (j : Fin (M + 1)) :
    Measurable (fun p : Ω × State E n M R hR ↦ queryClockProbe E n M R hR P p.1 hn j p.2) :=
  (clockProbe_continuous E M j).measurable.comp
    ((measurable_fst.comp measurable_snd).comp (nextQuery_measurable E n M R hR P hn))

theorem finalSourceProbe_measurable (j : Fin (M + 1)) :
    Measurable (fun p : Ω × State E n M R hR ↦ finalSourceProbe E n M R hR P p.1 j p.2) :=
  measurable_const.smul ((sourceProbe_continuous E M j).measurable.comp
    (output_measurable E n M R hR P))

end Measurable

end

end NCConcave16991.Haar.ConeMachine
