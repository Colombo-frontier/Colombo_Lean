import LeanArticleAudit.Pilot.UpperBorelBridge
import LeanArticleAudit.Pilot.UpperBaseStrong
import LeanArticleAudit.Pilot.UpperBorelPrimitives

/-!
# Borel replay rules for the concrete upper programs

This file proves measurability for the complete counterfactual transcript
tree of the concrete halving, correction, and base-trial programs.  These are
operational facts about the programs, not regularity assumptions on an
unknown oracle.
-/

open Set MeasureTheory Topology
open scoped RealInnerProductSpace BigOperators

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Reparameterize a jointly Borel replay rule by a measurable parameter
map. -/
theorem ExactJetProgram.IsJointlyBorelAction.compParameter
    {X Answer Output P Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Answer]
    [MeasurableSpace P] [MeasurableSpace Q]
    {finish : Option Output → X}
    {program : P → ExactJetProgram X Answer Output}
    (h : ExactJetProgram.IsJointlyBorelAction finish program)
    (g : Q → P) (hg : Measurable g) :
    ExactJetProgram.IsJointlyBorelAction finish (fun q => program (g q)) := by
  intro n
  exact (h n).comp (hg.comp measurable_fst |>.prodMk measurable_snd)

section Halving

variable (data : VIPublicData E) (mu : ℝ)

abbrev HalvingBorelState := data.X × E × ℝ

def halvingTerminal (s : HalvingBorelState data) : HalvingOutput data := {
  point := if s.2.2 = 0 then s.1.1 else (1 / s.2.2) • s.2.1
  early := false
  normal := 0
  value := 0 }

theorem measurable_halvingTerminal :
    Measurable (halvingTerminal data) := by
  apply measurable_halvingOutput_mk data
  · exact Measurable.ite
      (measurableSet_singleton 0 |>.preimage (measurable_snd.comp measurable_snd))
      (measurable_subtype_coe.comp measurable_fst)
      ((measurable_const.div (measurable_snd.comp measurable_snd)).smul
        (measurable_fst.comp measurable_snd))
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const

def halvingEarly (a : HalvingBorelState data × SymmetricExactJet E data.p) :
    HalvingOutput data :=
  let yn := knownModelStep data a.1.1 a.2
  { point := yn.1.1, early := true, normal := yn.2,
    value := symmetricJetValue data a.2 }

theorem measurable_halvingEarly :
    Measurable (halvingEarly data) := by
  let hm : Measurable (fun a : HalvingBorelState data × SymmetricExactJet E data.p =>
      knownModelStep data a.1.1 a.2) :=
    (measurable_knownModelStep_componentwise data).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  apply measurable_halvingOutput_mk data
  · exact measurable_subtype_coe.comp (measurable_fst.comp hm)
  · exact measurable_const
  · exact measurable_snd.comp hm
  · exact (measurable_symmetricJetValue_componentwise data).comp measurable_snd

def halvingNextState
    (a : (HalvingBorelState data × SymmetricExactJet E data.p) ×
      SymmetricExactJet E data.p) : HalvingBorelState data :=
  let s := a.1.1
  let yn := knownModelStep data s.1 a.1.2
  let lambda := 1 / ((tensorBetaCoefficient data.p * data.Lp) *
    ‖yn.1.1 - s.1.1‖ ^ (data.p - 1))
  let xp := compactProjection data
    (s.1.1 - lambda • symmetricJetValue data a.2)
  (xp, s.2.1 + lambda • yn.1.1, s.2.2 + lambda)

theorem measurable_halvingNextState :
    Measurable (halvingNextState data) := by
  let hmodel : Measurable (fun a :
      (HalvingBorelState data × SymmetricExactJet E data.p) ×
        SymmetricExactJet E data.p =>
      knownModelStep data a.1.1.1 a.1.2) :=
    (measurable_knownModelStep_componentwise data).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst))
  let hlambda : Measurable (fun a :
      (HalvingBorelState data × SymmetricExactJet E data.p) ×
        SymmetricExactJet E data.p =>
      1 / ((tensorBetaCoefficient data.p * data.Lp) *
        ‖(knownModelStep data a.1.1.1 a.1.2).1.1 - a.1.1.1.1‖ ^
          (data.p - 1))) := by
    fun_prop
  let harg : Measurable (fun a :
      (HalvingBorelState data × SymmetricExactJet E data.p) ×
        SymmetricExactJet E data.p =>
      a.1.1.1.1 -
        (1 / ((tensorBetaCoefficient data.p * data.Lp) *
          ‖(knownModelStep data a.1.1.1 a.1.2).1.1 - a.1.1.1.1‖ ^
            (data.p - 1))) • symmetricJetValue data a.2) := by
    exact (measurable_subtype_coe.comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst))).sub
      (hlambda.smul
        ((measurable_symmetricJetValue_componentwise data).comp measurable_snd))
  let hxp : Measurable (fun a :
      (HalvingBorelState data × SymmetricExactJet E data.p) ×
        SymmetricExactJet E data.p =>
      compactProjection data (a.1.1.1.1 -
          (1 / ((tensorBetaCoefficient data.p * data.Lp) *
            ‖(knownModelStep data a.1.1.1 a.1.2).1.1 - a.1.1.1.1‖ ^
              (data.p - 1))) • symmetricJetValue data a.2)) :=
    (continuous_compactProjection data).measurable.comp harg
  exact hxp.prodMk
    ((measurable_fst.comp (measurable_snd.comp
      (measurable_fst.comp measurable_fst))).add
      (hlambda.smul (measurable_subtype_coe.comp (measurable_fst.comp hmodel))) |>.prodMk
        ((measurable_snd.comp (measurable_snd.comp
          (measurable_fst.comp measurable_fst))).add hlambda))

/-- The complete halving loop, jointly in its public/internal state, has a
Borel raw replay outcome on every transcript length. -/
theorem halvingProgramAux_isJointlyBorelOutcome (remaining : ℕ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (fun s : HalvingBorelState data =>
        halvingProgramAux data mu remaining s.1 s.2.1 s.2.2) := by
  induction remaining with
  | zero =>
      simpa [halvingProgramAux, halvingTerminal] using
        ExactJetProgram.isJointlyBorelOutcome_halt
          (X := data.X) (Answer := SymmetricExactJet E data.p)
          (fun s : HalvingBorelState data => some (halvingTerminal data s))
          (measurable_some.comp (measurable_halvingTerminal data))
  | succ remaining ih =>
      let A := HalvingBorelState data × SymmetricExactJet E data.p
      let model : A → data.X × E := fun a =>
        knownModelStep data a.1.1 a.2
      have hmodel : Measurable model := by
        exact (measurable_knownModelStep_componentwise data).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      let earlySet : Set A := {a | (model a).1 = a.1.1}
      have hearlySet : MeasurableSet earlySet := by
        exact measurableSet_eq_fun (measurable_fst.comp hmodel)
          (measurable_fst.comp measurable_fst)
      let earlyProgram : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (HalvingOutput data) := fun a =>
        .halt (some (halvingEarly data a))
      have hearlyProgram :
          ExactJetProgram.IsJointlyBorelOutcome earlyProgram := by
        apply ExactJetProgram.isJointlyBorelOutcome_halt
        exact measurable_some.comp (measurable_halvingEarly data)
      let lateTail :
          (A × SymmetricExactJet E data.p) → ExactJetProgram data.X
            (SymmetricExactJet E data.p) (HalvingOutput data) := fun a =>
        halvingProgramAux data mu remaining
          (halvingNextState data a).1
          (halvingNextState data a).2.1
          (halvingNextState data a).2.2
      have hlateTail : ExactJetProgram.IsJointlyBorelOutcome lateTail := by
        exact ih.compParameter (halvingNextState data)
          (measurable_halvingNextState data)
      let lateProgram : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (HalvingOutput data) := fun a =>
        .query (model a).1 (fun jety => lateTail (a, jety))
      have hlateProgram :
          ExactJetProgram.IsJointlyBorelOutcome lateProgram := by
        exact ExactJetProgram.isJointlyBorelOutcome_query
          (fun a : A => (model a).1) lateTail
          (measurable_fst.comp hmodel) hlateTail
      let afterFirst : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (HalvingOutput data) :=
        ExactJetProgram.actionPiecewise earlySet earlyProgram lateProgram
      have hafterFirst :
          ExactJetProgram.IsJointlyBorelOutcome afterFirst :=
        ExactJetProgram.isJointlyBorelOutcome_piecewise earlySet hearlySet
          earlyProgram lateProgram hearlyProgram hlateProgram
      have hwhole := ExactJetProgram.isJointlyBorelOutcome_query
        (Output := HalvingOutput data)
        (fun s : HalvingBorelState data => s.1)
        (fun a : HalvingBorelState data × SymmetricExactJet E data.p => afterFirst a)
        measurable_fst hafterFirst
      convert hwhole using 1
      funext s
      simp only [halvingProgramAux]
      congr 1
      funext jetx
      by_cases hxy : (knownModelStep data s.1 jetx).1.1 = s.1.1
      · have hxy' : (knownModelStep data s.1 jetx).1 = s.1 := Subtype.ext hxy
        simp [afterFirst, ExactJetProgram.actionPiecewise, earlySet, model,
          earlyProgram, halvingEarly, hxy, hxy']
      · have hxy' : ¬(knownModelStep data s.1 jetx).1 = s.1 :=
          fun h => hxy (congrArg Subtype.val h)
        simp [afterFirst, ExactJetProgram.actionPiecewise, earlySet, model,
          lateProgram, lateTail, halvingNextState, compactProjection, hxy, hxy']

theorem halvingProgram_isBorelOutcome (center : data.X) (r : ℝ) :
    ExactJetProgram.IsBorelOutcome (halvingProgram data center mu r) := by
  exact (halvingProgramAux_isJointlyBorelOutcome data mu
    (halvingIterationCount data.p data.Lp r mu)).fixed (center, 0, 0)

end Halving

section Correction

variable (data : VIPublicData E) (fallback : data.X)

/-- The final two-query correction program has a Borel action on every full
or counterfactual transcript. -/
theorem correctionProgram_isBorelAction (center : data.X) (delta : ℝ) :
    ExactJetProgram.IsBorelAction (certifiedCallOutput data fallback)
      (correctionProgram data center delta) := by
  classical
  intro n
  cases n with
  | zero =>
      simpa [correctionProgram, ExactJetProgram.replayAction,
        ExactJetProgram.residualAfterHistory,
        ExactJetProgram.residualAfterAnswers] using
        (measurable_const : Measurable (fun _ : Fin 0 →
          data.X × SymmetricExactJet E data.p => Sum.inr center))
  | succ n =>
      cases n with
      | zero =>
          have hquery : Measurable (fun history : Fin 1 →
              data.X × SymmetricExactJet E data.p =>
              (Sum.inr (knownModelStep data center (history 0).2).1 :
                Sum data.X data.X)) := by
            apply measurable_inr.comp
            exact measurable_fst.comp
              ((measurable_knownModelStep_componentwise data).comp
                (measurable_const.prodMk (measurable_snd.comp
                  (measurable_pi_apply
                    (X := fun _ : Fin 1 =>
                      data.X × SymmetricExactJet E data.p) (0 : Fin 1)))))
          simpa [correctionProgram, ExactJetProgram.replayAction,
            ExactJetProgram.residualAfterHistory, List.ofFn_succ,
            ExactJetProgram.residualAfterAnswers] using hquery
      | succ n =>
          let point : (Fin (n + 2) → data.X × SymmetricExactJet E data.p) → data.X :=
            fun history => (knownModelStep data center (history 0).2).1
          let normal : (Fin (n + 2) → data.X × SymmetricExactJet E data.p) → E :=
            fun history => (knownModelStep data center (history 0).2).2
          let value : (Fin (n + 2) → data.X × SymmetricExactJet E data.p) → E :=
            fun history => symmetricJetValue data (history 1).2
          have hp : Measurable point := by
            exact measurable_fst.comp
              ((measurable_knownModelStep_componentwise data).comp
                (measurable_const.prodMk (measurable_snd.comp
                  (measurable_pi_apply
                    (X := fun _ : Fin (n + 2) =>
                      data.X × SymmetricExactJet E data.p)
                    (0 : Fin (n + 2))))))
          have hn : Measurable normal := by
            exact measurable_snd.comp
              ((measurable_knownModelStep_componentwise data).comp
                (measurable_const.prodMk (measurable_snd.comp
                  (measurable_pi_apply
                    (X := fun _ : Fin (n + 2) =>
                      data.X × SymmetricExactJet E data.p)
                    (0 : Fin (n + 2))))))
          have hv : Measurable value := by
            exact (measurable_symmetricJetValue_componentwise data).comp
              (measurable_snd.comp
                (measurable_pi_apply
                  (X := fun _ : Fin (n + 2) =>
                    data.X × SymmetricExactJet E data.p)
                  (1 : Fin (n + 2))))
          have hnormal : MeasurableSet {history | normal history ∈
              normalCone data.X (point history).1} := by
            exact (isClosed_upperNormalConeGraph data.X).measurableSet.preimage
              ((measurable_subtype_coe.comp hp).prodMk hn)
          have hres : MeasurableSet {history | ‖value history + normal history‖ ≤ delta} := by
            exact measurableSet_Iic.preimage ((hv.add hn).norm)
          let good := {history | normal history ∈ normalCone data.X (point history).1} ∩
            {history | ‖value history + normal history‖ ≤ delta}
          have hgood : MeasurableSet good := hnormal.inter hres
          have hout : Measurable (fun history : Fin (n + 2) →
              data.X × SymmetricExactJet E data.p =>
              if history ∈ good then
                (Sum.inl (point history) : Sum data.X data.X)
              else (Sum.inl fallback : Sum data.X data.X)) := by
            exact Measurable.ite hgood (measurable_inl.comp hp) measurable_const
          convert hout using 1
          funext history
          by_cases hn' : (knownModelStep data center (history 0).2).2 ∈
              normalCone data.X (knownModelStep data center (history 0).2).1.1
          · by_cases hr' : ‖symmetricJetValue data (history 1).2 +
                (knownModelStep data center (history 0).2).2‖ ≤ delta
            · simp [correctionProgram, ExactJetProgram.replayAction,
                ExactJetProgram.residualAfterHistory, List.ofFn_succ,
                ExactJetProgram.residualAfterAnswers, certifiedCallOutput,
                point, normal, value, good, hn', hr']
            · simp [correctionProgram, ExactJetProgram.replayAction,
                ExactJetProgram.residualAfterHistory, List.ofFn_succ,
                ExactJetProgram.residualAfterAnswers, certifiedCallOutput,
                point, normal, value, good, hn', hr']
          · simp [correctionProgram, ExactJetProgram.replayAction,
              ExactJetProgram.residualAfterHistory, List.ofFn_succ,
              ExactJetProgram.residualAfterAnswers, certifiedCallOutput,
              point, normal, value, good, hn']

end Correction

end

end LeanArticleAudit.Pilot
