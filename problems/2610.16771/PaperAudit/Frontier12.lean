import Mathlib
import PaperAudit.Frontier11

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: NaturalFiniteListMeasurable.lean

open MeasureTheory
namespace FangqingNaturalFiniteList
noncomputable section
variable {α X : Type*} [Inhabited α]

def code (l : List α) : ℕ × (ℕ → α) := (l.length,fun n => l.getD n default)

theorem code_injective : Function.Injective (code (α:=α)) := by
  intro l r h
  apply List.ext_getElem (congrArg Prod.fst h)
  intro i hi hj
  have hv := congrArg (fun z : ℕ × (ℕ → α) => z.2 i) h
  simpa only [code,← List.getElem_eq_getD (h:=hi) default,← List.getElem_eq_getD (h:=hj) default] using hv

variable [MeasurableSpace α]
instance finiteListMeasurableSpace : MeasurableSpace (List α) := MeasurableSpace.comap code inferInstance

theorem length_measurable : Measurable (List.length (α:=α)) :=
  measurable_fst.comp (Measurable.of_comap_le (f:=code) le_rfl)

theorem getD_measurable (n : ℕ) : Measurable (fun l : List α => l.getD n default) :=
  (measurable_pi_apply n).comp (measurable_snd.comp (Measurable.of_comap_le (f:=code) le_rfl))

theorem cons_measurable : Measurable (fun z : α × List α => z.1::z.2) := by
  apply measurable_comap_iff.mpr
  have hl : Measurable (fun z : α × List α => z.2.length+1) :=
    (length_measurable.comp measurable_snd).add_const 1
  refine hl.prodMk (measurable_pi_lambda _ fun n => ?_)
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (getD_measurable n).comp measurable_snd

end
end FangqingNaturalFiniteList
end

section
-- Source component: AdmissibleMainDataSpaces.lean

open MeasureTheory
namespace FangqingAdmissibleMainData
open OriginalSaddleImplicit OriginalAdmissibleMainReplay
noncomputable section
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace (Joint E F)]
  [MeasurableSpace (E →L[ℝ] E)]

abbrev Move (E F : Type*) := OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.Move E F
instance moveInhabited : Inhabited (Move E F) := ⟨⟨0,0,0,0⟩⟩

def moveCode (m : Move E F) : E × (E × (F × ℝ)) := (m.previous,(m.next,(m.warm,m.radius)))
instance moveMeasurableSpace : MeasurableSpace (Move E F) := MeasurableSpace.comap moveCode inferInstance

def moveEquiv : Move E F ≃ᵐ E × (E × (F × ℝ)) where
  toFun := moveCode
  invFun := fun p => ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rcases p with ⟨a,b,c,d⟩; rfl
  measurable_toFun := comap_measurable moveCode
  measurable_invFun := measurable_comap_iff.mpr measurable_id

abbrev GDResult (E F : Type*) := OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.Result E F

def gdCode (r : GDResult E F) : E × (Joint E F × (Bool × List (Move E F))) :=
  (r.point,(r.saddle,(r.success,r.moves)))
instance gdMeasurableSpace : MeasurableSpace (GDResult E F) := MeasurableSpace.comap gdCode inferInstance

def gdEquiv : GDResult E F ≃ᵐ E × (Joint E F × (Bool × List (Move E F))) where
  toFun := gdCode
  invFun := fun p => ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rcases p with ⟨a,b,c,d⟩; rfl
  measurable_toFun := comap_measurable gdCode
  measurable_invFun := measurable_comap_iff.mpr measurable_id

abbrev CubicResult (E F : Type*) := OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.Result E F

def cubicCode (r : CubicResult E F) : E × (Joint E F × (Bool × (ℕ × List (Move E F)))) :=
  (r.point,(r.saddle,(r.success,(r.charged,r.moves))))
instance cubicMeasurableSpace : MeasurableSpace (CubicResult E F) := MeasurableSpace.comap cubicCode inferInstance

def cubicEquiv : CubicResult E F ≃ᵐ E × (Joint E F × (Bool × (ℕ × List (Move E F)))) where
  toFun := cubicCode
  invFun := fun p => ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rcases p with ⟨a,b,c,d,e⟩; rfl
  measurable_toFun := comap_measurable cubicCode
  measurable_invFun := measurable_comap_iff.mpr measurable_id

abbrev Estimate (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] := OriginalEnvelopeOracleProgram.Estimate E F

def estimateCode (a : Estimate E F) : Joint E F × (E × (E →L[ℝ] E)) := (a.saddle,(a.grad,a.hess))
instance estimateMeasurableSpace : MeasurableSpace (Estimate E F) := MeasurableSpace.comap estimateCode inferInstance

def estimateEquiv : Estimate E F ≃ᵐ Joint E F × (E × (E →L[ℝ] E)) where
  toFun := estimateCode
  invFun := fun p => ⟨p.1,p.2.1,p.2.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rcases p with ⟨a,b,c⟩; rfl
  measurable_toFun := comap_measurable estimateCode
  measurable_invFun := measurable_comap_iff.mpr measurable_id

end
end FangqingAdmissibleMainData
end

section
-- Source component: AdmissibleMainGradientFamily.lean

open MeasureTheory
namespace FangqingAdmissibleMainGradient
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingAdmissibleMainData
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

abbrev State (E F:Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] := E × Joint E F

theorem gd_saddle_measurable : Measurable (fun r : GDResult E F => r.saddle) :=
  measurable_fst.comp (measurable_snd.comp gdEquiv.measurable)

theorem gd_moves_measurable : Measurable (fun r : GDResult E F => r.moves) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp gdEquiv.measurable))

theorem gd_append_measurable : Measurable (fun z : Move E F × GDResult E F =>
    OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.appendMove z.1 z.2) := by
  apply measurable_comap_iff.mpr
  have hc := (gdEquiv (E:=E) (F:=F)).measurable.comp
    (measurable_snd : Measurable (fun z:Move E F × GDResult E F => z.2))
  exact hc.fst.prodMk (hc.snd.fst.prodMk (hc.snd.snd.fst.prodMk
    (FangqingNaturalFiniteList.cons_measurable.comp (measurable_fst.prodMk hc.snd.snd.snd))))

theorem plugin_gradient_measurable (L:ℝ) :
    Measurable (fun z:State E F => OriginalEnvelopeOracle.plugInGradient L z.1 z.2) := by
  unfold OriginalEnvelopeOracle.plugInGradient
  exact measurable_const.smul (measurable_fst.sub ((WithLp.fstL 2 ℝ E F).continuous.measurable.comp measurable_snd))

def nextPoint (L:ℝ) (z:State E F) := z.1+OriginalOuterGD.step (2*L) (OriginalEnvelopeOracle.plugInGradient L z.1 z.2)

def nextRadius (mu L tau:ℝ) (z:State E F) := tau+2*Real.sqrt (L/mu)*
  ‖OriginalOuterGD.step (2*L) (OriginalEnvelopeOracle.plugInGradient L z.1 z.2)‖

theorem next_point_measurable (L:ℝ) : Measurable (nextPoint (E:=E) (F:=F) L) := by
  unfold nextPoint OriginalOuterGD.step
  exact measurable_fst.add (measurable_const.smul (plugin_gradient_measurable L))

theorem next_radius_measurable (mu L tau:ℝ) : Measurable (nextRadius (E:=E) (F:=F) mu L tau) := by
  unfold nextRadius OriginalOuterGD.step
  exact measurable_const.add (measurable_const.mul ((measurable_const.smul (plugin_gradient_measurable L)).norm))

theorem actual_gradient_loop_family (mu L rho tau eps:ℝ) (n:ℕ) :
    BorelFamily (fun z:State E F => OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.loop
      mu L rho tau eps n z.1 z.2) := by
  have hw : Measurable (fun z:State E F => z.2.snd) :=
    (WithLp.sndL 2 ℝ E F).continuous.measurable.comp measurable_snd
  have hY := next_point_measurable (E:=E) (F:=F) L
  have hD := next_radius_measurable (E:=E) (F:=F) mu L tau
  have hm : Measurable (fun z:State E F => (⟨z.1,nextPoint L z,z.2.snd,nextRadius mu L tau z⟩:Move E F)) :=
    moveEquiv.symm.measurable.comp (measurable_fst.prodMk (hY.prodMk (hw.prodMk hD)))
  induction n with
  | zero =>
    exact pure_family (Q:=Joint E F) (A:=OriginalDualOracleProgram.OracleAnswer (Joint E F))
      (fun z:State E F => (⟨z.1,z.2,false,[]⟩:GDResult E F))
      (gdEquiv.symm.measurable.comp (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const.prodMk measurable_const))))
  | succ n ih =>
    have ht := precomp_family _ ih (fun z:State E F × Joint E F => (nextPoint L z.1,z.2))
      ((hY.comp measurable_fst).prodMk measurable_snd)
    have ha := map_family _ ht (fun z:(State E F × Joint E F) × GDResult E F =>
      OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.appendMove
        (⟨z.1.1.1,nextPoint L z.1.1,z.1.1.2.snd,nextRadius mu L tau z.1.1⟩:Move E F) z.2)
      (gd_append_measurable.comp ((hm.comp measurable_fst.fst).prodMk measurable_snd))
    have hi : Measurable (fun z:State E F =>
        ((nextRadius mu L tau z,tau),(nextPoint L z,(nextPoint L z,z.2.snd)))) :=
      (hD.prodMk measurable_const).prodMk (hY.prodMk (hY.prodMk hw))
    have hs := precomp_family _ (FangqingBorelWarmMinimum.actual_joint_minimum_program_family (E:=E) (F:=F) mu L rho) _ hi
    have hb := bind_family _ hs _ ha
    have hstop := pure_family (Q:=Joint E F) (A:=OriginalDualOracleProgram.OracleAnswer (Joint E F))
      (fun z:State E F => (⟨z.1,z.2,true,[]⟩:GDResult E F))
      (gdEquiv.symm.measurable.comp (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const.prodMk measurable_const))))
    have htest : MeasurableSet {z:State E F | ‖OriginalEnvelopeOracle.plugInGradient L z.1 z.2‖ ≤ eps/2} :=
      measurableSet_le (plugin_gradient_measurable L).norm measurable_const
    have hall := ite_family _ htest _ _ hstop hb
    simpa only [OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.loop,
      nextPoint,nextRadius,OriginalAdmissibleMainReplay.OriginalMinimumWarmSolver.program,
      FangqingGetterComposition.map] using hall


theorem actual_gradient_program_family (mu L rho D0 tau eps Delta:ℝ) :
    BorelFamily (fun z:E×F => OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.program
      mu L rho D0 tau eps Delta z.1 z.2) := by
  have hi : Measurable (fun z:E×F => ((D0,tau),(z.1,(z.1,z.2)))) :=
    measurable_const.prodMk (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd))
  have hs := precomp_family _ (FangqingBorelWarmMinimum.actual_joint_minimum_program_family (E:=E) (F:=F) mu L rho) _ hi
  have ht := precomp_family _ (actual_gradient_loop_family (E:=E) (F:=F) mu L rho tau eps
    (OriginalOuterGD.fuel Delta (2*L) eps))
    (fun z:(E×F)×Joint E F => (z.1.1,z.2)) (measurable_fst.fst.prodMk measurable_snd)
  simpa only [OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.program,
    OriginalAdmissibleMainReplay.OriginalMinimumWarmSolver.program] using bind_family _ hs _ ht

/-- Genuine adaptive GD caller, with actual joint-radius/tolerance Borel inner
solver at every paid-query continuation, on every possible full answer stream. -/
theorem actual_gradient_caller_family (mu L rho Delta Ry eps:ℝ) :
    BorelFamily (fun z:E×F => OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.caller
      mu L rho Delta Ry eps z.1 z.2) :=
  actual_gradient_program_family mu L rho (Ry+(L/mu)*Real.sqrt (Delta/L))
    (OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.callerTolerance mu L eps) (eps/2) Delta

end
end FangqingAdmissibleMainGradient
end

section
-- Source component: AdmissibleEnvelopeEstimateFamily.lean

open MeasureTheory
namespace FangqingAdmissibleEstimate
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingAdmissibleMainData FangqingBorelDualOracleProgram
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] F) := borel (E →L[ℝ] F)
local instance : BorelSpace (E →L[ℝ] F) := ⟨rfl⟩
local instance : MeasurableSpace (F →L[ℝ] E) := borel (F →L[ℝ] E)
local instance : BorelSpace (F →L[ℝ] E) := ⟨rfl⟩
local instance : MeasurableSpace (F →L[ℝ] F) := borel (F →L[ℝ] F)
local instance : BorelSpace (F →L[ℝ] F) := ⟨rfl⟩

theorem schur_measurable : Measurable (OriginalSchurInverse.schur (E:=E) (F:=F)) := by
  have hXX : Continuous (OriginalSchurInverse.blockXX (E:=E) (F:=F)) := by
    unfold OriginalSchurInverse.blockXX; fun_prop
  have hXY : Continuous (OriginalSchurInverse.blockXY (E:=E) (F:=F)) := by
    unfold OriginalSchurInverse.blockXY; fun_prop
  have hYX : Continuous (OriginalSchurInverse.blockYX (E:=E) (F:=F)) := by
    unfold OriginalSchurInverse.blockYX; fun_prop
  have hYY : Continuous (OriginalSchurInverse.blockYY (E:=E) (F:=F)) := by
    unfold OriginalSchurInverse.blockYY; fun_prop
  have hi := OriginalBorelOperatorInverse.continuous_linear_map_inverse_measurable.comp hYY.measurable
  have hc : Continuous (fun p:(F→L[ℝ]E)×((F→L[ℝ]F)×(E→L[ℝ]F)) => p.1.comp (p.2.1.comp p.2.2)) := by fun_prop
  exact hXX.measurable.sub (hc.measurable.comp (hXY.measurable.prodMk (hi.prodMk hYX.measurable)))

theorem hessian_from_answer_measurable (L:ℝ) :
    Measurable (OriginalEnvelopeOracleProgram.hessianFromAnswer (E:=E) (F:=F) L) := by
  have hs : Measurable (fun H:Joint E F→L[ℝ]Joint E F =>
      OriginalSchurInverse.schur (H+(2*L) • OriginalSaddleTangent.primalProjection)) :=
    schur_measurable.comp (measurable_id.add_const _)
  exact (measurable_const (a:=(2*L) • ContinuousLinearMap.id ℝ E)).sub
    ((measurable_const (a:=(4*L^2:ℝ))).smul
      (OriginalBorelOperatorInverse.continuous_linear_map_inverse_measurable.comp hs))

theorem from_answer_measurable (L:ℝ) :
    Measurable (fun z:(E×Joint E F)×OriginalDualOracleProgram.OracleAnswer (Joint E F) =>
      OriginalEnvelopeOracleProgram.fromAnswer L z.1.1 z.1.2 z.2) := by
  have hg : Measurable (fun z:(E×Joint E F)×OriginalDualOracleProgram.OracleAnswer (Joint E F) =>
      OriginalEnvelopeOracle.plugInGradient L z.1.1 z.1.2) :=
    (FangqingAdmissibleMainGradient.plugin_gradient_measurable (E:=E) (F:=F) L).comp measurable_fst
  have hh : Measurable (fun z:(E×Joint E F)×OriginalDualOracleProgram.OracleAnswer (Joint E F) =>
      OriginalEnvelopeOracleProgram.hessianFromAnswer L z.2.hess) :=
    (hessian_from_answer_measurable (E:=E) (F:=F) L).comp (answer_hessian_measurable.comp measurable_snd)
  exact estimateEquiv.symm.measurable.comp (measurable_fst.snd.prodMk (hg.prodMk hh))

/-- Every actual envelope estimate pays its final bundled-Hessian request;
all inverse/model operations are total Borel even on invalid answers. -/
theorem actual_estimate_program_family (mu L rho tau:ℝ) :
    BorelFamily (fun z:ℝ×(E×F) =>
      OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.estimateProgram
        mu L rho z.1 tau z.2.1 z.2.2) := by
  let X := ℝ×(E×F)
  have hi : Measurable (fun z:X => ((z.1,tau),(z.2.1,(z.2.1,z.2.2)))) :=
    (measurable_fst.prodMk measurable_const).prodMk
      (measurable_snd.fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))
  have hw := precomp_family _ (FangqingBorelWarmMinimum.actual_joint_minimum_program_family (E:=E) (F:=F) mu L rho) _ hi
  have hm : Measurable (fun z:(X×Joint E F)×OriginalDualOracleProgram.OracleAnswer (Joint E F) =>
      OriginalEnvelopeOracleProgram.fromAnswer L z.1.1.2.1 z.1.2 z.2) :=
    (from_answer_measurable (E:=E) (F:=F) L).comp
      ((measurable_fst.fst.snd.fst.prodMk measurable_fst.snd).prodMk measurable_snd)
  have hret := pure_family (Q:=Joint E F) (A:=OriginalDualOracleProgram.OracleAnswer (Joint E F)) _ hm
  have ha := ask_family (fun z:X×Joint E F => z.2) measurable_snd _ hret
  simpa only [OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.estimateProgram,
    OriginalEnvelopeOracleProgram.program,OriginalAdmissibleMainReplay.OriginalMinimumWarmSolver.program] using
    bind_family _ hw _ ha

end
end FangqingAdmissibleEstimate
end

section
-- Source component: AdmissibleMainCubicFamily.lean

open MeasureTheory
namespace FangqingAdmissibleMainCubic
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingAdmissibleMainData FangqingAdmissibleEstimate
noncomputable section
set_option maxHeartbeats 7000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

abbrev State (E F:Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] := E × Estimate E F

theorem estimate_gradient_measurable : Measurable (fun a:Estimate E F => a.grad) :=
  measurable_fst.comp (measurable_snd.comp estimateEquiv.measurable)

theorem estimate_saddle_measurable : Measurable (fun a:Estimate E F => a.saddle) :=
  measurable_fst.comp estimateEquiv.measurable

theorem estimate_hessian_measurable : Measurable (fun a:Estimate E F => a.hess) :=
  measurable_snd.comp (measurable_snd.comp estimateEquiv.measurable)

theorem cubic_saddle_measurable : Measurable (fun a:CubicResult E F => a.saddle) :=
  measurable_fst.comp (measurable_snd.comp cubicEquiv.measurable)

theorem cubic_append_measurable : Measurable (fun z:Move E F × CubicResult E F =>
    OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.appendCharged z.1 z.2) := by
  apply measurable_comap_iff.mpr
  have hc := (cubicEquiv (E:=E) (F:=F)).measurable.comp
    (measurable_snd : Measurable (fun z:Move E F × CubicResult E F => z.2))
  exact hc.fst.prodMk (hc.snd.fst.prodMk (hc.snd.snd.fst.prodMk
    ((hc.snd.snd.snd.fst.add_const 1).prodMk
      (FangqingNaturalFiniteList.cons_measurable.comp (measurable_fst.prodMk hc.snd.snd.snd.snd)))))

theorem actual_cubic_minimizer_measurable (M:ℝ) :
    Measurable (fun p:E×(E→L[ℝ]E) =>
      OriginalAdmissibleMainReplay.OriginalBorelOuterCubic.minimizer p.1 p.2 M) := by
  classical
  by_cases hM:0<M
  · simpa only [OriginalAdmissibleMainReplay.OriginalBorelOuterCubic.minimizer,dif_pos hM] using
      OriginalCubicBorelSelection.select_measurable (E:=E) M hM
  · simp only [OriginalAdmissibleMainReplay.OriginalBorelOuterCubic.minimizer,dif_neg hM]
    exact measurable_const

def nextStep (M:ℝ) (z:State E F) :=
  OriginalAdmissibleMainReplay.OriginalBorelOuterCubic.minimizer z.2.grad z.2.hess (2*M)
def nextPoint (M:ℝ) (z:State E F) := z.1+nextStep M z
def nextRadius (mu L tau M:ℝ) (z:State E F) := tau+2*Real.sqrt (L/mu)*‖nextStep M z‖
def nextMove (mu L tau M:ℝ) (z:State E F) : Move E F :=
  ⟨z.1,nextPoint M z,z.2.saddle.snd,nextRadius mu L tau M z⟩

theorem next_step_measurable (M:ℝ) : Measurable (nextStep (E:=E) (F:=F) M) :=
  (actual_cubic_minimizer_measurable (2*M)).comp
    ((estimate_gradient_measurable.comp measurable_snd).prodMk (estimate_hessian_measurable.comp measurable_snd))

theorem next_point_measurable (M:ℝ) : Measurable (nextPoint (E:=E) (F:=F) M) :=
  measurable_fst.add (next_step_measurable M)

theorem next_radius_measurable (mu L tau M:ℝ) : Measurable (nextRadius (E:=E) (F:=F) mu L tau M) :=
  measurable_const.add (measurable_const.mul (next_step_measurable M).norm)

theorem next_move_measurable (mu L tau M:ℝ) : Measurable (nextMove (E:=E) (F:=F) mu L tau M) :=
  moveEquiv.symm.measurable.comp (measurable_fst.prodMk
    ((next_point_measurable M).prodMk
      (((WithLp.sndL 2 ℝ E F).continuous.measurable.comp
        (estimate_saddle_measurable.comp measurable_snd)).prodMk (next_radius_measurable mu L tau M))))

theorem actual_cubic_loop_family (mu L rho tau M eps:ℝ) (n:ℕ) :
    BorelFamily (fun z:State E F => OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.loop
      mu L rho tau M eps n z.1 z.2) := by
  have hS : Measurable (fun z:State E F => z.2.saddle) := estimate_saddle_measurable.comp measurable_snd
  have hG : Measurable (fun z:State E F => z.2.grad) := estimate_gradient_measurable.comp measurable_snd
  have hY := next_point_measurable (E:=E) (F:=F) M
  have hD := next_radius_measurable (E:=E) (F:=F) mu L tau M
  have hm := next_move_measurable (E:=E) (F:=F) mu L tau M
  induction n with
  | zero =>
    exact pure_family (Q:=Joint E F) (A:=OriginalDualOracleProgram.OracleAnswer (Joint E F))
      (fun z:State E F => (⟨z.1,z.2.saddle,false,0,[]⟩:CubicResult E F))
      (cubicEquiv.symm.measurable.comp (measurable_fst.prodMk (hS.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_const)))))
  | succ n ih =>
    have ht := precomp_family _ ih (fun z:State E F × Estimate E F => (nextPoint M z.1,z.2))
      ((hY.comp measurable_fst).prodMk measurable_snd)
    have ha := map_family _ ht (fun z:(State E F × Estimate E F) × CubicResult E F =>
      OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.appendCharged
        (nextMove mu L tau M z.1.1) z.2)
      (cubic_append_measurable.comp ((hm.comp measurable_fst.fst).prodMk measurable_snd))
    have hsing : Measurable (fun z:State E F × Estimate E F => [nextMove mu L tau M z.1]) :=
      FangqingNaturalFiniteList.cons_measurable.comp ((hm.comp measurable_fst).prodMk measurable_const)
    have hstopInner := pure_family (Q:=Joint E F) (A:=OriginalDualOracleProgram.OracleAnswer (Joint E F))
      (fun z:State E F × Estimate E F => (⟨nextPoint M z.1,z.2.saddle,true,0,[nextMove mu L tau M z.1]⟩:CubicResult E F))
      (cubicEquiv.symm.measurable.comp ((hY.comp measurable_fst).prodMk
        ((estimate_saddle_measurable.comp measurable_snd).prodMk (measurable_const.prodMk
          (measurable_const.prodMk hsing)))))
    have htestInner : MeasurableSet {z:State E F × Estimate E F | ‖z.2.grad‖ ≤ eps/2} :=
      measurableSet_le (estimate_gradient_measurable.comp measurable_snd).norm measurable_const
    have hc := ite_family _ htestInner _ _ hstopInner ha
    have hi : Measurable (fun z:State E F =>
        (nextRadius mu L tau M z,(nextPoint M z,z.2.saddle.snd))) :=
      hD.prodMk (hY.prodMk ((WithLp.sndL 2 ℝ E F).continuous.measurable.comp hS))
    have hs := precomp_family _ (actual_estimate_program_family (E:=E) (F:=F) mu L rho tau) _ hi
    have hb := bind_family _ hs _ hc
    have hstop := pure_family (Q:=Joint E F) (A:=OriginalDualOracleProgram.OracleAnswer (Joint E F))
      (fun z:State E F => (⟨z.1,z.2.saddle,true,0,[]⟩:CubicResult E F))
      (cubicEquiv.symm.measurable.comp (measurable_fst.prodMk (hS.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_const)))))
    have htest : MeasurableSet {z:State E F | ‖z.2.grad‖ ≤ eps/2} := measurableSet_le hG.norm measurable_const
    have hall := ite_family _ htest _ _ hstop hb
    simpa only [OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.loop,
      nextStep,nextPoint,nextRadius,nextMove,FangqingGetterComposition.map] using hall

theorem actual_cubic_program_family (mu L rho D0 tau M eps Delta:ℝ) :
    BorelFamily (fun z:E×F => OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.program
      mu L rho D0 tau M eps Delta z.1 z.2) := by
  have hs := precomp_family _ (actual_estimate_program_family (E:=E) (F:=F) mu L rho tau)
    (fun z:E×F => (D0,z)) (measurable_const.prodMk measurable_id)
  have ht := precomp_family _ (actual_cubic_loop_family (E:=E) (F:=F) mu L rho tau M eps
    (OriginalAdmissibleMainReplay.OriginalBorelOuterCubicSeparateErrors.fuel Delta M eps))
    (fun z:(E×F)×Estimate E F => (z.1.1,z.2)) (measurable_fst.fst.prodMk measurable_snd)
  simpa only [OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.program] using bind_family _ hs _ ht


theorem actual_cubic_caller_family (mu L rho Delta Ry eps:ℝ) :
    BorelFamily (fun z:E×F => OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.caller
      mu L rho Delta Ry eps z.1 z.2) :=
  actual_cubic_program_family mu L rho (Ry+(L/mu)*Real.sqrt (Delta/L))
    (OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.callerTolerance mu L rho eps)
    (OriginalAdmissibleMainReplay.OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) (eps/2) Delta

end
end FangqingAdmissibleMainCubic
end

section
-- Source component: BorelZeroSyntheticOracle.lean

open MeasureTheory
namespace FangqingBorelZeroSyntheticOracle
open OriginalDualOracleProgram FangqingBorelDualOracleProgram
noncomputable section
variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  [MeasurableSpace (Z →L[ℝ] Z)] [BorelSpace (Z →L[ℝ] Z)]

theorem sympart_continuous : Continuous (CertifiedATS.sympart (E := Z)) := by
  unfold CertifiedATS.sympart
  exact (continuous_id.add ContinuousLinearMap.adjoint.continuous).const_smul (1/2 : ℝ)

theorem synthetic_quadratic_value_measurable : Measurable (fun x : OracleAnswer Z × Z =>
    OriginalZeroHessianReconstruction.quadratic x.1 x.2) := by
  have hv := (answer_value_measurable (Z := Z)).comp (measurable_fst : Measurable (Prod.fst : OracleAnswer Z × Z → OracleAnswer Z))
  have hg := (answer_gradient_measurable (Z := Z)).comp (measurable_fst : Measurable (Prod.fst : OracleAnswer Z × Z → OracleAnswer Z))
  have hH := (answer_hessian_measurable (Z := Z)).comp (measurable_fst : Measurable (Prod.fst : OracleAnswer Z × Z → OracleAnswer Z))
  have heval : Measurable (fun x : OracleAnswer Z × Z => x.1.hess x.2) :=
    ((show Continuous (fun p : (Z →L[ℝ] Z) × Z => p.1 p.2) by fun_prop).measurable).comp (hH.prodMk measurable_snd)
  have hm := hv.add ((hg.inner measurable_snd).add
      ((measurable_const (a := (1/2 : ℝ))).mul (heval.inner measurable_snd)))
  convert hm using 1
  funext x
  simp only [OriginalZeroHessianReconstruction.quadratic,OriginalOuterCubic.model,
    zero_div,zero_mul,add_zero,Function.comp_def,Pi.add_apply,Pi.mul_apply]

theorem synthetic_polynomial_oracle_measurable : Measurable (fun x : OracleAnswer Z × Z =>
    OriginalZeroHessianReconstruction.polynomialOracle x.1 x.2) := by
  have hg := (answer_gradient_measurable (Z := Z)).comp (measurable_fst : Measurable (Prod.fst : OracleAnswer Z × Z → OracleAnswer Z))
  have hH := (answer_hessian_measurable (Z := Z)).comp (measurable_fst : Measurable (Prod.fst : OracleAnswer Z × Z → OracleAnswer Z))
  have hs := sympart_continuous.measurable.comp hH
  have heval : Measurable (fun x : OracleAnswer Z × Z => CertifiedATS.sympart x.1.hess x.2) :=
    ((show Continuous (fun p : (Z →L[ℝ] Z) × Z => p.1 p.2) by fun_prop).measurable).comp (hs.prodMk measurable_snd)
  exact answer_mk_measurable _ _ _ synthetic_quadratic_value_measurable (hg.add heval) hs

end
end FangqingBorelZeroSyntheticOracle
end

section
-- Source component: AdmissibleZeroHessianFamily.lean

open MeasureTheory
namespace FangqingAdmissibleZeroHessianFamily
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingBorelGetterOperationalReplay FangqingAdmissibleMainData FangqingAdmissibleMainGradient
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

/-- The free computation after the one paid bundle is a genuine jointly Borel
finite execution of the reconstructed polynomial oracle with the admissible GD
caller, on every possible input bundle including illegal synthetic quadratics. -/
theorem synthetic_reconstruction_result_measurable (mu L Delta Ry eps : ℝ) :
    Measurable (fun z : (E×F) × OriginalDualOracleProgram.OracleAnswer (Joint E F) =>
      (execute (OriginalAdmissibleMainReplay.OriginalZeroHessianReconstruction.polynomialOracle z.2)
        (OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.caller
          mu L 0 Delta Ry eps z.1.1 z.1.2)).1.saddle.fst) := by
  let p := fun z : (E×F) × OriginalDualOracleProgram.OracleAnswer (Joint E F) =>
    OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.caller mu L 0 Delta Ry eps z.1.1 z.1.2
  have hp : BorelFamily p := precomp_family _ (actual_gradient_caller_family mu L 0 Delta Ry eps)
    Prod.fst measurable_fst
  let getter := fun z : ((E×F) × OriginalDualOracleProgram.OracleAnswer (Joint E F)) × Joint E F =>
    OriginalAdmissibleMainReplay.OriginalZeroHessianReconstruction.polynomialOracle z.1.2 z.2
  have hg : Measurable getter := by
    change Measurable (fun z : ((E×F) × OriginalDualOracleProgram.OracleAnswer (Joint E F)) × Joint E F =>
      OriginalZeroHessianReconstruction.polynomialOracle z.1.2 z.2)
    exact FangqingBorelZeroSyntheticOracle.synthetic_polynomial_oracle_measurable.comp
      (measurable_snd.comp measurable_fst |>.prodMk measurable_snd)
  let a0 : OriginalDualOracleProgram.OracleAnswer (Joint E F) := ⟨0,0,0⟩
  have he := actual_execution_result_and_count_measurable p hp getter hg a0 0
  have hs := (WithLp.fstL 2 ℝ E F).continuous.measurable.comp
    ((gd_saddle_measurable (E:=E) (F:=F)).comp (measurable_fst.comp he))
  exact hs

/-- Exactly one original-oracle request and a full-answer-space Borel output,
for the actual rho=0 branch used by the final three-branch main algorithm. -/
theorem actual_zero_hessian_program_family (mu L Delta Ry eps : ℝ) :
    BorelFamily (fun z : E×F =>
      OriginalAdmissibleMainReplay.OriginalZeroHessianReconstruction.program
        mu L Delta Ry eps z.1 z.2) := by
  exact ask_family _ measurable_const _
    (pure_family _ (synthetic_reconstruction_result_measurable mu L Delta Ry eps))

end
end FangqingAdmissibleZeroHessianFamily
end

section
-- Source component: AdmissibleMainUpperComplete.lean

open MeasureTheory
namespace FangqingAdmissibleMainUpper
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
  OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingAdmissibleMainData
  FangqingAdmissibleMainCubic FangqingAdmissibleMainGradient
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

theorem actual_positive_upper_program_family (mu L rho Delta Ry eps:ℝ) :
    BorelFamily (fun z:E×F => OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.positiveProgram
      mu L rho Delta Ry eps z.1 z.2) := by
  have hc := map_family _ (actual_cubic_caller_family (E:=E) (F:=F) mu L rho Delta Ry eps)
    (fun z:(E×F)×CubicResult E F => z.2.saddle.fst)
    ((WithLp.fstL 2 ℝ E F).continuous.measurable.comp (cubic_saddle_measurable.comp measurable_snd))
  have hg := map_family _ (actual_gradient_caller_family (E:=E) (F:=F) mu L rho Delta Ry eps)
    (fun z:(E×F)×GDResult E F => z.2.saddle.fst)
    ((WithLp.fstL 2 ℝ E F).continuous.measurable.comp (gd_saddle_measurable.comp measurable_snd))
  classical
  by_cases h:OriginalGDRateNormalization.ratio mu L rho eps ≤ 1
  · simpa only [OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.positiveProgram,if_pos h] using hc
  · simpa only [OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.positiveProgram,if_neg h] using hg

/-- Complete original-O2 program, including rho=0 synthetic reconstruction,
actual adaptive cubic/GD trajectories, every changing-radius warm callback,
and all request/stop/output maps on arbitrary full answer streams. -/
theorem actual_full_upper_program_family (mu L rho Delta Ry eps:ℝ) :
    BorelFamily (fun z:E×F => OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.program
      mu L rho Delta Ry eps z.1 z.2) := by
  classical
  by_cases h:rho=0
  · simpa only [OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.program,if_pos h] using
      FangqingAdmissibleZeroHessianFamily.actual_zero_hessian_program_family (E:=E) (F:=F) mu L Delta Ry eps
  · simpa only [OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.program,if_neg h] using
      actual_positive_upper_program_family (E:=E) (F:=F) mu L rho Delta Ry eps

/-- Main-upper obligation only. This is a complete admissible actual algorithm
with the manuscript's three-way polynomial frontier. Its explicit logarithmic
multiplier includes the proved factor TWO for dyadic warm rounding. The lower
bound and unchanged full thm:main are separate original-Claim obligations. -/
theorem admissible_main_upper_from_original_standing_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z-gradient J w‖ ≤ L*‖z-w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z-fderiv ℝ (gradient J) w‖ ≤ rho*‖z-w‖)
    (hsc : ∀ u:E, StrongConvexOn (Set.univ:Set F) mu (fun y=>-JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start:E) (yin:F)
    (hgap : phi (JointSliceRegularity.curry J) start-sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin-yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    BorelFamily (fun z:E×F => OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.program
      mu L rho Delta Ry eps z.1 z.2) ∧
    let run:=execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.program mu L rho Delta Ry eps start yin)
    let U:=OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.logarithmicFactor mu L rho Delta Ry eps
    1≤U ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖≤eps ∧
      (run.2:ℝ)≤32768*U*(OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry+
        OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps) :=
  ⟨actual_full_upper_program_family mu L rho Delta Ry eps,
    OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.main_upper_from_original_standing_inputs
      J mu L rho Delta Ry eps hmu hLmu hrho heps hC2 hLip hHess hsc hbelow start yin hgap hdual⟩

theorem actual_full_upper_execution_measurable (J:Joint E F→ℝ) (hC2:ContDiff ℝ 2 J)
    (mu L rho Delta Ry eps:ℝ) :
    Measurable (fun z:E×F => execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.program mu L rho Delta Ry eps z.1 z.2)) :=
  FangqingBorelGetterOperationalReplay.actual_execution_result_and_count_measurable _
    (actual_full_upper_program_family mu L rho Delta Ry eps)
    (fun z:(E×F)×Joint E F => OriginalDualOracleProgram.actualOracle J z.2)
    ((FangqingBorelWarmMinimum.actual_bundle_measurable J hC2).comp measurable_snd) ⟨0,0,0⟩ 0

end
end FangqingAdmissibleMainUpper
end


namespace FangqingMainOriginalScalars
open OriginalThreePhaseScalars
noncomputable section
set_option maxHeartbeats 4500000

def mainTerm (mu L rho Delta eps:ℝ) : ℝ :=
  OriginalGDRateNormalization.A1 Delta L eps *
    OriginalThreePhaseScalars.frontier (L/mu) (HandleAlignment.regime L rho eps (L/mu))

theorem ratio_is_paper_regime (mu L rho eps:ℝ) (hmu:0 < mu) (hL:0 < L) :
    OriginalGDRateNormalization.ratio mu L rho eps=HandleAlignment.regime L rho eps (L/mu) :=
  OriginalGDRateNormalization.ratio_eq_paper mu L rho eps hmu hL

theorem displayed_minimum_factorization (mu L rho Delta eps:ℝ)
    (hmu:0 < mu) (hL:0 < L) (hrho:0 ≤ rho) (hDelta:0 ≤ Delta) (heps:0 < eps) :
    OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps =
      OriginalGDRateNormalization.A1 Delta L eps *
        OriginalThreePhaseScalars.upperFactor (L/mu) (HandleAlignment.regime L rho eps (L/mu)) := by
  have ha : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have h2:=OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.A2_eq_A1_sqrt_ratio mu L rho Delta eps hmu hL hrho heps
  unfold OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier
    OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.cubic
    OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.middle
    OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.first upperFactor
  rw [h2,ratio_is_paper_regime mu L rho eps hmu hL,
    mul_min_of_nonneg _ _ ha,mul_min_of_nonneg _ _ ha]
  congr 1
  · ring
  · congr 1
    ring

theorem original_frontier_within_factor_two (mu L rho Delta eps:ℝ)
    (hmu:0 < mu) (hLmu:mu ≤ L) (hrho:0 < rho) (hDelta:0 ≤ Delta) (heps:0 < eps) :
    mainTerm mu L rho Delta eps  ≤ 
      OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps ∧
    OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps  ≤ 
      2*mainTerm mu L rho Delta eps := by
  have hL:=hmu.trans_le hLmu
  have hk:1 ≤ L/mu := (one_le_div hmu).mpr hLmu
  have hr:0 < HandleAlignment.regime L rho eps (L/mu) := by unfold HandleAlignment.regime; positivity
  have ha:0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have h:=complete_scalar_frontier (L/mu) (HandleAlignment.regime L rho eps (L/mu)) hk hr
  rw [displayed_minimum_factorization mu L rho Delta eps hmu hL hrho.le hDelta heps]
  exact ⟨mul_le_mul_of_nonneg_left h.1 ha,by simpa only [mainTerm,mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left h.2 ha⟩

theorem dominated_upper_exact_constant (T U I mu L rho Delta eps:ℝ)
    (hmu:0 < mu) (hLmu:mu ≤ L) (hrho:0 < rho) (hDelta:0 ≤ Delta) (heps:0 < eps)
    (hU:0 ≤ U) (hdom:I+1 ≤ mainTerm mu L rho Delta eps)
    (hupper:T ≤ 32768*U*(I+OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps)) :
    T ≤ 98304*U*mainTerm mu L rho Delta eps := by
  have hR:=(original_frontier_within_factor_two mu L rho Delta eps hmu hLmu hrho hDelta heps).2
  have hI:I ≤ mainTerm mu L rho Delta eps := by linarith only [hdom]
  have hh:=mul_le_mul_of_nonneg_left (add_le_add hI hR) (show 0 ≤ 32768*U by positivity)
  nlinarith only [hupper,hh]


/-- Exact powers in the middle row of the original three-rate display. -/
theorem middle_rate_identity (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (heps : 0 < eps) :
    OriginalGDRateNormalization.A1 Delta L eps * (HandleAlignment.regime L rho eps (L/mu))^(2/7:ℝ) =
      Delta*rho^(2/7:ℝ)*(L/mu)^(3/7:ℝ)*L^(3/7:ℝ)/eps^(12/7:ℝ) := by
  have hk : 0 ≤ L/mu := by positivity
  have hL4 : 0 < L^(4/7:ℝ) := Real.rpow_pos_of_pos hL _
  have he2 : 0 < eps^(2/7:ℝ) := Real.rpow_pos_of_pos heps _
  have he12 : 0 < eps^(12/7:ℝ) := Real.rpow_pos_of_pos heps _
  have hLprod : L^(3/7:ℝ)*L^(4/7:ℝ)=L := by rw [←Real.rpow_add hL]; norm_num
  have heprod : eps^(12/7:ℝ)*eps^(2/7:ℝ)=eps^2 := by rw [←Real.rpow_add heps]; norm_num
  have hp : (HandleAlignment.regime L rho eps (L/mu))^(2/7:ℝ)=
      rho^(2/7:ℝ)*(L/mu)^(3/7:ℝ)*eps^(2/7:ℝ)/L^(4/7:ℝ) := by
    unfold HandleAlignment.regime
    rw [Real.div_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) heps.le,
      Real.mul_rpow hrho.le (Real.rpow_nonneg hk _),←Real.rpow_mul hk,
      ←Real.rpow_natCast L 2,←Real.rpow_mul hL.le]
    norm_num
  rw [hp]
  unfold OriginalGDRateNormalization.A1
  calc
    _ = Delta*(L^(3/7:ℝ)*L^(4/7:ℝ))/(eps^(12/7:ℝ)*eps^(2/7:ℝ))*
      (rho^(2/7:ℝ)*(L/mu)^(3/7:ℝ)*eps^(2/7:ℝ)/L^(4/7:ℝ)) := by rw [hLprod,heprod]
    _ = _ := by field_simp [ne_of_gt hL4,ne_of_gt he2,ne_of_gt he12] <;> ring

/-- All three closed phase rows, including their shared endpoints. -/
theorem original_three_rate_rows (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps) :
    let r := HandleAlignment.regime L rho eps (L/mu)
    (r ≤ 1 → mainTerm mu L rho Delta eps =
      Delta*Real.sqrt rho*(L/mu)^(3/4:ℝ)/eps^(3/2:ℝ)) ∧
    (1 ≤ r → r ≤ (L/mu)^(7/4:ℝ) → mainTerm mu L rho Delta eps =
      Delta*rho^(2/7:ℝ)*(L/mu)^(3/7:ℝ)*L^(3/7:ℝ)/eps^(12/7:ℝ)) ∧
    ((L/mu)^(7/4:ℝ) ≤ r → mainTerm mu L rho Delta eps =
      Delta*L*Real.sqrt (L/mu)/eps^2) := by
  dsimp only
  have hL := hmu.trans_le hLmu
  have hk : 1 ≤ L/mu := (one_le_div hmu).mpr hLmu
  let r := HandleAlignment.regime L rho eps (L/mu)
  have hA2 := OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.A2_eq_A1_sqrt_ratio
    mu L rho Delta eps hmu hL hrho.le heps
  rw [ratio_is_paper_regime mu L rho eps hmu hL] at hA2
  refine ⟨?_,?_,?_⟩
  · intro hr
    unfold mainTerm
    rw [OriginalThreePhaseScalars.frontier,if_pos hr,←hA2]
    rfl
  · intro hr hp
    by_cases hr1 : r ≤ 1
    · have he : r=1 := le_antisymm hr1 hr
      have hm : mainTerm mu L rho Delta eps = OriginalGDRateNormalization.A1 Delta L eps * r^(2/7:ℝ) := by
        unfold mainTerm
        change _*OriginalThreePhaseScalars.frontier (L/mu) r = _
        rw [OriginalThreePhaseScalars.frontier,if_pos hr1,he,Real.sqrt_one,Real.one_rpow]
      rw [hm]
      exact middle_rate_identity mu L rho Delta eps hmu hL hrho heps
    · unfold mainTerm
      rw [OriginalThreePhaseScalars.frontier,if_neg hr1,if_pos hp]
      exact middle_rate_identity mu L rho Delta eps hmu hL hrho heps
  · intro hp
    have hu := OriginalThreePhaseScalars.third_phase_identity (L/mu) r hk hp
    have hf := OriginalThreePhaseScalars.complete_scalar_frontier (L/mu) r hk
      (by dsimp [r,HandleAlignment.regime]; positivity)
    have hfr : OriginalThreePhaseScalars.frontier (L/mu) r = Real.sqrt (L/mu) := by
      unfold OriginalThreePhaseScalars.frontier
      by_cases h1 : r ≤ 1
      · have hkthr : 1 ≤ (L/mu)^(7/4:ℝ) := Real.one_le_rpow hk (by norm_num)
        have hre : r=1 := le_antisymm h1 (hkthr.trans hp)
        have hkpow : L/mu ≤ (L/mu)^(7/4:ℝ) := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hk
            (by norm_num : (1:ℝ) ≤ 7/4)
        have hkEq : L/mu=1 := le_antisymm (hkpow.trans (hp.trans h1)) hk
        simp [h1,hre,hkEq]
      · by_cases h2 : r ≤ (L/mu)^(7/4:ℝ)
        · rw [if_neg h1,if_pos h2,le_antisymm h2 hp,OriginalThreePhaseScalars.threshold_rpow_identity _ (zero_le_one.trans hk)]
        · rw [if_neg h1,if_neg h2]
    unfold mainTerm
    change _*OriginalThreePhaseScalars.frontier (L/mu) r = _
    rw [hfr]
    unfold OriginalGDRateNormalization.A1
    ring

end
end FangqingMainOriginalScalars


namespace FangqingMainOriginalScalars
noncomputable section

theorem dominated_upper_with_fixed_factor (T U K I mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps)
    (hU : 0 ≤ U) (hdom : I+1 ≤ K*mainTerm mu L rho Delta eps)
    (hupper : T ≤ 32768*U*(I+OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps)) :
    T ≤ 32768*(K+2)*U*mainTerm mu L rho Delta eps := by
  have hR := (original_frontier_within_factor_two mu L rho Delta eps hmu hLmu hrho hDelta heps).2
  have hI : I ≤ K*mainTerm mu L rho Delta eps := by linarith only [hdom]
  have hh := mul_le_mul_of_nonneg_left (add_le_add hI hR) (show 0 ≤ 32768*U by positivity)
  nlinarith only [hupper,hh]

end
end FangqingMainOriginalScalars


open MeasureTheory
namespace FangqingOriginalMainTheorem
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
  OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingCanonicalSeedProfile FangqingCanonicalHierarchyGlobalWorld
  FangqingCompositionOriginalTheorem FangqingCompleteLowerOriginalTheorem
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingMainOriginalScalars
noncomputable section
set_option maxHeartbeats 8000000
universe v

/-- Original finite-dimensional deterministic oracle obligation. Every request,
stop and output continuation has its actual full-answer Borel certificate. -/
def UpperAtParameters (mu L rho Delta Ry eps : ℝ) : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F],
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace F := borel F
  letI : BorelSpace F := ⟨rfl⟩
  letI : MeasurableSpace (Joint E F) := borel (Joint E F)
  letI : BorelSpace (Joint E F) := ⟨rfl⟩
  letI : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
  letI : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩
  ∀ (J : Joint E F → ℝ), ContDiff ℝ 2 J →
    (∀ z w : Joint E F, ‖gradient J z-gradient J w‖ ≤ L*‖z-w‖) →
    (∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z-fderiv ℝ (gradient J) w‖ ≤ rho*‖z-w‖) →
    (∀ u:E, StrongConvexOn (Set.univ:Set F) mu (fun y=>-JointSliceRegularity.curry J u y)) →
    BddBelow (Set.range (phi (JointSliceRegularity.curry J))) →
  ∀ (start:E) (yin:F),
    phi (JointSliceRegularity.curry J) start-sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta →
    ‖yin-yStar (JointSliceRegularity.curry J) start‖ ≤ Ry →
  BorelFamily (fun z:E×F => OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.program
    mu L rho Delta Ry eps z.1 z.2) ∧
  let run:=execute (OriginalDualOracleProgram.actualOracle J)
    (OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.program mu L rho Delta Ry eps start yin)
  let U:=OriginalAdmissibleMainReplay.OriginalBorelActualMainUpper.logarithmicFactor mu L rho Delta Ry eps
  1 ≤ U ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps ∧
    (run.2:ℝ) ≤ 32768*U*(OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry+
      OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps) ∧
  (0 < rho → ∀ K : ℝ,
    OriginalAdmissibleMainReplay.OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry+1 ≤
      K*mainTerm mu L rho Delta eps → (run.2:ℝ) ≤ 32768*(K+2)*U*mainTerm mu L rho Delta eps)

theorem actual_upper_at_parameters (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps) :
    UpperAtParameters mu L rho Delta Ry eps := by
  intro E F _ _ _ _ _ _ _ _
  dsimp only
  intro J hC2 hLip hHess hsc hbelow start yin hgap hdual
  have h := FangqingAdmissibleMainUpper.admissible_main_upper_from_original_standing_inputs
    J mu L rho Delta Ry eps hmu hLmu hrho heps hC2 hLip hHess hsc hbelow start yin hgap hdual
  rcases h with ⟨hb,hU,hgrad,hcost⟩
  refine ⟨hb,hU,hgrad,hcost,?_⟩
  intro hrhoPos K hdom
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap,hi]
  exact dominated_upper_with_fixed_factor _ _ K _ mu L rho Delta eps hmu hLmu hrhoPos hDelta heps
    (zero_le_one.trans hU) hdom hcost

/-- The lower certificate includes literal ordinary full-jet executions,
instance-independent arbitrary random seeds, finite infimum, exact dual
initialization, and the original public-dimension/fixed-instance order. -/
def LowerAtParameters
    (H : HierarchyConstants.{0} FlatCubic.canonicalProfile seedProfile 4 24)
    (c : ℝ) (mu L rho Delta eps : ℝ) : Prop :=
  let r:=HandleAlignment.regime L rho eps (L/mu)
  FangqingThirdGroupScaling.rho L mu eps r=rho ∧
    UnrestrictedHardAtRate.{v} FlatCubic.canonicalProfile seedProfile 4 24 H L mu eps r Delta
      (c*mainTerm mu L rho Delta eps)

theorem original_main_lower_with_zero_boundary :
    ∃ (H : HierarchyConstants.{0} FlatCubic.canonicalProfile seedProfile 4 24) (c C : ℝ),
      0 < c ∧ 0 < C ∧
      ∀ L mu rho eps Delta : ℝ, 0 < L → 0 < mu → mu ≤ L → 0 ≤ rho → 0 < eps → 0 ≤ Delta →
        C ≤ OriginalGDRateNormalization.A1 Delta L eps → LowerAtParameters.{v} H c mu L rho Delta eps := by
  obtain ⟨H,c,C,hc,hC,hLower⟩ := FangqingClosedOriginalLowerTheorems.original_complete_lower_closed.{v}
  refine ⟨H,c,C,hc,hC,?_⟩
  intro L mu rho eps Delta hL hmu hmL hrho heps hDelta hA
  have hDeltaPos : 0 < Delta := by
    by_contra hn
    have ha : OriginalGDRateNormalization.A1 Delta L eps ≤ 0 := by
      unfold OriginalGDRateNormalization.A1
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hL.le) (sq_nonneg eps)
    linarith only [hC,hA,ha]
  by_cases hp : 0 < rho
  · simpa only [LowerAtParameters,mainTerm,OriginalGDRateNormalization.A1,mul_assoc] using
      hLower L mu rho eps Delta hL hmu hmL hp heps hDeltaPos hA
  · have hz : rho=0 := le_antisymm (le_of_not_gt hp) hrho
    subst rho
    have hr : HandleAlignment.regime L 0 eps (L/mu)=0 := by simp [HandleAlignment.regime]
    constructor
    · exact external_curvature_reparameterization L mu eps 0 hL hmu heps
    · unfold UnrestrictedHardAtRate
      left
      refine ⟨1,by norm_num,?_⟩
      have hT : c*mainTerm mu L 0 Delta eps=0 := by simp [mainTerm,hr,OriginalThreePhaseScalars.frontier]
      rw [hT]
      intro Seed _ seeds _ N hN
      exact False.elim ((not_lt_of_ge (Nat.cast_nonneg N)) hN)

/-- Complete original thm:main, with universal constants chosen before all
problem parameters, dimensions, algorithms and realized random seeds. The
piecewise frontier and explicit three-rate identities share the SAME r and
normalization as the actual upper and randomized lower executions. -/
theorem original_main_three_phase_frontier :
    ∃ (H : HierarchyConstants.{0} FlatCubic.canonicalProfile seedProfile 4 24) (c C : ℝ),
      0 < c ∧ 0 < C ∧
      (∀ mu L rho Delta Ry eps : ℝ, 0 < mu → mu ≤ L → 0 ≤ rho → 0 < eps →
        UpperAtParameters mu L rho Delta Ry eps) ∧
      (∀ L mu rho eps Delta : ℝ, 0 < L → 0 < mu → mu ≤ L → 0 ≤ rho → 0 < eps → 0 ≤ Delta →
        C ≤ OriginalGDRateNormalization.A1 Delta L eps → LowerAtParameters.{v} H c mu L rho Delta eps) ∧
      (∀ mu L rho Delta eps : ℝ, 0 < mu → mu ≤ L → 0 < rho → 0 ≤ Delta → 0 < eps →
        mainTerm mu L rho Delta eps ≤ OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps ∧
        OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps ≤ 2*mainTerm mu L rho Delta eps) ∧
      (∀ T U I mu L rho Delta eps : ℝ, 0 < mu → mu ≤ L → 0 < rho → 0 ≤ Delta → 0 < eps →
        0 ≤ U → I+1 ≤ mainTerm mu L rho Delta eps →
        T ≤ 32768*U*(I+OriginalAdmissibleMainReplay.OriginalBorelMainUpperRates.frontier mu L rho Delta eps) →
        T ≤ 98304*U*mainTerm mu L rho Delta eps) ∧
      (∀ mu L rho Delta eps : ℝ, 0 < mu → mu ≤ L → 0 < rho → 0 < eps →
        let r:=HandleAlignment.regime L rho eps (L/mu)
        (r ≤ 1 → mainTerm mu L rho Delta eps=Delta*Real.sqrt rho*(L/mu)^(3/4:ℝ)/eps^(3/2:ℝ)) ∧
        (1 ≤ r → r ≤ (L/mu)^(7/4:ℝ) → mainTerm mu L rho Delta eps=
          Delta*rho^(2/7:ℝ)*(L/mu)^(3/7:ℝ)*L^(3/7:ℝ)/eps^(12/7:ℝ)) ∧
        ((L/mu)^(7/4:ℝ) ≤ r → mainTerm mu L rho Delta eps=Delta*L*Real.sqrt (L/mu)/eps^2)) := by
  obtain ⟨H,c,C,hc,hC,hLower⟩ := original_main_lower_with_zero_boundary.{v}
  exact ⟨H,c,C,hc,hC,actual_upper_at_parameters,hLower,
    original_frontier_within_factor_two,dominated_upper_exact_constant,original_three_rate_rows⟩

end
end FangqingOriginalMainTheorem