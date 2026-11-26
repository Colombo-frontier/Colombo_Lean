import Bilevel.MultiscaleDisclosedContinuity
import Bilevel.MultiscaleDisclosedReply
import Bilevel.ParametricGradientMeasurable

/-! Total Borel full replies from old/new finite arrays. Scalar gradients
are canonical, including at arbitrary invalid data. -/
noncomputable section
namespace Bilevel.MultiscaleMean.Parameters
open CompensatedMean
set_option autoImplicit false
set_option maxHeartbeats 150000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (P : Parameters (E:=E) n)

omit [CompleteSpace E] in
theorem disclosedSample_continuous (p : ℝ) (r s : ℕ) (coin : Bool) :
    Continuous (fun z : ((Fin (n+1) → E) × (Fin (n+1) → E)) × InnerQuery E =>
      P.disclosedSample p r s z.1.1 z.1.2 coin z.2.1 z.2.2) := by
  have hargsOld : Continuous (fun z : ((Fin (n+1) → E) × (Fin (n+1) → E)) × InnerQuery E => (z.1.1,z.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hargsNew : Continuous (fun z : ((Fin (n+1) → E) × (Fin (n+1) → E)) × InnerQuery E => (z.1.2,z.2)) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  have hi := (P.disclosedLower_continuous false r).comp hargsOld
  have ha := (P.disclosedLower_continuous true s).comp hargsNew
  exact hi.add (continuous_const.mul (ha.sub hi))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)]

theorem disclosedReply_fixed_measurable (p : ℝ) (r s : ℕ) (coin : Bool) :
    Measurable (fun z : ((Fin (n+1) → E) × (Fin (n+1) → E)) × InnerQuery E =>
      P.disclosedReply p r s z.1.1 z.1.2 z.2 coin) := by
  let Col := Fin (n+1) → E
  have hfyC : Continuous (Function.uncurry
      (fun a : Col × E => P.disclosedUpper r a.1 a.2)) := by
    have hargs : Continuous (fun z : (Col × E) × LowerSpace E => (z.1.1,(z.1.2,z.2))) :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    have h := (P.disclosedUpper_continuous r).comp hargs
    exact h
  have hfy := ParametricGradient.gradient_measurable (P:=Col × E) (E:=LowerSpace E)
    (fun a : Col × E => P.disclosedUpper r a.1 a.2) hfyC
  have hfyArgs : Measurable (fun z : (Col × Col) × InnerQuery E => ((z.1.1,z.2.1),z.2.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)
  have hfy' := hfy.comp hfyArgs
  have hgyC : Continuous (Function.uncurry
      (fun a : (Col × Col) × E => P.disclosedSample p r s a.1.1 a.1.2 coin a.2)) := by
    have hargs : Continuous (fun z : ((Col × Col) × E) × LowerSpace E => (z.1.1,(z.1.2,z.2))) :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    have h := (P.disclosedSample_continuous p r s coin).comp hargs
    exact h
  have hgy := ParametricGradient.gradient_measurable (P:=(Col × Col) × E) (E:=LowerSpace E)
    (fun a : (Col × Col) × E => P.disclosedSample p r s a.1.1 a.1.2 coin a.2) hgyC
  have hgyArgs : Measurable (fun z : (Col × Col) × InnerQuery E => ((z.1,z.2.1),z.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have hgy' := hgy.comp hgyArgs
  have hu : Measurable (fun z : (Col × Col) × InnerQuery E => uProj E z.2.2) :=
    (uProj E).continuous.measurable.comp (measurable_snd.comp measurable_snd)
  exact (measurable_const.prodMk hfy').prodMk ((hu.const_smul (-P.L)).prodMk hgy')

theorem disclosedReply_measurable (p : ℝ) :
    Measurable (fun z :
      (((Fin (n+1) → E) × (Fin (n+1) → E)) × InnerQuery E) × ((ℕ × ℕ) × Bool) =>
      P.disclosedReply p z.2.1.1 z.2.1.2 z.1.1.1 z.1.1.2 z.1.2 z.2.2) :=
  measurable_from_prod_countable (fun t => P.disclosedReply_fixed_measurable p t.1.1 t.1.2 t.2)

end Bilevel.MultiscaleMean.Parameters
