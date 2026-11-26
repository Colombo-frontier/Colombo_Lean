import Bilevel.PolishedLiteralOriginalFresh
import Bilevel.ParametricGradientMeasurable

/-! A continuous scalar extension of the actual hyperobjective to every
raw column array. It supplies the joint Borel gradient needed for the
same-prior expected-cost specialization without selecting completions
of invalid arrays. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteralActualObserver
open PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (P : PolishedLiteral.Parameters (X:=X) (U:=U))

def rawOuterMean (κ : ℝ) (a : P.MacroColumns) (b : P.MicroColumns) (z : Joint X U) : ℝ :=
  P.rawExactUpper (P.macroNode.n+1) (fun _ => P.n+1) a b
    (pack (pack z.fst 0) (pack (κ • z.snd) 0))+
  P.rawSelectedResidual (P.macroNode.n+1) (fun _ => P.n+1) a b (pack z.fst (κ • z.snd))

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawOuterMean_continuous (κ : ℝ) :
    Continuous (fun z : (P.MacroColumns × P.MicroColumns) × Joint X U => rawOuterMean P κ z.1.1 z.1.2 z.2) := by
  have ha : Continuous (fun z : (P.MacroColumns × P.MicroColumns) × Joint X U => z.1.1) := continuous_fst.comp continuous_fst
  have hb : Continuous (fun z : (P.MacroColumns × P.MicroColumns) × Joint X U => z.1.2) := continuous_snd.comp continuous_fst
  have hx : Continuous (fun z : (P.MacroColumns × P.MicroColumns) × Joint X U => z.2.fst) :=
    PolishedLiteral.fstMap.continuous.comp continuous_snd
  have hu : Continuous (fun z : (P.MacroColumns × P.MicroColumns) × Joint X U => κ • z.2.snd) :=
    (PolishedLiteral.sndMap.continuous.comp continuous_snd).const_smul κ
  have hq : Continuous (fun z : (P.MacroColumns × P.MicroColumns) × Joint X U =>
      pack (pack z.2.fst (0:U)) (pack (κ • z.2.snd) (0:ℝ))) :=
    packLinear.continuous.comp ((packLinear.continuous.comp (hx.prodMk continuous_const)).prodMk
      (packLinear.continuous.comp (hu.prodMk continuous_const)))
  exact (P.rawExactUpper_continuous _ _ _ _ _ ha hb hq).add
    (P.rawSelectedResidual_continuous _ _ _ _ _ _ ha hb hx hu)

theorem rawOuterMean_eq_outerMean (κ : ℝ) (a : P.MacroColumns) (b : P.MicroColumns)
    (ha : ∀ j,a j=P.macroNode.frame (ChiBoundedChain.basis j))
    (hb : ∀ i j,b i j=P.frames i (ChiBoundedChain.basis j)) :
    rawOuterMean P κ a b=P.outerMean κ := by
  have hm (x : X) : ChiPrefixEvaluation.readout P.macroNode.n (P.macroNode.n+1) P.macroNode.radius a x=
      P.macroNode.coordinates x := by
    rw [ChiPrefixEvaluation.readout_eq_retained _ _ _ _ _ (fun j _ => ha j)]
    exact PolishedLiteral.retain_full le_rfl _
  have hu (i : Fin (P.macroNode.n+1)) (u : U) : P.rawMicro (fun _ => P.n+1) b i u=P.coordinates i u := by
    unfold PolishedLiteral.Parameters.rawMicro
    rw [ChiPrefixEvaluation.readout_eq_retained _ _ _ _ _ (fun j _ => hb i j)]
    exact PolishedLiteral.retain_full le_rfl _
  have hua (i : Fin (P.macroNode.n+1)) (u : U) :
      P.rawMicro (P.activeCutCounts (P.macroNode.n+1) (fun _ => P.n+1)) b i u=P.coordinates i u := by
    unfold PolishedLiteral.Parameters.rawMicro
    rw [ChiPrefixEvaluation.readout_eq_retained _ _ _ _ _ (fun j _ => hb i j)]
    apply PolishedLiteral.retain_full
    simp only [PolishedLiteral.Parameters.activeCutCounts,if_pos (Nat.le_of_lt i.isLt)]
    omega
  have hs (i : Fin (P.macroNode.n+1)) (x : X) : P.rawSelector (P.macroNode.n+1) a i x=
      PolishedLiteral.wrappedSelector P.macroNode i x := by
    unfold PolishedLiteral.Parameters.rawSelector PolishedLiteral.wrappedSelector
    rw [hm]
  funext z
  rw [PolishedLiteral.Parameters.outerMean,←P.exact_cancellation]
  unfold rawOuterMean
  congr 1
  · rw [P.upperBase_closed_formula]
    simp only [PolishedLiteral.Parameters.rawExactUpper,PolishedLiteral.Parameters.rawRelease,
      PolishedLiteral.packed_fst,PolishedLiteral.packed_snd,hs,hm,hu,
      PolishedLiteral.Parameters.microRelease,PolishedLiteral.Parameters.terminal,mul_zero,add_zero]
  · simp only [PolishedLiteral.Parameters.rawSelectedResidual,PolishedLiteral.Parameters.selectedResidual,
      PolishedLiteral.Parameters.microResidual,PolishedLiteral.packed_fst,PolishedLiteral.packed_snd,hs,hua]

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ U]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace (Joint X U)] [BorelSpace (Joint X U)]

theorem rawOuterMean_gradient_measurable (κ : ℝ) :
    Measurable (fun z : (P.MacroColumns × P.MicroColumns) × Joint X U => gradient (rawOuterMean P κ z.1.1 z.1.2) z.2) :=
  ParametricGradient.gradient_measurable (fun p : P.MacroColumns × P.MicroColumns => rawOuterMean P κ p.1 p.2)
    (rawOuterMean_continuous P κ)

end Bilevel.PolishedLiteralActualObserver
