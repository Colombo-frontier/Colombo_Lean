import Bilevel.MultiscaleDisclosedBorel

/-! The original full reply and actual mean loss are jointly Borel in
the sampled frame and query. The proof uses all columns only to identify
the original law; the execution evaluator still uses disclosed prefixes. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean ChiPrefixEvaluation ZeroChain WrappedChain
set_option autoImplicit false
set_option maxHeartbeats 120000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (P : Parameters (E:=E) n)

def innerDisclosedMean (columns : Fin (n+1) → E) (x : E) : ℝ :=
  P.disclosedRevealed (n+1) columns ((P.L/P.μ) • x)+
    P.disclosedResidual (n+1) columns ((P.L/P.μ) • x)

omit [CompleteSpace E] in
theorem innerDisclosedMean_continuous :
    Continuous (fun z : (Fin (n+1) → E) × E => innerDisclosedMean P z.1 z.2) := by
  have hg : Continuous (fun z : (Fin (n+1) → E) × E => (P.L/P.μ) • z.2) :=
    continuous_const.smul continuous_snd
  have hargs : Continuous (fun z : (Fin (n+1) → E) × E => (z.1,(P.L/P.μ) • z.2)) :=
    continuous_fst.prodMk hg
  have h := ((P.disclosedRevealed_continuous (n+1)).comp hargs).add
    ((P.disclosedResidual_continuous (n+1)).comp hargs)
  exact h

theorem innerDisclosedMean_full (V : Space n →ₗᵢ[ℝ] E) :
    innerDisclosedMean P (fun k => V (basis k))=(P.withFrame V).realized := by
  have hr (u : E) : readout n (n+1) P.R (fun k => V (basis k)) u=coordinates n P.R V u := by
    ext k
    rw [readout_apply,if_pos k.isLt,coordinates_inner]
    rfl
  funext x
  change ZeroChainResidualScaled.A n P.amplitude P.β
      (readout n (n+1) P.R (fun k => V (basis k)) ((P.L/P.μ) • x))+
    RadialWrapper.bowl P.ν P.R ((P.L/P.μ) • x)+
    ZeroChainResidualScaled.R n P.amplitude P.β
      (readout n (n+1) P.R (fun k => V (basis k)) ((P.L/P.μ) • x))=_
  rw [hr]
  have hh := ZeroChainResidualScaled.exact_split n P.amplitude P.β
    (coordinates n P.R V ((P.L/P.μ) • x))
  change _=ScaledZeroChain.value n P.amplitude P.β (coordinates n P.R V ((P.L/P.μ) • x))+
    RadialWrapper.bowl P.ν P.R ((P.L/P.μ) • x)
  linarith only [hh]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)]

omit [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)] in
theorem innerDisclosedMean_gradient_measurable :
    Measurable (fun z : (Fin (n+1) → E) × E => gradient (innerDisclosedMean P z.1) z.2) :=
  ParametricGradient.gradient_measurable (innerDisclosedMean P) (innerDisclosedMean_continuous P)

omit [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)] in
theorem innerOriginalLoss_frame_measurable {I : Type*} [MeasurableSpace I]
    (V : I → Space n →ₗᵢ[ℝ] E)
    (hV : Measurable (fun i => fun k => V i (basis k))) :
    Measurable (fun z : I × E => innerOriginalLoss (P.withFrame (V z.1)) z.2) := by
  have hh := (innerDisclosedMean_gradient_measurable P).comp
    ((hV.comp measurable_fst).prodMk measurable_snd)
  have hnorm := hh.norm
  simpa only [Function.comp_apply,innerDisclosedMean_full,innerOriginalLoss] using hnorm

theorem innerOriginalReply_frame_measurable {I : Type*} [MeasurableSpace I]
    (V : I → Space n →ₗᵢ[ℝ] E)
    (hV : Measurable (fun i => fun k => V i (basis k))) (p : ℝ) :
    Measurable (fun z : I × (InnerQuery E × Bool) =>
      innerOriginalReply (P.withFrame (V z.1)) p z.2.1 z.2.2) := by
  let Col := Fin (n+1) → E
  have hcols : Measurable (fun z : I × (InnerQuery E × Bool) =>
      (fun k => V z.1 (basis k))) := hV.comp measurable_fst
  have hb : Measurable (fun z : I × (InnerQuery E × Bool) => z.2.2) :=
    measurable_snd.comp measurable_snd
  have hnext : Measurable (fun z : I × (InnerQuery E × Bool) => n+1+if z.2.2 then 1 else 0) :=
    (measurable_of_finite (fun b : Bool => n+1+if b then 1 else 0)).comp hb
  have hargs : Measurable (fun z : I × (InnerQuery E × Bool) =>
      ((((fun k => V z.1 (basis k)),(fun k => V z.1 (basis k))),z.2.1),
        ((n+1,n+1+if z.2.2 then 1 else 0),z.2.2))) :=
    ((hcols.prodMk hcols).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_const.prodMk hnext).prodMk hb)
  have hh := (P.disclosedReply_measurable p).comp hargs
  convert hh using 1
  funext z
  have he := (P.withFrame (V z.1)).original_eq_disclosed_reply p (n+1)
    (fun k => V z.1 (basis k)) (fun k => V z.1 (basis k)) z.2.2
    (fun _ _ => rfl) (fun _ _ _ => rfl) z.2.1
    (fun k hk => by omega)
  exact he

end Bilevel.MultiscaleMean
