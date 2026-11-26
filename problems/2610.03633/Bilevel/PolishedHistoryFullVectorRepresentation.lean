import Bilevel.PolishedHistoryConditionalRepresentation
import Bilevel.PolishedHistoryModel

/-! Direct realization of the two full-vector conditional bounds as the
history-threaded SFO interface. The joint full-response distribution is
preserved after the exact public block-coordinate conversion. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful
set_option autoImplicit false

variable {U V Q H Ω : Type*} [MeasurableSpace U] [MeasurableSpace V]
  [MeasurableSpace Q] [MeasurableSpace H] [MeasurableSpace Ω]

/-- Taking a measurable coordinate of the same joint response preserves the
entering state and all correlation. -/
theorem compProd_map_right (π : Measure U) [IsProbabilityMeasure π]
    (K : Kernel U V) [IsMarkovKernel K]
    {W : Type*} [MeasurableSpace W] (f : V → W) (hf : Measurable f) :
    π ⊗ₘ K.map f=(π ⊗ₘ K).map (fun z => (z.1,f z.2)) := by
  ext s hs
  have hm : Measurable (fun z : U × V => (z.1,f z.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  rw [Measure.compProd_apply hs,Measure.map_apply hm hs,Measure.compProd_apply (hm hs)]
  congr with u
  rw [Kernel.map_apply' _ hf _ (measurable_prodMk_left hs)]
  rfl

variable (G : Geometry) {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The full conditional equations of `def:sfo`, on the actual entering
information, give an actual `HistorySFO` with both moments at every state.
Null-state repair leaves the entering-state/full-response joint law exactly
unchanged. `tf` and `tg` are the true full primitive gradients. -/
theorem one_call_fullVector_historySFO
    (state : Ω → Q × H) (obs : Ω → G.Reply)
    (hs : Measurable state) (ho : Measurable obs)
    (tf tg : Q → G.Query) (htf : Measurable tf) (htg : Measurable tg)
    (σf σg : ℝ)
    (hif : Integrable (fun ω => ‖(obs ω).1-tf (state ω).1‖^2) μ)
    (hig : Integrable (fun ω => ‖(obs ω).2-tg (state ω).1‖^2) μ)
    (hmf : Integrable (fun ω => (obs ω).1-tf (state ω).1) μ)
    (hmg : Integrable (fun ω => (obs ω).2-tg (state ω).1) μ)
    (hmef : μ[fun ω => (obs ω).1-tf (state ω).1 |
      MeasurableSpace.comap state inferInstance] =ᵐ[μ] 0)
    (hmeg : μ[fun ω => (obs ω).2-tg (state ω).1 |
      MeasurableSpace.comap state inferInstance] =ᵐ[μ] 0)
    (hvf : ∀ᵐ ω ∂μ, μ[fun ω => ‖(obs ω).1-tf (state ω).1‖^2 |
      MeasurableSpace.comap state inferInstance] ω≤σf^2)
    (hvg : ∀ᵐ ω ∂μ, μ[fun ω => ‖(obs ω).2-tg (state ω).1‖^2 |
      MeasurableSpace.comap state inferInstance] ω≤σg^2)
    (update : (Q × H) × G.Reply → H) (hu : Measurable update) :
    ∃ R : HistorySFO (Query:=Q) (History:=H) (X:=G.X) (Y:=G.Y) σf σg,
      (μ.map state) ⊗ₘ R.law=
        μ.map (fun ω => (state ω,splitResponse (obs ω))) ∧
      (∀ q,R.upper.truth_x q=(tf q).1) ∧
      (∀ q,R.upper.truth_y q=(tf q).2) ∧
      (∀ q,R.lower.truth_x q=(tg q).1) ∧
      (∀ q,R.lower.truth_y q=(tg q).2) := by
  let ef : (Q × H) × G.Reply → G.Query := fun z => z.2.1-tf z.1.1
  let eg : (Q × H) × G.Reply → G.Query := fun z => z.2.2-tg z.1.1
  have hef : Measurable ef :=
    (measurable_fst.comp measurable_snd).sub
      (htf.comp (measurable_fst.comp measurable_fst))
  have heg : Measurable eg :=
    (measurable_snd.comp measurable_snd).sub
      (htg.comp (measurable_fst.comp measurable_fst))
  let fallback : Q × H → G.Reply := fun s => (tf s.1,tg s.1)
  have hf : Measurable fallback := (htf.comp measurable_fst).prodMk (htg.comp measurable_fst)
  let K := conditionalPairedKernel (μ:=μ) state obs ef eg σf σg hef heg fallback hf
  have hr := one_call_paired_representation state obs hs ho ef eg σf σg
    hef heg fallback hf (fun _ => sub_self _) (fun _ => sub_self _)
    hif hig hmf hmg hmef hmeg hvf hvg
  let R := HistorySFO.ofFullVectorKernel K tf tg htf htg σf σg
    (fun q h => (hr.1 (q,h)).1) (fun q h => (hr.1 (q,h)).2) update hu
  refine ⟨R,?_,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩
  change (μ.map state) ⊗ₘ K.map splitResponse=_
  haveI : IsProbabilityMeasure (μ.map state) := isProbabilityMeasure_map hs.aemeasurable
  rw [compProd_map_right _ _ _ splitResponse_measurable,hr.2]
  have hm : Measurable (fun z : (Q × H) × G.Reply => (z.1,splitResponse z.2)) :=
    measurable_fst.prodMk (splitResponse_measurable.comp measurable_snd)
  exact (Measure.map_map hm (hs.prodMk ho))

end Bilevel.PolishedHistory
