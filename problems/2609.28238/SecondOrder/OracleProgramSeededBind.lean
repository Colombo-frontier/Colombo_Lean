import SecondOrder.OracleProgramSeededKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O O' Ω S T : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace O'] [MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T]

theorem seededOutputLaw_bind_fixed (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (o₀' : O') (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p)
    (N : ℕ) (hN : ∀ s, UsesAtMost N (p s))
    (f : O → OracleProgram Q Y O') (hf : MeasurableFamily q₀ o₀' f)
    (M : ℕ) (hM : ∀ o, UsesAtMost M (f o)) :
    seededOutputLaw μ η q₀ o₀' reply (fun s => bind (p s) f) (N+M)=
      (seededOutputLaw μ η q₀ o₀ reply p N).bind
        (outputKernel μ q₀ y₀ o₀' a₀ reply hr f hf M) := by
  have hfull := hp.bind (f := fun _ o => f o)
    (hf.comp (fun w : S × O => w.2) measurable_snd)
  rw [seededOutputLaw_eq_bind μ η q₀ y₀ o₀' a₀ reply hr _ hfull (N+M),
    seededOutputLaw_eq_bind μ η q₀ y₀ o₀ a₀ reply hr p hp N,
    Measure.bind_bind (outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N).measurable.aemeasurable
      (outputKernel μ q₀ y₀ o₀' a₀ reply hr f hf M).measurable.aemeasurable]
  apply congrArg (fun k : S → Measure O' => η.bind k)
  funext s
  exact outputLaw_bind_of_usesAtMost μ q₀ y₀ o₀ o₀' a₀ reply hr (p s)
    (hp.comp (fun _ : Unit => s) measurable_const) N (hN s) f hf M hM

/-- Independent private seeds may be sampled in advance. After any bounded
first program, the continuation has its own fresh seed and oracle samples. -/
theorem seededOutputLaw_bind_of_usesAtMost
    (μ : Measure Ω) (η : Measure S) (θ : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] [IsProbabilityMeasure θ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (o₀' : O') (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p)
    (N : ℕ) (hN : ∀ s, UsesAtMost N (p s))
    (f : O × T → OracleProgram Q Y O') (hf : MeasurableFamily q₀ o₀' f)
    (M : ℕ) (hM : ∀ w, UsesAtMost M (f w)) :
    seededOutputLaw μ (η.prod θ) q₀ o₀' reply
      (fun w => bind (p w.1) (fun o => f (o,w.2))) (N+M)=
      (seededOutputLaw μ η q₀ o₀ reply p N).bind
        (seededOutputKernel μ θ q₀ y₀ o₀' a₀ reply hr f hf M) := by
  let K := outputKernel μ q₀ y₀ o₀' a₀ reply hr f hf M
  let H := seededOutputKernel μ θ q₀ y₀ o₀' a₀ reply hr f hf M
  let J := outputKernel μ q₀ y₀ o₀ a₀ reply hr p hp N
  have hfull := (hp.comp (fun w : S × T => w.1) measurable_fst).bind
    (f := fun w o => f (o,w.2))
    (hf.comp (fun w : (S × T) × O => (w.2,w.1.2))
      (measurable_snd.prodMk measurable_fst.snd))
  let G := outputKernel μ q₀ y₀ o₀' a₀ reply hr
    (fun w : S × T => bind (p w.1) (fun o => f (o,w.2))) hfull (N+M)
  rw [seededOutputLaw_eq_bind μ (η.prod θ) q₀ y₀ o₀' a₀ reply hr _ hfull (N+M),
    seededOutputLaw_eq_bind μ η q₀ y₀ o₀ a₀ reply hr p hp N]
  change (η.prod θ).bind G=(η.bind J).bind H
  ext e he
  rw [Measure.bind_apply he G.measurable.aemeasurable,
    Measure.bind_apply he H.measurable.aemeasurable,
    Measure.lintegral_bind J.measurable.aemeasurable (H.measurable_coe he).aemeasurable,
    lintegral_prod _ (G.measurable_coe he).aemeasurable]
  apply lintegral_congr
  intro s
  have hpoint (t : T) : G (s,t) e=∫⁻ o, K (o,t) e ∂J s := by
    have hps := hp.comp (fun _ : Unit => s) measurable_const
    have hft := hf.comp (fun o : O => (o,t)) (measurable_id.prodMk measurable_const)
    have hh := outputLaw_bind_of_usesAtMost μ q₀ y₀ o₀ o₀' a₀ reply hr
      (p s) hps N (hN s) (fun o => f (o,t)) hft M (fun o => hM (o,t))
    change outputLaw μ q₀ o₀' reply (bind (p s) (fun o => f (o,t))) (N+M) e=_
    rw [hh,Measure.bind_apply he
      (outputKernel μ q₀ y₀ o₀' a₀ reply hr (fun o => f (o,t)) hft M).measurable.aemeasurable]
    rfl
  simp_rw [hpoint]
  have hk : Measurable (fun w : T × O => K (w.2,w.1) e) :=
    (K.measurable_coe he).comp measurable_swap
  rw [lintegral_lintegral_swap hk.aemeasurable]
  apply lintegral_congr
  intro o
  exact (seededOutputKernel_apply_set μ θ q₀ y₀ o₀' a₀ reply hr f hf M o e he).symm

end
end OracleProgram
end SecondOrder
