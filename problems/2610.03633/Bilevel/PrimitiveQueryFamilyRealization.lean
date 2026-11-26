import Bilevel.PrimitiveQueryFamily

/-! Source-family adapters need only identify the actual full reply and the
actual hyperobjective loss. No independent information event or minimax
assumption is hidden in the conversion to the common query model. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PrimitiveQuery
open BorelAdaptive
set_option autoImplicit false
variable {G : Geometry} {Index Seed : Type} [MeasurableSpace Seed]
  {ν : Measure Seed} [IsProbabilityMeasure ν] {μ L ρ Δ R₀ σf σg : ℝ}
  (F : Family G Index Seed ν μ L ρ Δ R₀ σf σg)

theorem Family.rateProperty_of_original (reply : Index → G.Query → Seed → G.Reply)
    (loss : Index → G.X → ℝ) (ε rate : ℝ)
    (hr : ∀ i q c,F.reply i q c=reply i q c) (hl : ∀ i x,F.loss i x=loss i x)
    (h : ∀ A : Algorithm G,
      (∀ i,(∫⁻ z,ENNReal.ofReal (loss i (seededStopped A.program reply A.start (i,z)).2)
        ∂A.privateLaw.prod (IndependentStream.law ν))≤ENNReal.ofReal ε) →
      ∃ i,ENNReal.ofReal rate≤∫⁻ z,seededCalls A.program reply A.start (i,z)
        ∂A.privateLaw.prod (IndependentStream.law ν)) : F.RateProperty ε rate := by
  have hr' : F.reply=reply := funext (fun i => funext (fun q => funext (hr i q)))
  have hl' : F.loss=loss := funext (fun i => funext (hl i))
  simpa only [Family.RateProperty,hr',hl'] using h

theorem Family.conservative_of_potentials
    (f g : Index → Seed → G.Query → ℝ)
    (hf : ∀ i c,Differentiable ℝ (f i c)) (hg : ∀ i c,Differentiable ℝ (g i c))
    (hreply : ∀ i q c,F.reply i q c=(gradient (f i c) q,gradient (g i c) q)) :
    ∀ i,(F.instance i).IsConservative := by
  intro i c
  refine ⟨f i c,g i c,?_,?_⟩
  · intro q
    have he := congrArg Prod.fst (hreply i q c)
    change (F.upper i).sample q c=gradient (f i c) q at he
    change HasGradientAt (f i c) ((F.upper i).sample q c) q
    rw [he]
    exact (hf i c q).hasGradientAt
  · intro q
    have he := congrArg Prod.snd (hreply i q c)
    change (F.lower i).sample q c=gradient (g i c) q at he
    change HasGradientAt (g i c) ((F.lower i).sample q c) q
    rw [he]
    exact (hg i c q).hasGradientAt

theorem Family.curvature_of_mean (mean : Index → G.X → ℝ) (Λ : ℝ)
    (hm : ∀ i x,(F.primitive i).hyperobjective (F.response i) x=mean i x)
    (hL : ∀ i x x',‖gradient (mean i) x-gradient (mean i) x'‖≤Λ*‖x-x'‖) :
    ∀ i,(F.instance i).CurvatureBound Λ := by
  intro i x x'
  change ‖gradient ((F.primitive i).hyperobjective (F.response i)) x-
    gradient ((F.primitive i).hyperobjective (F.response i)) x'‖≤Λ*‖x-x'‖
  rw [funext (hm i)]
  exact hL i x x'

theorem independentStream_unit :
    IndependentStream.law (Measure.dirac ())=Measure.dirac (fun _ : ℕ => ()) := by
  have he : (fun s : ℕ → Unit => s)=(fun _ => (fun _ : ℕ => ())) :=
    funext (fun s => Subsingleton.elim _ _)
  have hm := Measure.map_const (μ:=IndependentStream.law (Measure.dirac ())) (fun _ : ℕ => ())
  rw [← he] at hm
  change Measure.map id (IndependentStream.law (Measure.dirac ()))=_ at hm
  simpa only [Measure.map_id,measure_univ,one_smul] using hm

end Bilevel.PrimitiveQuery
