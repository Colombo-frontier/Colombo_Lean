import Bilevel.PolishedHistoryModel

/-! The stationary fresh-seed class is embedded without changing the
primitive, retained response, loss, gap, initialization, or paired response
kernel. Path-law and stopping-law identifications are proved separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
open PrimitiveQuery Stateful PrimitiveGeometry
set_option autoImplicit false
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}

def ofStationary (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) :
    Instance G μ L ρ Δ R₀ σf σg where
  primitive := I.primitive
  response := I.response
  x₀ := 0
  yinit := 0
  gap := I.gap
  initialization := by simpa only [zero_sub,norm_neg] using I.initialization
  History := Unit
  initialHistory := ()
  oracle := I.historySFO
  truth_fx := fun x y => I.historySFO_fx_truth (x,y)
  truth_fy := fun x y => I.historySFO_fy_truth (x,y)
  truth_gx := fun x y => I.historySFO_gx_truth (x,y)
  truth_gy := fun x y => I.historySFO_gy_truth (x,y)

variable (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg)

@[simp] theorem ofStationary_loss (x : G.X) : (ofStationary I).loss x=I.loss x := rfl

@[simp] theorem ofStationary_packedLaw (q : G.Query) (h : Unit) :
    (ofStationary I).packedLaw (q,h)=I.law.map (I.reply () q) := by
  cases h
  rw [Instance.packedLaw_apply]
  change (I.historySFO.law (PrimitiveQuery.unpack q,())).map packResponse = _
  have hr : Measurable (I.fullResponse (PrimitiveQuery.unpack q)) :=
    I.fullResponse_measurable.comp (measurable_const.prodMk measurable_id)
  rw [I.historySFO_law,Measure.map_map packResponse_measurable hr]
  rfl

@[simp] theorem ofStationary_packedUpdate
    (z : (G.Query × Unit) × G.Reply) : (ofStationary I).packedUpdate z=() := rfl

theorem ofStationary_isConservative (h : I.IsConservative) :
    (ofStationary I).IsConservative := by
  refine ⟨{
    Seed := I.Seed
    measurableSeed := I.measurableSeed
    law := Kernel.const (G.Query × Unit) I.law
    markov := ⟨fun _ => I.probability⟩
    sample := fun _ q c => I.reply () q c
    sample_measurable := ?_
    law_eq := ?_
    potential := fun _ c => h c }⟩
  · exact (I.upper.sample_measurable.prodMk I.lower.sample_measurable).comp measurable_snd
  · intro q h
    rw [ofStationary_packedLaw]
    rfl

theorem ofStationary_curvature_iff (Λ : ℝ) :
    (ofStationary I).CurvatureBound Λ ↔ I.CurvatureBound Λ := Iff.rfl

end Bilevel.PolishedHistory
