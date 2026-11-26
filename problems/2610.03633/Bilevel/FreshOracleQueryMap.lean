import Bilevel.FreshOracle

/-! Measurable query reparametrization leaves each full sample and all
pointwise SFO moment bounds unchanged. -/
noncomputable section
namespace Bilevel.FreshOracle.Oracle
set_option autoImplicit false
open MeasureTheory
variable {Q Q' Seed E : Type*} [MeasurableSpace Q] [MeasurableSpace Q'] [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure Seed} {σ : ℝ}

def reparametrize (O : Oracle (Query:=Q) (E:=E) ν σ) (f : Q' → Q) (hf : Measurable f) :
    Oracle (Query:=Q') (E:=E) ν σ where
  truth := O.truth ∘ f
  sample := fun q s => O.sample (f q) s
  truth_measurable := O.truth_measurable.comp hf
  sample_measurable := O.sample_measurable.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  square_integrable := fun q => O.square_integrable (f q)
  mean := fun q => O.mean (f q)
  variance := fun q => O.variance (f q)

end Bilevel.FreshOracle.Oracle
