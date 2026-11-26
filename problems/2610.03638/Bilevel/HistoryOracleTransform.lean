import Bilevel.HistoryOracle

/-! Known transformations of original calls, preserving their history and
conditional variance. Query-dependent tilts use deterministic postprocessing
of the very same original observation. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful.HistoryOracle
variable {Query Query' History Obs E : Type*} [MeasurableSpace Query] [MeasurableSpace Query']
  [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

def requery (q : Query' → Query) (hq : Measurable q) :
    HistoryOracle (Query := Query') (History := History) (Obs := Obs) (E := E) σ where
  law := O.law.comap (fun z => (q z.1,z.2)) ((hq.comp measurable_fst).prodMk measurable_snd)
  markov := inferInstance
  read := O.read
  read_measurable := O.read_measurable
  truth := O.truth ∘ q
  truth_measurable := O.truth_measurable.comp hq
  update := fun z => O.update ((q z.1.1,z.1.2),z.2)
  update_measurable := O.update_measurable.comp
    (((hq.comp (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  square_integrable p h := O.square_integrable (q p) h
  mean p h := O.mean (q p) h
  variance p h := O.variance (q p) h

def recordQuery (z : (Query × History) × Obs) : Query × Obs := (z.1.1,z.2)

theorem recordQuery_measurable : Measurable (recordQuery (Query := Query) (History := History) (Obs := Obs)) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

def shiftedLaw : Kernel (Query × History) (Query × Obs) := KernelMap.dependent O.law recordQuery

instance shiftedLaw_markov : IsMarkovKernel O.shiftedLaw :=
  KernelMap.dependent_markov _ _ recordQuery_measurable

omit [BorelSpace E] [SecondCountableTopology E] in
theorem shiftedLaw_apply (q : Query) (h : History) :
    O.shiftedLaw (q,h) = (O.law (q,h)).map (fun o => (q,o)) :=
  KernelMap.dependent_apply _ _ recordQuery_measurable _

def shift (a : Query → E) (ha : Measurable a) :
    HistoryOracle (Query := Query) (History := History) (Obs := Query × Obs) (E := E) σ where
  law := O.shiftedLaw
  markov := inferInstance
  read := fun z => O.read z.2 + a z.1
  read_measurable := (O.read_measurable.comp measurable_snd).add (ha.comp measurable_fst)
  truth := fun q => O.truth q + a q
  truth_measurable := O.truth_measurable.add ha
  update := fun z => O.update (z.1,z.2.2)
  update_measurable := O.update_measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  square_integrable q h := by
    rw [O.shiftedLaw_apply]
    have hm : Measurable (fun z : Query × Obs => ‖O.read z.2+a z.1-(O.truth q+a q)‖ ^ 2) :=
      (((O.read_measurable.comp measurable_snd).add (ha.comp measurable_fst)).sub measurable_const).norm.pow_const 2
    apply (integrable_map_measure hm.aestronglyMeasurable measurable_prodMk_left.aemeasurable).mpr
    change Integrable (fun o => ‖O.read o+a q-(O.truth q+a q)‖ ^ 2) (O.law (q,h))
    simpa only [add_sub_add_right_eq_sub] using O.square_integrable q h
  mean q h := by
    rw [O.shiftedLaw_apply]
    have hm : Measurable (fun z : Query × Obs => O.read z.2+a z.1-(O.truth q+a q)) :=
      ((O.read_measurable.comp measurable_snd).add (ha.comp measurable_fst)).sub measurable_const
    rw [integral_map measurable_prodMk_left.aemeasurable hm.aestronglyMeasurable]
    simpa only [add_sub_add_right_eq_sub] using O.mean q h
  variance q h := by
    rw [O.shiftedLaw_apply]
    have hm : Measurable (fun z : Query × Obs => ‖O.read z.2+a z.1-(O.truth q+a q)‖ ^ 2) :=
      (((O.read_measurable.comp measurable_snd).add (ha.comp measurable_fst)).sub measurable_const).norm.pow_const 2
    rw [integral_map measurable_prodMk_left.aemeasurable hm.aestronglyMeasurable]
    simpa only [add_sub_add_right_eq_sub] using O.variance q h

end Bilevel.Stateful.HistoryOracle
