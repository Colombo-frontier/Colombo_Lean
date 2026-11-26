import RandomizedFO2003.Model
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace RandomizedFO2003.Model

open MeasureTheory

variable {d : ℕ} {Param : Type*} {Seed : Type} [MeasurableSpace Param] [MeasurableSpace Seed]

/-- Full-history interaction with a jointly measurable family of actual
first-order oracles is jointly measurable in the instance and private seed. -/
theorem measurable_transcript_family (A : Algorithm d Seed) (f : Param → Space d → ℝ)
    (hf : Measurable (fun p : Param × Space d => oracle (f p.1) p.2)) (t : ℕ) :
    Measurable (fun p : Param × Seed => transcript A (f p.1) p.2 t) := by
  induction t with
  | zero =>
    apply measurable_pi_lambda
    intro i
    exact i.elim0
  | succ t ih =>
    have hq := (A.query_measurable t).comp (measurable_snd.prodMk ih)
    have hr := hf.comp (measurable_fst.prodMk hq)
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [transcript, Fin.snoc_last] using hr
    · simpa only [transcript, Fin.snoc_castSucc] using (measurable_pi_apply j).comp ih

theorem measurable_query_family (A : Algorithm d Seed) (f : Param → Space d → ℝ)
    (hf : Measurable (fun p : Param × Space d => oracle (f p.1) p.2)) (t : ℕ) :
    Measurable (fun p : Param × Seed => A.query t p.2 (transcript A (f p.1) p.2 t)) :=
  (A.query_measurable t).comp
    (measurable_snd.prodMk (measurable_transcript_family A f hf t))

/-- The terminal point is the algorithm's unrestricted output. It is not
identified with any previously submitted query. -/
theorem measurable_output_family (A : Algorithm d Seed) (f : Param → Space d → ℝ)
    (hf : Measurable (fun p : Param × Space d => oracle (f p.1) p.2)) (t : ℕ) :
    Measurable (fun p : Param × Seed => A.output t p.2 (transcript A (f p.1) p.2 t)) :=
  (A.output_measurable t).comp
    (measurable_snd.prodMk (measurable_transcript_family A f hf t))

def familySuccess (A : Algorithm d Seed) (f : Param → Space d → ℝ) (ε : ℝ) (T : ℕ) :
    Set (Param × Seed) := {p | p.2 ∈ Success A (f p.1) ε T}

theorem measurableSet_familySuccess (A : Algorithm d Seed) (f : Param → Space d → ℝ)
    (hf : Measurable (fun p : Param × Space d => oracle (f p.1) p.2)) (ε : ℝ) (T : ℕ) :
    MeasurableSet (familySuccess A f ε T) := by
  have hg : Measurable (fun p : Param × Space d => gradient (f p.1) p.2) := hf.snd
  exact measurableSet_le
    (hg.comp (measurable_fst.prodMk (measurable_output_family A f hf T))).norm measurable_const

theorem measurableSet_success_section (A : Algorithm d Seed) (f : Param → Space d → ℝ)
    (hf : Measurable (fun p : Param × Space d => oracle (f p.1) p.2))
    (ε : ℝ) (T : ℕ) (p : Param) : MeasurableSet (Success A (f p) ε T) := by
  have hp : Measurable (fun seed : Seed => (p, seed)) := measurable_const.prodMk measurable_id
  have hm := (measurableSet_familySuccess A f hf ε T).preimage hp
  simpa only [familySuccess, Set.preimage_setOf_eq] using hm

end RandomizedFO2003.Model
