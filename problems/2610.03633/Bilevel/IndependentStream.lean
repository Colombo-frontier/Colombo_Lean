import Bilevel.IndependentDraws
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Basic

/-! A countable supply of independent original seeds. Every finite prefix has
exactly the nested product law used by the executed finite solvers. This gives
a common sample space when the required finite call count depends on a query. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.IndependentStream

open IndependentDraws

variable {Seed : Type*} [MeasurableSpace Seed]

abbrev Stream (Seed : Type*) := ℕ → Seed

def law (ν : Measure Seed) [IsProbabilityMeasure ν] : Measure (Stream Seed) :=
  Measure.infinitePi (fun _ : ℕ => ν)

instance law_probability (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (law ν) := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))

def fromVector : (n : ℕ) → (Fin n → Seed) → Draws Seed n
  | 0, _ => PUnit.unit
  | n + 1, z => (fromVector n (fun i => z i.castSucc), z (Fin.last n))

theorem fromVector_measurable (n : ℕ) : Measurable (fromVector (Seed := Seed) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc))).prodMk
      (measurable_pi_apply (Fin.last n))

def project (n : ℕ) (z : Stream Seed) : Draws Seed n := fromVector n (fun i => z i)

theorem project_measurable (n : ℕ) : Measurable (project (Seed := Seed) n) :=
  (fromVector_measurable n).comp (measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ)))

omit [MeasurableSpace Seed] in
theorem project_succ (n : ℕ) (z : Stream Seed) : project (n + 1) z = (project n z, z n) := rfl

variable (ν : Measure Seed) [IsProbabilityMeasure ν]

theorem coordinate_measure (i : ℕ) (s : Set Seed) (hs : MeasurableSet s) :
    law ν ((fun z : Stream Seed => z i) ⁻¹' s) = ν s := by
  have h := Measure.infinitePi_pi (fun _ : ℕ => ν) (s := {i}) (t := fun _ => s)
    (by intro j hj; exact hs)
  have he : Set.pi (↑({i} : Finset ℕ)) (fun _ : ℕ => s) =
      (fun z : Stream Seed => z i) ⁻¹' s := by ext z; simp
  simpa only [he, Finset.prod_singleton, law] using h

theorem coordinate_preserves (i : ℕ) :
    MeasurePreserving (fun z : Stream Seed => z i) (law ν) ν := by
  refine ⟨measurable_pi_apply i, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  exact coordinate_measure ν i s hs

theorem coordinates_independent : iIndepFun (fun i (z : Stream Seed) => z i) (law ν) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hs
  have he : (⋂ i ∈ s, (fun z : Stream Seed => z i) ⁻¹' sets i) = Set.pi (s : Set ℕ) sets := by
    ext z
    simp
  rw [he, law, Measure.infinitePi_pi (fun _ : ℕ => ν) hs]
  apply Finset.prod_congr rfl
  intro i hi
  exact (coordinate_measure ν i (sets i) (hs i hi)).symm

def decodePast (n : ℕ) (z : (Finset.range n) → Seed) : Draws Seed n :=
  fromVector n (fun i => z ⟨i, Finset.mem_range.mpr i.isLt⟩)

theorem decodePast_measurable (n : ℕ) : Measurable (decodePast (Seed := Seed) n) :=
  (fromVector_measurable n).comp (measurable_pi_lambda _ (fun i =>
    measurable_pi_apply (⟨i, Finset.mem_range.mpr i.isLt⟩ : Finset.range n)))

theorem prefix_fresh_independent (n : ℕ) :
    IndepFun (project (Seed := Seed) n) (fun z : Stream Seed => z n) (law ν) := by
  have hd : Disjoint (Finset.range n) {n} := Finset.disjoint_singleton_right.mpr (by simp)
  have hi := (coordinates_independent ν).indepFun_finset (Finset.range n) {n} hd
    (fun i => measurable_pi_apply i)
  exact hi.comp (decodePast_measurable n) (measurable_pi_apply ⟨n, by simp⟩)

/-- The first n stream seeds are precisely n independent original draws. -/
theorem project_preserves (n : ℕ) :
    MeasurePreserving (project (Seed := Seed) n) (law ν) (IndependentDraws.law ν n) := by
  refine ⟨project_measurable n, ?_⟩
  induction n with
  | zero =>
    change Measure.map (fun _ : Stream Seed => PUnit.unit) (law ν) = Measure.dirac PUnit.unit
    simp only [Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    have hi := (indepFun_iff_map_prod_eq_prod_map_map
      (project_measurable (Seed := Seed) n).aemeasurable
      (measurable_pi_apply n).aemeasurable).mp (prefix_fresh_independent ν n)
    simpa only [project_succ, ih, (coordinate_preserves ν n).map_eq, IndependentDraws.law] using hi

end Bilevel.IndependentStream
