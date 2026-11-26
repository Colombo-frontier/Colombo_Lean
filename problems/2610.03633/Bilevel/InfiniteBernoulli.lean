import Bilevel.SmallGapTesting
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Basic

/-! An actual countable product of an arbitrary private seed and independent
Bernoulli draws. Independence of each fresh draw from the whole finite past is
derived from the product measure, not supplied as a hypothesis. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Bilevel.InfiniteBernoulli

def Coordinate (Seed : Type) : Option ℕ → Type
  | none => Seed
  | some _ => Bool

instance {Seed : Type} [MeasurableSpace Seed] (i : Option ℕ) :
    MeasurableSpace (Coordinate Seed i) := by cases i <;> dsimp [Coordinate] <;> infer_instance

abbrev Sample (Seed : Type) := (i : Option ℕ) → Coordinate Seed i

variable {Seed : Type} [MeasurableSpace Seed]

def coordinateLaw (ν : Measure Seed) (p : ℝ) (hp : p ≤ 1) :
    (i : Option ℕ) → Measure (Coordinate Seed i)
  | none => ν
  | some _ => BernoulliOracle.law p hp

instance coordinateLaw_probability (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp : p ≤ 1) (i : Option ℕ) :
    IsProbabilityMeasure (coordinateLaw ν p hp i) := by
  cases i with
  | none => exact ‹IsProbabilityMeasure ν›
  | some n => exact BernoulliOracle.law_isProbability p hp

def law (ν : Measure Seed) [IsProbabilityMeasure ν] (p : ℝ) (hp : p ≤ 1) :
    Measure (Sample Seed) := Measure.infinitePi (coordinateLaw ν p hp)

instance law_probability (ν : Measure Seed) [IsProbabilityMeasure ν] (p : ℝ) (hp : p ≤ 1) :
    IsProbabilityMeasure (law ν p hp) := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))

theorem coordinate_measure (ν : Measure Seed) [IsProbabilityMeasure ν] (p : ℝ) (hp : p ≤ 1)
    (sets : (i : Option ℕ) → Set (Coordinate Seed i)) (i : Option ℕ)
    (hs : MeasurableSet (sets i)) :
    law ν p hp ((fun z : Sample Seed => z i) ⁻¹' sets i) = coordinateLaw ν p hp i (sets i) := by
  have h := Measure.infinitePi_pi (coordinateLaw ν p hp) (s := {i}) (t := sets)
    (by intro j hj; have he := Finset.mem_singleton.mp hj; subst j; exact hs)
  have he : Set.pi (↑({i} : Finset (Option ℕ))) sets = (fun z : Sample Seed => z i) ⁻¹' sets i := by
    ext z
    simp
  simpa only [he, Finset.prod_singleton, law] using h

theorem coordinates_independent (ν : Measure Seed) [IsProbabilityMeasure ν] (p : ℝ) (hp : p ≤ 1) :
    iIndepFun (fun i (z : Sample Seed) => z i) (law ν p hp) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hs
  have he : (⋂ i ∈ s, (fun z : Sample Seed => z i) ⁻¹' sets i) = Set.pi (s : Set (Option ℕ)) sets := by
    ext z
    simp
  rw [he, law, Measure.infinitePi_pi (coordinateLaw ν p hp) hs]
  apply Finset.prod_congr rfl
  intro i hi
  exact (coordinate_measure ν p hp sets i (hs i hi)).symm

def past (n : ℕ) : Finset (Option ℕ) := insert none ((Finset.range n).image some)

theorem none_mem_past (n : ℕ) : none ∈ past n := by simp [past]

theorem some_mem_past {n : ℕ} (i : Fin n) : some (i : ℕ) ∈ past n := by simp [past, i.isLt]

theorem fresh_not_mem_past (n : ℕ) : some n ∉ past n := by simp [past]

def decodePast (n : ℕ) (z : (i : past n) → Coordinate Seed i) : Seed × (Fin n → Bool) :=
  (z ⟨none, none_mem_past n⟩, fun i => z ⟨some i, some_mem_past i⟩)

theorem decodePast_measurable (n : ℕ) : Measurable (decodePast (Seed := Seed) n) :=
  (measurable_pi_apply (⟨none, none_mem_past n⟩ : past n)).prodMk
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (⟨some i, some_mem_past i⟩ : past n)))

def pastInput (n : ℕ) (z : Sample Seed) : Seed × (Fin n → Bool) := (z none, fun i => z (some i))

theorem pastInput_measurable (n : ℕ) : Measurable (pastInput (Seed := Seed) n) :=
  (measurable_pi_apply none).prodMk
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (some (i : ℕ))))

theorem prefix_fresh_independent (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp : p ≤ 1) (n : ℕ) :
    IndepFun (pastInput (Seed := Seed) n) (fun z : Sample Seed => z (some n)) (law ν p hp) := by
  have hd : Disjoint (past n) {some n} := Finset.disjoint_singleton_right.mpr (fresh_not_mem_past n)
  have hi := (coordinates_independent ν p hp).indepFun_finset (past n) {some n} hd
    (fun i => measurable_pi_apply i)
  exact hi.comp (decodePast_measurable n) (measurable_pi_apply ⟨some n, by simp⟩)

theorem fresh_probability (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1) (n : ℕ) :
    (law ν p hp).real {z : Sample Seed | z (some n) = true} = p := by
  let sets : (i : Option ℕ) → Set (Coordinate Seed i) := fun i =>
    match i with
    | none => Set.univ
    | some _ => {true}
  have h := coordinate_measure ν p hp sets (some n) (MeasurableSet.singleton true)
  change law ν p hp {z : Sample Seed | z (some n) = true} = BernoulliOracle.law p hp {true} at h
  rw [measureReal_def, h, SmallGapTesting.bernoulli_true, ENNReal.toReal_ofReal hp0]

end Bilevel.InfiniteBernoulli
