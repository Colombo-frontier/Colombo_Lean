import Bilevel.IndependentStream

/-! Splitting the actual iid oracle stream into one fresh draw and its remaining
stream. This is a measure-preserving identity, not a realization axiom. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Bilevel.IndependentStream

variable {Seed : Type*} [MeasurableSpace Seed]

def tail (x : Stream Seed) : Stream Seed := fun n => x (n+1)

def cons (x : Seed × Stream Seed) : Stream Seed := fun n =>
  match n with
  | 0 => x.1
  | n+1 => x.2 n

theorem tail_measurable : Measurable (tail (Seed:=Seed)) :=
  measurable_pi_lambda _ (fun n => measurable_pi_apply (n+1))

theorem cons_measurable : Measurable (cons (Seed:=Seed)) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

def split (x : Stream Seed) : Seed × Stream Seed := (x 0,tail x)

theorem split_measurable : Measurable (split (Seed:=Seed)) :=
  (measurable_pi_apply 0).prodMk tail_measurable

omit [MeasurableSpace Seed] in
theorem split_cons (x : Seed × Stream Seed) : split (cons x)=x := rfl

omit [MeasurableSpace Seed] in
theorem cons_split (x : Stream Seed) : cons (split x)=x := by
  funext n
  cases n <;> rfl

private def tailIndices (s : Finset ℕ) : Finset ℕ :=
  s.preimage Nat.succ Nat.succ_injective.injOn

private theorem tailIndices_image (s : Finset ℕ) :
    (tailIndices s).image Nat.succ=s.erase 0 := by
  ext n
  cases n with
  | zero => simp [tailIndices]
  | succ n => simp [tailIndices]

private theorem prod_split (s : Finset ℕ) (f : ℕ → ℝ≥0∞) :
    ∏ i ∈ s,f i = (if 0∈s then f 0 else 1)*∏ j ∈ tailIndices s,f (j+1) := by
  have hp : ∏ j ∈ tailIndices s,f (j+1)=∏ i ∈ s.erase 0,f i := by
    rw [← tailIndices_image s,Finset.prod_image]
    exact fun _ _ _ _ h => Nat.succ_injective h
  rw [hp]
  by_cases h : 0∈s
  · rw [if_pos h,← Finset.mul_prod_erase _ _ h]
  · simp [h]

variable (ν : Measure Seed) [IsProbabilityMeasure ν]

theorem cons_preserves : MeasurePreserving (cons (Seed:=Seed)) (ν.prod (law ν)) (law ν) := by
  refine ⟨cons_measurable,?_⟩
  apply Measure.eq_infinitePi (fun _ : ℕ => ν)
  intro s t ht
  have hp : MeasurableSet (Set.pi (s : Set ℕ) t) :=
    MeasurableSet.pi s.countable_toSet ht
  rw [Measure.map_apply cons_measurable hp]
  have he : cons ⁻¹' Set.pi (s : Set ℕ) t =
      (if 0∈s then t 0 else Set.univ) ×ˢ
        Set.pi (tailIndices s : Set ℕ) (fun j => t (j+1)) := by
    ext x
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe]
    constructor
    · intro hx
      constructor
      · split_ifs with h
        · exact hx 0 h
        · trivial
      · intro j hj
        exact hx (j+1) (by simpa [tailIndices] using hj)
    · rintro ⟨h0,htail⟩ i hi
      cases i with
      | zero => simpa only [if_pos hi] using h0
      | succ i => exact htail i (by simpa [tailIndices] using hi)
  rw [he,Measure.prod_prod]
  have ht' : ∀ j∈tailIndices s,MeasurableSet (t (j+1)) :=
    fun j hj => ht (j+1) (by simpa [tailIndices] using hj)
  rw [law,Measure.infinitePi_pi _ ht',prod_split s]
  by_cases h : 0∈s
  · simp only [if_pos h]
  · simp only [if_neg h,measure_univ]

theorem split_preserves : MeasurePreserving (split (Seed:=Seed)) (law ν) (ν.prod (law ν)) := by
  refine ⟨split_measurable,?_⟩
  calc
    (law ν).map split = ((ν.prod (law ν)).map cons).map split :=
      congrArg (Measure.map split) (cons_preserves ν).map_eq.symm
    _ = ν.prod (law ν) := by
      rw [Measure.map_map split_measurable cons_measurable]
      change Measure.map id (ν.prod (law ν))=ν.prod (law ν)
      exact Measure.map_id

end Bilevel.IndependentStream
