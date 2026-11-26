import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! First-acceptance cylinders for an actual infinite sequence of independent
raw samples. Their measures are computed from the infinite product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical
namespace HeavyTail

variable {Ω : Type*} [MeasurableSpace Ω]

def iidRawLaw (P : Measure Ω) [IsProbabilityMeasure P] : Measure (ℕ → Ω) :=
  Measure.infinitePi (fun _ : ℕ => P)

instance iidRawLaw_probability (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (iidRawLaw P) := by
  unfold iidRawLaw
  infer_instance

def firstSuccessWith (S T : Set Ω) (n : ℕ) : Set (ℕ → Ω) :=
  {ω | ω n ∈ S ∩ T ∧ ∀ i < n, ω i ∉ S}

theorem firstSuccessWith_measurable {S T : Set Ω} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (n : ℕ) : MeasurableSet (firstSuccessWith S T n) := by
  have hp : MeasurableSet {ω : ℕ → Ω | ∀ i < n, ω i ∉ S} := by
    convert (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ : i < n =>
      hS.compl.preimage (measurable_pi_apply i)) using 1
    ext ω
    simp
  exact ((hS.inter hT).preimage (measurable_pi_apply n)).inter
    hp

theorem firstSuccessWith_disjoint (S T : Set Ω) :
    Pairwise (fun n m => Disjoint (firstSuccessWith S T n) (firstSuccessWith S T m)) := by
  intro n m hnm
  apply disjoint_left.mpr
  intro ω hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact hm.2 n h hn.1.1
  · exact hn.2 m h hm.1.1

theorem firstSuccessWith_eq_pi (S T : Set Ω) (n : ℕ) :
    firstSuccessWith S T n = Set.pi (Finset.range (n + 1))
      (fun i => if i = n then S ∩ T else Sᶜ) := by
  ext ω
  constructor
  · rintro ⟨hn, hprev⟩ i hi
    by_cases he : i = n
    · simpa [he] using hn
    · have hi' : i < n := by have := Finset.mem_range.mp hi; omega
      simpa [he] using hprev i hi'
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h n (Finset.mem_range.mpr (Nat.lt_succ_self n))
    · intro i hi
      have he : i ≠ n := ne_of_lt hi
      simpa [he] using h i (Finset.mem_range.mpr (by omega))

theorem firstSuccessWith_measure (P : Measure Ω) [IsProbabilityMeasure P]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) (n : ℕ) :
    iidRawLaw P (firstSuccessWith S T n) = P Sᶜ ^ n * P (S ∩ T) := by
  rw [firstSuccessWith_eq_pi, iidRawLaw, Measure.infinitePi_pi]
  · rw [Finset.prod_range_succ]
    simp only [ite_true]
    have he : (∏ i ∈ Finset.range n, P (if i = n then S ∩ T else Sᶜ)) = P Sᶜ ^ n := by
      calc
        _ = ∏ _i ∈ Finset.range n, P Sᶜ := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [if_neg (ne_of_lt (Finset.mem_range.mp hi))]
        _ = _ := by simp
    rw [he]
  · intro i _
    split_ifs
    · exact hS.inter hT
    · exact hS.compl

theorem firstSuccess_union_measure (P : Measure Ω) [IsProbabilityMeasure P]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    iidRawLaw P (⋃ n, firstSuccessWith S T n) = (P S)⁻¹ * P (S ∩ T) := by
  rw [measure_iUnion (firstSuccessWith_disjoint S T) (firstSuccessWith_measurable hS hT)]
  simp_rw [firstSuccessWith_measure P hS hT]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  have he : 1 - P Sᶜ = P S := by
    simpa only [measure_univ, compl_compl] using
      (measure_compl hS.compl (measure_ne_top P Sᶜ)).symm
  rw [he]

theorem firstSuccess_union_eq (S : Set Ω) :
    (⋃ n, firstSuccessWith S Set.univ n) = {ω | ∃ n, ω n ∈ S} := by
  ext ω
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1.1⟩
  · intro h
    refine ⟨Nat.find h, ?_⟩
    exact ⟨⟨Nat.find_spec h, mem_univ _⟩, fun i hi => Nat.find_min h hi⟩

theorem eventuallyAccepts_measurable {S : Set Ω} (hS : MeasurableSet S) :
    MeasurableSet {ω : ℕ → Ω | ∃ n, ω n ∈ S} := by
  convert (MeasurableSet.iUnion fun n : ℕ => hS.preimage (measurable_pi_apply n)) using 1
  ext ω
  simp

theorem iid_eventually_accepts (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set Ω} (hS : MeasurableSet S) (hpos : P S ≠ 0) :
    ∀ᵐ ω ∂iidRawLaw P, ∃ n, ω n ∈ S := by
  have hmass : iidRawLaw P {ω | ∃ n, ω n ∈ S} = 1 := by
    rw [← firstSuccess_union_eq, firstSuccess_union_measure P hS MeasurableSet.univ,
      inter_univ]
    exact ENNReal.inv_mul_cancel hpos (measure_ne_top P S)
  rw [ae_iff]
  have hm := eventuallyAccepts_measurable hS
  change iidRawLaw P {ω : ℕ → Ω | ∃ n, ω n ∈ S}ᶜ = 0
  rw [measure_compl hm (measure_ne_top _ _), hmass, measure_univ, tsub_self]

end HeavyTail
