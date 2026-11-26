import HeavyTail.RejectionSamplerEvents

/-!
An actual rejection sampler on an infinite iid raw sequence. Its output is the
coordinate at the least accepted index. Coordinate zero is a harmless fallback
on paths that never accept; those paths are proved null whenever P(S)>0.
The conditional accepted law is a theorem about this output pushforward.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
namespace HeavyTail

variable {Ω : Type*} [MeasurableSpace Ω]

def firstAcceptIndex (S : Set Ω) (ω : ℕ → Ω) : ℕ :=
  if h : ∃ n, ω n ∈ S then Nat.find h else 0

def rejectionSample (S : Set Ω) (ω : ℕ → Ω) : Ω :=
  ω (firstAcceptIndex S ω)

theorem firstAcceptIndex_eq {S T : Set Ω} {ω : ℕ → Ω} {n : ℕ}
    (hn : ω ∈ firstSuccessWith S T n) : firstAcceptIndex S ω = n := by
  have he : ∃ i, ω i ∈ S := ⟨n, hn.1.1⟩
  rw [firstAcceptIndex, dif_pos he]
  exact (Nat.find_eq_iff he).mpr ⟨hn.1.1, hn.2⟩

theorem rejectionSample_first_success {S T : Set Ω} {ω : ℕ → Ω} {n : ℕ}
    (hn : ω ∈ firstSuccessWith S T n) : rejectionSample S ω = ω n := by
  rw [rejectionSample, firstAcceptIndex_eq hn]

theorem rejectionSample_preimage (S T : Set Ω) :
    rejectionSample S ⁻¹' T = (⋃ n, firstSuccessWith S T n) ∪
      ({ω | ¬ ∃ n, ω n ∈ S} ∩ {ω | ω 0 ∈ T}) := by
  ext ω
  simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_setOf_eq]
  constructor
  · intro ht
    by_cases he : ∃ n, ω n ∈ S
    · left
      refine ⟨Nat.find he, ⟨⟨Nat.find_spec he, ?_⟩, fun i hi => Nat.find_min he hi⟩⟩
      simpa only [rejectionSample, firstAcceptIndex, dif_pos he] using ht
    · right
      exact ⟨he, by simpa only [rejectionSample, firstAcceptIndex, dif_neg he] using ht⟩
  · rintro (⟨n, hn⟩ | ⟨he, ht⟩)
    · rw [rejectionSample_first_success hn]
      exact hn.1.2
    · simpa only [rejectionSample, firstAcceptIndex, dif_neg he] using ht

theorem rejectionSample_measurable {S : Set Ω} (hS : MeasurableSet S) :
    Measurable (rejectionSample S) := by
  intro T hT
  rw [rejectionSample_preimage]
  apply (MeasurableSet.iUnion (firstSuccessWith_measurable hS hT)).union
  exact (eventuallyAccepts_measurable hS).compl.inter
    (hT.preimage (measurable_pi_apply 0))

/-- The output of the actual first-acceptance sampler has exactly the normalized
restriction of the raw law to the acceptance set. -/
theorem rejectionSample_map (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set Ω} (hS : MeasurableSet S) (hpos : P S ≠ 0) :
    (iidRawLaw P).map (rejectionSample S) = ProbabilityTheory.cond P S := by
  ext T hT
  rw [Measure.map_apply (rejectionSample_measurable hS) hT]
  have he : rejectionSample S ⁻¹' T =ᵐ[iidRawLaw P] ⋃ n, firstSuccessWith S T n := by
    filter_upwards [iid_eventually_accepts P hS hpos] with ω hω
    apply propext
    have hset := Set.ext_iff.mp (rejectionSample_preimage S T) ω
    constructor
    · intro ht
      rcases hset.mp ht with ht | ht
      · exact ht
      · exact False.elim (ht.1 hω)
    · intro ht
      exact hset.mpr (Or.inl ht)
  rw [measure_congr he, firstSuccess_union_measure P hS hT,
    ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_apply hT]
  simp only [smul_eq_mul, inter_comm]

theorem rejectionSample_mem_ae (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set Ω} (hS : MeasurableSet S) (hpos : P S ≠ 0) :
    ∀ᵐ ω ∂iidRawLaw P, rejectionSample S ω ∈ S := by
  filter_upwards [iid_eventually_accepts P hS hpos] with ω hω
  simpa only [rejectionSample, firstAcceptIndex, dif_pos hω] using Nat.find_spec hω

end HeavyTail
