import FullJet.SamplingWithoutReplacement

open scoped BigOperators ENNReal

namespace FullJet

variable {α : Type*} [DecidableEq α]

/-- Positive and negative answers constrain a column only on revealed labels. -/
def compatibleColumn (P N S : Finset α) : Prop := P ⊆ S ∧ Disjoint N S

instance compatibleColumnDecidable (P N S : Finset α) :
    Decidable (compatibleColumn P N S) := inferInstanceAs (Decidable (P ⊆ S ∧ Disjoint N S))

theorem union_injOn_residual (U P N : Finset α) (k : ℕ) :
    Set.InjOn (P ∪ ·) ((U \ (P ∪ N)).powersetCard k : Set (Finset α)) := by
  intro S hS R hR heq
  have hd (A : Finset α) (hA : A ∈ (U \ (P ∪ N)).powersetCard k) : Disjoint P A := by
    apply Finset.disjoint_left.mpr
    intro i hi hiA
    exact (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hA).1 hiA)).2
      (Finset.mem_union_left N hi)
  have h := congrArg (fun A : Finset α => A \ P) heq
  simpa only [Finset.union_sdiff_cancel_left (hd S hS),
    Finset.union_sdiff_cancel_left (hd R hR)] using h

theorem powersetCard_filter_compatible (U P N : Finset α) (k : ℕ)
    (hP : P ⊆ U) (hPN : Disjoint P N) (hk : P.card ≤ k) :
    (U.powersetCard k).filter (compatibleColumn P N) =
      ((U \ (P ∪ N)).powersetCard (k - P.card)).image (P ∪ ·) := by
  ext S
  constructor
  · intro hS
    obtain ⟨hS, hPS, hNS⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSU, hcard⟩ := Finset.mem_powersetCard.mp hS
    refine Finset.mem_image.mpr ⟨S \ P, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩,
      Finset.union_sdiff_of_subset hPS⟩
    · intro i hi
      obtain ⟨hiS, hiP⟩ := Finset.mem_sdiff.mp hi
      refine Finset.mem_sdiff.mpr ⟨hSU hiS, ?_⟩
      intro hiPN
      rcases Finset.mem_union.mp hiPN with hiP' | hiN
      · exact hiP hiP'
      · exact Finset.disjoint_left.mp hNS hiN hiS
    · rw [Finset.card_sdiff hPS, hcard]
  · intro hS
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨hRU, hcard⟩ := Finset.mem_powersetCard.mp hR
    have hPR : Disjoint P R := by
      apply Finset.disjoint_left.mpr
      intro i hiP hiR
      exact (Finset.mem_sdiff.mp (hRU hiR)).2 (Finset.mem_union_left N hiP)
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.subset_union_left, ?_⟩
    · exact Finset.union_subset hP (hRU.trans Finset.sdiff_subset)
    · rw [Finset.card_union_of_disjoint hPR, hcard]
      omega
    · apply Finset.disjoint_left.mpr
      intro i hiN hiPR
      rcases Finset.mem_union.mp hiPR with hiP | hiR
      · exact Finset.disjoint_left.mp hPN hiP hiN
      · exact (Finset.mem_sdiff.mp (hRU hiR)).2 (Finset.mem_union_right P hiN)

/-- After any compatible finite observations, the unrevealed signs remain a
uniform fixed-size subset. This is equality of the normalized conditional PMFs. -/
theorem fixedSizeLaw_condition_compatible (U P N : Finset α) (k : ℕ)
    (hU : k ≤ U.card) (hP : P ⊆ U) (hPN : Disjoint P N) (hk : P.card ≤ k)
    (hrem : k - P.card ≤ (U \ (P ∪ N)).card)
    (hpos : ∃ S ∈ {S | compatibleColumn P N S}, S ∈ (fixedSizeLaw U k hU).support) :
    (fixedSizeLaw U k hU).filter {S | compatibleColumn P N S} hpos =
      (fixedSizeLaw (U \ (P ∪ N)) (k - P.card) hrem).map (P ∪ ·) := by
  have hR : ((U \ (P ∪ N)).powersetCard (k - P.card)).Nonempty :=
    Finset.powersetCard_nonempty.mpr hrem
  have hA : ((U.powersetCard k).filter (compatibleColumn P N)).Nonempty := by
    rw [powersetCard_filter_compatible U P N k hP hPN hk]
    exact hR.image (P ∪ ·)
  unfold fixedSizeLaw
  rw [uniformOfFinset_filter (U.powersetCard k) (Finset.powersetCard_nonempty.mpr hU)
    {S | compatibleColumn P N S} hA hpos]
  trans PMF.uniformOfFinset (((U \ (P ∪ N)).powersetCard (k - P.card)).image (P ∪ ·))
    (hR.image (P ∪ ·))
  · congr 1
    convert powersetCard_filter_compatible U P N k hP hPN hk using 1
  · exact (uniformOfFinset_map_injOn _ hR _ (union_injOn_residual U P N _)).symm

/-- A deterministic adaptive row strategy. Randomized strategies are obtained by
fixing their seed; arbitrary dependence on previous answers is allowed. -/
def rowAnswers (ask : List Bool → α) (S : Finset α) (past : List Bool) : ℕ → List Bool
  | 0 => []
  | q + 1 =>
    let b := decide (ask past ∈ S)
    b :: rowAnswers ask S (past ++ [b]) q

def positiveLabels (ask : List Bool → α) (past : List Bool) : List Bool → Finset α
  | [] => ∅
  | b :: bs =>
    let P := positiveLabels ask (past ++ [b]) bs
    if b then insert (ask past) P else P

def negativeLabels (ask : List Bool → α) (past : List Bool) : List Bool → Finset α
  | [] => ∅
  | b :: bs =>
    let N := negativeLabels ask (past ++ [b]) bs
    if b then N else insert (ask past) N

/-- The fiber of an adaptive transcript is exactly its positive/negative
membership constraints, even when the strategy repeats labels. -/
theorem rowAnswers_eq_iff (ask : List Bool → α) (S : Finset α)
    (past bits : List Bool) :
    rowAnswers ask S past bits.length = bits ↔
      compatibleColumn (positiveLabels ask past bits) (negativeLabels ask past bits) S := by
  induction bits generalizing past with
  | nil => simp [rowAnswers, positiveLabels, negativeLabels, compatibleColumn]
  | cons b bs ih =>
    cases b <;> by_cases hi : ask past ∈ S <;>
      simp [rowAnswers, positiveLabels, negativeLabels, compatibleColumn,
        hi, ih, Finset.disjoint_insert_left, Finset.insert_subset_iff]

theorem compatibleColumn_feasible (U P N S : Finset α) (k : ℕ)
    (hS : S ∈ U.powersetCard k) (hc : compatibleColumn P N S) :
    P ⊆ U ∧ Disjoint P N ∧ P.card ≤ k ∧ k - P.card ≤ (U \ (P ∪ N)).card := by
  obtain ⟨hSU, hcard⟩ := Finset.mem_powersetCard.mp hS
  obtain ⟨hPS, hNS⟩ := hc
  have hPN : Disjoint P N := hNS.symm.mono_left hPS
  have hPk : P.card ≤ k := hcard ▸ Finset.card_le_card hPS
  refine ⟨hPS.trans hSU, hPN, hPk, ?_⟩
  have hres : S \ P ⊆ U \ (P ∪ N) := by
    intro i hi
    obtain ⟨hiS, hiP⟩ := Finset.mem_sdiff.mp hi
    refine Finset.mem_sdiff.mpr ⟨hSU hiS, ?_⟩
    intro hiPN
    rcases Finset.mem_union.mp hiPN with hiP' | hiN
    · exact hiP hiP'
    · exact Finset.disjoint_left.mp hNS hiN hiS
  have h := Finset.card_le_card hres
  rwa [Finset.card_sdiff hPS, hcard] at h

/-- A realizable adaptive transcript leaves exactly the uniform residual law.
Feasibility is derived from positive probability, not assumed as a hypothesis. -/
theorem fixedSizeLaw_condition_rowAnswers (U : Finset α) (k : ℕ) (hU : k ≤ U.card)
    (ask : List Bool → α) (past bits : List Bool)
    (hpos : ∃ S ∈ {S | rowAnswers ask S past bits.length = bits},
      S ∈ (fixedSizeLaw U k hU).support) :
    ∃ hrem : k - (positiveLabels ask past bits).card ≤
        (U \ (positiveLabels ask past bits ∪ negativeLabels ask past bits)).card,
    (fixedSizeLaw U k hU).filter {S | rowAnswers ask S past bits.length = bits} hpos =
      (fixedSizeLaw (U \ (positiveLabels ask past bits ∪ negativeLabels ask past bits))
        (k - (positiveLabels ask past bits).card) hrem).map (positiveLabels ask past bits ∪ ·) := by
  let P := positiveLabels ask past bits
  let N := negativeLabels ask past bits
  have hset : {S | rowAnswers ask S past bits.length = bits} =
      {S | compatibleColumn P N S} := by
    ext S
    exact rowAnswers_eq_iff ask S past bits
  obtain ⟨S, hbits, hS⟩ := hpos
  have hmem : S ∈ U.powersetCard k := by
    simpa only [fixedSizeLaw, PMF.mem_support_uniformOfFinset_iff] using hS
  have hc : compatibleColumn P N S := (rowAnswers_eq_iff ask S past bits).mp hbits
  obtain ⟨hP, hPN, hk, hrem⟩ := compatibleColumn_feasible U P N S k hmem hc
  refine ⟨hrem, ?_⟩
  have hpos' : ∃ S ∈ {S | compatibleColumn P N S}, S ∈ (fixedSizeLaw U k hU).support :=
    ⟨S, hc, hS⟩
  convert fixedSizeLaw_condition_compatible U P N k hU hP hPN hk hrem hpos' using 1
  congr 1

/-- Exact conditional probability of a positive answer at a new row selected
after an arbitrary adaptive transcript. Repeated past queries are counted once. -/
theorem fixedSizeLaw_next_probability (U : Finset α) (k : ℕ) (hU : k ≤ U.card)
    (ask : List Bool → α) (past bits : List Bool)
    (hpos : ∃ S ∈ {S | rowAnswers ask S past bits.length = bits},
      S ∈ (fixedSizeLaw U k hU).support)
    (i : α) (hi : i ∈ U \ (positiveLabels ask past bits ∪ negativeLabels ask past bits)) :
    (((fixedSizeLaw U k hU).filter {S | rowAnswers ask S past bits.length = bits} hpos).toOuterMeasure
      {S | i ∈ S}).toReal =
        ((k - (positiveLabels ask past bits).card : ℕ) : ℝ) /
          (U \ (positiveLabels ask past bits ∪ negativeLabels ask past bits)).card := by
  obtain ⟨hrem, heq⟩ := fixedSizeLaw_condition_rowAnswers U k hU ask past bits hpos
  rw [heq, PMF.toOuterMeasure_map_apply]
  have hiP : i ∉ positiveLabels ask past bits := fun h =>
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ h)
  have hset : (fun S => positiveLabels ask past bits ∪ S) ⁻¹' {S | i ∈ S} = {S | i ∈ S} := by
    ext S
    simp [hiP]
  rw [hset]
  exact fixedSizeLaw_present_probability _ _ i hi hrem

end FullJet
