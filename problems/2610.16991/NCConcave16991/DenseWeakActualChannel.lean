import NCConcave16991.DenseWeakBankChannel
import NCConcave16991.DenseWeakPosteriorMap

/-! # The actual posterior cell law equals the central binary channel -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

attribute [local instance] Classical.propDecidable

variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]

theorem condition_map_pair_row_ratio (P : FiniteLaw A) (E : Set A)
    (hE : 0 < P.eventMass E) (f : A → I) (g : A → J) (i : I) (j : J)
    (hi : 0 < P.eventMass {a | a ∈ E ∧ f a = i}) :
    conditionalMass ((P.condition E hE).map (fun a ↦ (f a,g a))).mass i j =
      P.eventMass {a | a ∈ E ∧ f a = i ∧ g a = j} /
        P.eventMass {a | a ∈ E ∧ f a = i} := by
  have hn : ((P.condition E hE).map (fun a ↦ (f a,g a))).mass (i,j) =
      P.eventMass {a | a ∈ E ∧ f a = i ∧ g a = j} / P.eventMass E := by
    change (P.condition E hE).eventMass {a | (f a,g a) = (i,j)} = _
    rw [condition_eventMass]
    congr 2
    ext a
    simp [Prod.mk.injEq, and_assoc]
    tauto
  have hd : ((P.condition E hE).map (fun a ↦ (f a,g a))).fst.mass i =
      P.eventMass {a | a ∈ E ∧ f a = i} / P.eventMass E := by
    rw [map_pair_fst_mass, condition_eventMass]
    rfl
  change ((P.condition E hE).map (fun a ↦ (f a,g a))).mass (i,j) /
    ((P.condition E hE).map (fun a ↦ (f a,g a))).fst.mass i = _
  rw [hn, hd]
  field_simp [hE.ne', hi.ne']

theorem eq_of_mass_eq (P Q : FiniteLaw I) (h : P.mass = Q.mass) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem binary_eq_central (P : FiniteLaw (Fin 2 × Fin 2)) (p q : ℝ)
    (hp : p ∈ Set.Icc (7 / 16 : ℝ) (9 / 16))
    (hq : q ∈ Set.Icc (7 / 16 : ℝ) (9 / 16))
    (hc : ∀ θ, conditionalMass P.mass θ 0 = if θ = 0 then p else q) :
    P = centralBinaryChannel (P.fst.mass 0) p q
      ⟨P.fst.nonneg 0,P.fst.mass_le_one 0⟩ hp hq := by
  have h00 := rowMass_mul_conditionalMass P.mass P.nonneg 0 0
  have h10 := rowMass_mul_conditionalMass P.mass P.nonneg 1 0
  rw [hc] at h00 h10
  have hrow0 : rowMass P.mass 0 = P.mass (0,0) + P.mass (0,1) := by
    simp only [rowMass, Fin.sum_univ_two]
  have hrow1 : rowMass P.mass 1 = P.mass (1,0) + P.mass (1,1) := by
    simp only [rowMass, Fin.sum_univ_two]
  have hrows : rowMass P.mass 0 + rowMass P.mass 1 = 1 := by
    simpa only [fst, Fin.sum_univ_two] using P.fst.sum_one
  have hrow1' : rowMass P.mass 1 = 1 - rowMass P.mass 0 := by linarith
  rw [hrow1'] at h10 hrow1
  apply eq_of_mass_eq
  funext z
  rcases z with ⟨θ,b⟩
  fin_cases θ <;> fin_cases b <;>
    simp [centralBinaryChannel, bernoulliMass, fst] at * <;>
    nlinarith only [h00,h10,hrow0,hrow1,hrows]

end NCConcave16991.DenseWeakHiding.FiniteLaw

namespace NCConcave16991.DenseWeakHiding

attribute [local instance] Classical.propDecidable

def observedCellLaw {n m : ℕ} (hm : m ≤ n) (R B : Finset (Fin n))
    (hE : 0 < (biasedColumnLaw n m hm).eventMass (observationEvent R B)) (j : Fin n) :
    FiniteLaw (Fin 2 × Fin 2) :=
  ((biasedColumnLaw n m hm).condition (observationEvent R B) hE).map
    (fun c ↦ (c.1,columnBit c j))

/-- The actual static-column posterior, after any feasible row observation,
has the paper's literal one-cell information bound. -/
theorem observedCellLaw_mutualInformation_le {n m : ℕ} (hm : m ≤ n)
    (hparity : m % 2 = n % 2) (R B : Finset (Fin n)) (hB : B ⊆ R)
    (hbudget : 8 * m + 9 * R.card ≤ n)
    (hE : 0 < (biasedColumnLaw n m hm).eventMass (observationEvent R B))
    (j : UnseenRows R) :
    (observedCellLaw hm R B hE j.val).mutualInformation ≤
      (32 / 63 : ℝ) * ((m : ℝ) / ((n : ℝ) - R.card)) ^ 2 := by
  have hrn : R.card < n := by
    have hc := Finset.card_le_card (Finset.subset_univ (insert j.val R))
    rw [Finset.card_insert_of_notMem j.property, Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hsmall : 2 * R.card + m + 1 ≤ n := by omega
  have hBc : B.card ≤ R.card := Finset.card_le_card hB
  let σ : ℝ := 2 * (B.card : ℝ) - R.card
  let p := nextSignProbability n m R.card σ 1
  let q := nextSignProbability n m R.card σ (-1)
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hd0 : 0 ≤ (R.card : ℝ) := Nat.cast_nonneg _
  have hnd : (R.card : ℝ) < n := by exact_mod_cast hrn
  have hbd : 8 * (m : ℝ) + 9 * R.card ≤ n := by exact_mod_cast hbudget
  have hσ : |σ| ≤ R.card := by
    have hbR : (B.card : ℝ) ≤ R.card := by exact_mod_cast hBc
    have hb0 : 0 ≤ (B.card : ℝ) := Nat.cast_nonneg _
    exact abs_le.mpr ⟨by dsimp [σ]; linarith, by dsimp [σ]; linarith⟩
  have hp := nextSignProbability_mem_Icc hm0 hd0 hnd hbd hσ (Or.inl rfl)
  have hq := nextSignProbability_mem_Icc hm0 hd0 hnd hbd hσ (Or.inr rfl)
  let S := observedCellLaw hm R B hE j.val
  have hc (θ : Fin 2) : conditionalMass S.mass θ 0 = if θ = 0 then p else q := by
    have hpos := biasedColumn_observed_label_mass_pos hm hsmall hB θ
    have hden : {c : EncodedColumn n m | c ∈ observationEvent R B ∧ c.1 = θ} =
        {c | c.1 = θ ∧ c.2.val ∩ R = B} := by
      ext c
      simp [observationEvent, and_comm]
    have hnum : {c : EncodedColumn n m |
        c ∈ observationEvent R B ∧ c.1 = θ ∧ columnBit c j.val = 0} =
        {c | c.1 = θ ∧ c.2.val ∩ R = B ∧ columnBit c j.val = 0} := by
      ext c
      simp [observationEvent, and_comm, and_left_comm]
    have hr := FiniteLaw.condition_map_pair_row_ratio (biasedColumnLaw n m hm)
      (observationEvent R B) hE Sigma.fst (fun c ↦ columnBit c j.val) θ 0
      (by simpa only [hden] using hpos)
    rw [hnum, hden] at hr
    haveI := biasedColumn_observation_nonempty hsmall hB θ
    have hk := (positiveCount_observation_bounds hsmall θ).1
    have he := biasedColumn_conditional_nextBit hm hparity θ R B hB (hBc.trans hk) j
    have hresult := hr.trans he
    fin_cases θ <;> simpa [S, observedCellLaw, p, q, σ, hiddenSign] using hresult
  have heq := FiniteLaw.binary_eq_central S p q hp hq hc
  change S.mutualInformation ≤ _
  rw [heq]
  exact nextSign_mutualInformation_le hm0 hd0 hnd hbd hσ
    ⟨S.fst.nonneg 0,S.fst.mass_le_one 0⟩

end NCConcave16991.DenseWeakHiding
