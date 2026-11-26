import NCConcave16991.DenseWeakAdaptiveBank
import NCConcave16991.DenseWeakBankEntropy
import NCConcave16991.DenseWeakBinaryLaw

/-! # The next unread cell channel of the original static biased column -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def columnBit {n m : ℕ} (c : EncodedColumn n m) (i : Fin n) : Fin 2 :=
  if i ∈ c.2.val then 0 else 1

theorem columnBit_zero_iff {n m : ℕ} (c : EncodedColumn n m) (i : Fin n) :
    columnBit c i = 0 ↔ i ∈ c.2.val := by
  by_cases h : i ∈ c.2.val <;> simp [columnBit, h]

theorem columnBit_sign {n m : ℕ} (c : EncodedColumn n m) (i : Fin n) :
    hiddenSign (columnBit c i) = columnSign c.2.val i := by
  by_cases h : i ∈ c.2.val <;> simp [columnBit, hiddenSign, columnSign, h]

def observationEvent {n m : ℕ} (R B : Finset (Fin n)) : Set (EncodedColumn n m) :=
  {c | c.2.val ∩ R = B}

theorem observedColumn_nonempty_of_bounds {n k : ℕ} {R B : Finset (Fin n)}
    (hB : B ⊆ R) (hBk : B.card ≤ k) (hrem : k - B.card ≤ n - R.card) :
    Nonempty (ObservedColumn k R B) := by
  have hc : k - B.card ≤ Fintype.card (UnseenRows R) := by
    simpa only [unseenRows_card, Fintype.card_fin] using hrem
  obtain ⟨C⟩ := positiveColumn_nonempty (UnseenRows R) (k - B.card) hc
  exact ⟨completeColumn hB hBk C⟩

theorem positiveCount_observation_bounds {n m r : ℕ} (hsmall : 2 * r + m + 1 ≤ n)
    (θ : Fin 2) : r ≤ positiveCount n m θ ∧ positiveCount n m θ + r ≤ n := by
  unfold positiveCount
  split_ifs <;> omega

theorem biasedColumn_observation_nonempty {n m : ℕ} {R B : Finset (Fin n)}
    (hsmall : 2 * R.card + m + 1 ≤ n) (hB : B ⊆ R) (θ : Fin 2) :
    Nonempty (ObservedColumn (positiveCount n m θ) R B) := by
  have hb := Finset.card_le_card hB
  have hk := positiveCount_observation_bounds hsmall θ
  apply observedColumn_nonempty_of_bounds hB (hb.trans hk.1)
  omega

theorem biasedColumn_mass_pos {n m : ℕ} (hm : m ≤ n) (c : EncodedColumn n m) :
    0 < (biasedColumnLaw n m hm).mass c := by
  letI := positiveColumn_nonempty (Fin n) (positiveCount n m c.1) (by simpa using positiveCount_le hm c.1)
  have hc : 0 < (Fintype.card (BiasColumn n m c.1) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  change 0 < (1 / 2 : ℝ) * (Fintype.card (BiasColumn n m c.1) : ℝ)⁻¹
  exact mul_pos (by norm_num) (inv_pos.mpr hc)

theorem biasedColumn_observed_label_mass_pos {n m : ℕ} (hm : m ≤ n)
    {R B : Finset (Fin n)} (hsmall : 2 * R.card + m + 1 ≤ n)
    (hB : B ⊆ R) (θ : Fin 2) :
    0 < (biasedColumnLaw n m hm).eventMass {c | c.1 = θ ∧ c.2.val ∩ R = B} := by
  obtain ⟨A⟩ := biasedColumn_observation_nonempty hsmall hB θ
  have hp := biasedColumn_mass_pos hm (⟨θ,A.val⟩ : EncodedColumn n m)
  apply hp.trans_le
  unfold FiniteLaw.eventMass
  have h := Finset.single_le_sum
    (fun c (_ : c ∈ (Finset.univ : Finset (EncodedColumn n m))) ↦
      show 0 ≤ (if c.1 = θ ∧ c.2.val ∩ R = B then
        (biasedColumnLaw n m hm).mass c else 0) by
        split_ifs; exact (biasedColumnLaw n m hm).nonneg c; rfl)
    (Finset.mem_univ (⟨θ,A.val⟩ : EncodedColumn n m))
  simpa only [Set.mem_setOf_eq, true_and, ite_true, A.property] using h

theorem biasedColumn_slice_eventMass {n m : ℕ} (hm : m ≤ n) (θ : Fin 2)
    (F : Finset (Fin n) → Prop) :
    (biasedColumnLaw n m hm).eventMass {c | c.1 = θ ∧ F c.2.val} =
      (1 / 2 : ℝ) *
        (columnLaw (Fin n) (positiveCount n m θ) (by simpa using positiveCount_le hm θ)).eventMass
          {A | F A.val} := by
  fin_cases θ <;>
    simp [FiniteLaw.eventMass, Fintype.sum_sigma, Fin.sum_univ_two, biasedColumnLaw] <;>
    rw [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;>
    intro A _ <;>
    split_ifs <;> simp

theorem biasedColumn_label_map_mass {n m : ℕ} (hm : m ≤ n) (θ : Fin 2) :
    ((biasedColumnLaw n m hm).map Sigma.fst).mass θ = 1 / 2 := by
  change (biasedColumnLaw n m hm).eventMass {c | c.1 = θ} = _
  have h := biasedColumn_slice_eventMass hm θ (fun _ ↦ True)
  simpa only [and_true, Set.setOf_true, FiniteLaw.eventMass, Set.mem_setOf_eq, Set.mem_univ, ite_true,
    (columnLaw (Fin n) (positiveCount n m θ) (by simpa using positiveCount_le hm θ)).sum_one,
    mul_one] using h

theorem columnBank_label_map_mass {n m D : ℕ} (hm : m ≤ n) (θ : Fin D → Fin 2) :
    ((columnBankLaw n m D hm).map (fun bank d ↦ (bank d).1)).mass θ =
      (1 / 2 : ℝ) ^ D := by
  rw [columnBankLaw, FiniteLaw.map_pi_mass]
  simp only [FiniteLaw.pi, biasedColumn_label_map_mass, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Exact next-positive-cell probability after conditioning the original
biased law on its label and its actual observed rows. -/
theorem biasedColumn_conditional_nextBit {n m : ℕ} (hm : m ≤ n)
    (hparity : m % 2 = n % 2) (θ : Fin 2) (R B : Finset (Fin n))
    (hB : B ⊆ R) (hBk : B.card ≤ positiveCount n m θ)
    [Nonempty (ObservedColumn (positiveCount n m θ) R B)] (j : UnseenRows R) :
    (biasedColumnLaw n m hm).eventMass
        {c | c.1 = θ ∧ c.2.val ∩ R = B ∧ columnBit c j.val = 0} /
      (biasedColumnLaw n m hm).eventMass
        {c | c.1 = θ ∧ c.2.val ∩ R = B} =
      nextSignProbability n m R.card (2 * (B.card : ℝ) - R.card) (hiddenSign θ) := by
  simp_rw [columnBit_zero_iff]
  rw [biasedColumn_slice_eventMass hm θ (fun A ↦ A ∩ R = B ∧ j.val ∈ A),
    biasedColumn_slice_eventMass hm θ (fun A ↦ A ∩ R = B)]
  rw [mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  letI : MeasurableSpace (BiasColumn n m θ) := ⊤
  rw [FiniteLaw.eventMass_eq_probability, FiniteLaw.eventMass_eq_probability]
  simpa only [Fintype.card_fin] using
    conditional_nextSign_probability (by simpa using positiveCount_le hm θ) hB hBk j
      (by simpa using positiveCount_encoding hm hparity θ)

end NCConcave16991.DenseWeakHiding
