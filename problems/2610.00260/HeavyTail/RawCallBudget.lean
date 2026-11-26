import HeavyTail.ConditionalConcentration

/-!
An adapted raw-call rejection budget. The one-step input is the actual
conditional expectation of a rejection indicator, bounded by 1/16. The
terminal count estimate is derived, not assumed. Boundedness discharges all
integrability requirements in the conditional product argument.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace HeavyTail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P]

def rejectionIndicator (A : ℕ → Set Ω) (i : ℕ) : Ω → ℝ :=
  (A i).indicator (fun _ => 1)

def rejectionFactor (A : ℕ → Set Ω) (i : ℕ) (ω : Ω) : ℝ :=
  1 + 15 * rejectionIndicator A i ω

def rejectionCount (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range n, if ω ∈ A i then 1 else 0

theorem rejectionCount_succ (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    rejectionCount A (n + 1) ω = rejectionCount A n ω + (if ω ∈ A n then 1 else 0) := by
  classical
  unfold rejectionCount
  rw [Finset.sum_range_succ]

theorem rejectionIndicator_nonneg (A : ℕ → Set Ω) (i : ℕ) (ω : Ω) :
    0 ≤ rejectionIndicator A i ω := by
  classical
  by_cases h : ω ∈ A i <;> simp [rejectionIndicator, h]

theorem rejectionIndicator_le_one (A : ℕ → Set Ω) (i : ℕ) (ω : Ω) :
    rejectionIndicator A i ω ≤ 1 := by
  classical
  by_cases h : ω ∈ A i <;> simp [rejectionIndicator, h]

theorem rejectionFactor_bounds (A : ℕ → Set Ω) (i : ℕ) (ω : Ω) :
    0 < rejectionFactor A i ω ∧ rejectionFactor A i ω ≤ 16 := by
  unfold rejectionFactor
  constructor <;> nlinarith [rejectionIndicator_nonneg A i ω, rejectionIndicator_le_one A i ω]

theorem rejectionFactor_product (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    prefixProduct (rejectionFactor A) n ω = (16 : ℝ) ^ rejectionCount A n ω := by
  classical
  induction n with
  | zero => simp [prefixProduct, rejectionCount]
  | succ n ih =>
    rw [prefixProduct_succ, ih, rejectionCount_succ]
    by_cases h : ω ∈ A n <;>
      norm_num [rejectionFactor, rejectionIndicator, h, pow_succ]

theorem rejectionIndicator_integrable {ℱ : Filtration ℕ mΩ} {A : ℕ → Set Ω}
    (hA : ∀ i, MeasurableSet[ℱ (i + 1)] (A i)) (i : ℕ) :
    Integrable (rejectionIndicator A i) P := by
  exact (integrable_const (1 : ℝ)).indicator ((ℱ.le (i + 1)) _ (hA i))

theorem rejectionFactor_stronglyMeasurable {ℱ : Filtration ℕ mΩ} {A : ℕ → Set Ω}
    (hA : ∀ i, MeasurableSet[ℱ (i + 1)] (A i)) (i : ℕ) :
    StronglyMeasurable[ℱ (i + 1)] (rejectionFactor A i) := by
  exact stronglyMeasurable_const.add
    ((stronglyMeasurable_const.indicator (hA i)).const_mul 15)

theorem rejectionFactor_conditional_bound {ℱ : Filtration ℕ mΩ} {A : ℕ → Set Ω}
    (hA : ∀ i, MeasurableSet[ℱ (i + 1)] (A i))
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[rejectionIndicator A i | ℱ i]) ω ≤ 1 / 16) (i : ℕ) :
    ∀ᵐ ω ∂P, (P[rejectionFactor A i | ℱ i]) ω ≤ 2 := by
  have hi := rejectionIndicator_integrable (P := P) hA i
  have hadd := condExp_add (integrable_const (1 : ℝ)) (hi.const_mul 15) (ℱ i)
  have hsmul := condExp_smul (μ := P) (15 : ℝ) (rejectionIndicator A i) (ℱ i)
  filter_upwards [hadd, hsmul, hcond i] with ω ha hs hc
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const (ℱ.le i)] at ha hs
  change (P[(fun _ => (1 : ℝ)) + (fun ω => 15 * rejectionIndicator A i ω) | ℱ i]) ω ≤ 2
  rw [ha]
  change 1 + (P[(15 : ℝ) • rejectionIndicator A i | ℱ i]) ω ≤ 2
  rw [hs]
  nlinarith

/-- In `4n` adapted trials, at least `3n` rejections have probability at most
`2^(-8n)`, with no independence assumption between trials. -/
theorem rejection_budget_tail {ℱ : Filtration ℕ mΩ} {A : ℕ → Set Ω}
    (hA : ∀ i, MeasurableSet[ℱ (i + 1)] (A i))
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[rejectionIndicator A i | ℱ i]) ω ≤ 1 / 16) (n : ℕ) :
    P.real {ω | 3 * n ≤ rejectionCount A (4 * n) ω} ≤ ((2 : ℝ) ^ (8 * n))⁻¹ := by
  have hm := rejectionFactor_stronglyMeasurable hA
  have hi : ∀ i, Integrable (rejectionFactor A i) P := by
    intro i
    exact (integrable_const (1 : ℝ)).add ((rejectionIndicator_integrable hA i).const_mul 15)
  have hpi : ∀ k, Integrable (prefixProduct (rejectionFactor A) k) P := by
    intro k
    apply (integrable_const ((16 : ℝ) ^ k)).mono'
      ((prefixProduct_stronglyMeasurable hm k).mono (ℱ.le k)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (prefixProduct_pos
        (fun i ω => (rejectionFactor_bounds A i ω).1) k ω)]
      calc
        _ ≤ ∏ _i ∈ Finset.range k, (16 : ℝ) :=
          Finset.prod_le_prod (fun i _ => (rejectionFactor_bounds A i ω).1.le)
            (fun i _ => (rejectionFactor_bounds A i ω).2)
        _ = (16 : ℝ) ^ k := by simp
  have ht := prefixProduct_tail_bound (by norm_num : (0 : ℝ) < 2)
    (inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) (8 * n))) hm
    (fun i ω => (rejectionFactor_bounds A i ω).1.le) hi hpi
    (rejectionFactor_conditional_bound hA hcond) (4 * n)
  apply le_trans (measureReal_mono (s₂ :=
    {ω | (2 : ℝ) ^ (4 * n) / ((2 : ℝ) ^ (8 * n))⁻¹ ≤
      prefixProduct (rejectionFactor A) (4 * n) ω}) ?_) ht
  intro ω hω
  change (2 : ℝ) ^ (4 * n) / ((2 : ℝ) ^ (8 * n))⁻¹ ≤
    prefixProduct (rejectionFactor A) (4 * n) ω
  rw [rejectionFactor_product]
  have he : (2 : ℝ) ^ (4 * n) / ((2 : ℝ) ^ (8 * n))⁻¹ = (16 : ℝ) ^ (3 * n) := by
    rw [div_inv_eq_mul, ← pow_add, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
    congr 1
    omega
  rw [he]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) hω

def acceptedIndices (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : List ℕ := by
  classical
  exact (List.range n).filter (fun i => decide (ω ∉ A i))

theorem accepted_length_add_rejectionCount (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    (acceptedIndices A n ω).length + rejectionCount A n ω = n := by
  classical
  induction n with
  | zero => simp [acceptedIndices, rejectionCount]
  | succ n ih =>
    rw [rejectionCount_succ]
    have he : acceptedIndices A (n + 1) ω =
        acceptedIndices A n ω ++ (if ω ∈ A n then [] else [n]) := by
      by_cases h : ω ∈ A n <;> simp [acceptedIndices, List.range_succ, List.filter_append, h]
    rw [he, List.length_append]
    by_cases h : ω ∈ A n <;> simp [h] <;> omega

/-- Failure to obtain n accepted observations within 4n raw calls. -/
theorem accepted_budget_failure_tail {ℱ : Filtration ℕ mΩ} {A : ℕ → Set Ω}
    (hA : ∀ i, MeasurableSet[ℱ (i + 1)] (A i))
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[rejectionIndicator A i | ℱ i]) ω ≤ 1 / 16) (n : ℕ) :
    P.real {ω | (acceptedIndices A (4 * n) ω).length < n} ≤ ((2 : ℝ) ^ (8 * n))⁻¹ := by
  apply le_trans (measureReal_mono (s₂ := {ω | 3 * n ≤ rejectionCount A (4 * n) ω}) ?_)
    (rejection_budget_tail hA hcond n)
  intro ω hω
  have hc := accepted_length_add_rejectionCount A (4 * n) ω
  change (acceptedIndices A (4 * n) ω).length < n at hω
  change 3 * n ≤ rejectionCount A (4 * n) ω
  omega

/-- On a common raw path, a successful capped execution has exactly the
same first n accepted observations as any longer ideal execution. -/
theorem capped_accepted_prefix_eq {α : Type*} (Y : ℕ → Ω → α)
    (A : ℕ → Set Ω) (ω : Ω) {m k n : ℕ} (hmk : m ≤ k)
    (hsuccess : n ≤ (acceptedIndices A m ω).length) :
    ((acceptedIndices A m ω).map (fun i => Y i ω)).take n =
      ((acceptedIndices A k ω).map (fun i => Y i ω)).take n := by
  classical
  have hr : List.range m <+: List.range k := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
    rw [List.range_add]
    exact List.prefix_append _ _
  have hp := (hr.filter (fun i => decide (ω ∉ A i))).map (fun i => Y i ω)
  change ((acceptedIndices A m ω).map (fun i => Y i ω)) <+:
    ((acceptedIndices A k ω).map (fun i => Y i ω)) at hp
  obtain ⟨rest, he⟩ := hp
  rw [← he, List.take_append_of_le_length (by simpa using hsuccess)]

/-- The capped and longer accepted-output prefixes disagree only on the
derived raw-budget failure event. -/
theorem capped_ideal_output_disagreement_bound {α : Type*} (Y : ℕ → Ω → α)
    {ℱ : Filtration ℕ mΩ} {A : ℕ → Set Ω}
    (hA : ∀ i, MeasurableSet[ℱ (i + 1)] (A i))
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[rejectionIndicator A i | ℱ i]) ω ≤ 1 / 16)
    (n k : ℕ) (hk : 4 * n ≤ k) :
    P.real {ω | ((acceptedIndices A (4 * n) ω).map (fun i => Y i ω)).take n ≠
      ((acceptedIndices A k ω).map (fun i => Y i ω)).take n} ≤ ((2 : ℝ) ^ (8 * n))⁻¹ := by
  apply le_trans (measureReal_mono (s₂ :=
    {ω | (acceptedIndices A (4 * n) ω).length < n}) ?_)
    (accepted_budget_failure_tail hA hcond n)
  intro ω hω
  change (acceptedIndices A (4 * n) ω).length < n
  by_contra hn
  exact hω (capped_accepted_prefix_eq Y A ω hk (Nat.le_of_not_gt hn))

end HeavyTail
