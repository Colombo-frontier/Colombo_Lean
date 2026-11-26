import FullJet.Model
import FullJet.FiniteAveraging

open MeasureTheory Set
open scoped BigOperators

namespace FullJet

abbrev ScalarJet (p : ℕ) := (r : Fin (p + 1)) → ℝ [×r.val]→L[ℝ] ℝ

/-- An arbitrary adaptive algorithm run against actual component jets.
The state may contain an entire transcript and arbitrary private randomness. -/
noncomputable def fullJetOutput {State : Type*} {n p : ℕ}
    (query : State → Fin n × ℝ) (update : State → ScalarJet p → State)
    (output : State → ℝ) (initial : State) (q : ℕ) (f : Fin n → ℝ → ℝ) : ℝ :=
  output (oracleRun query update (fun z => fullJet p (f z.1) z.2) initial q)

def rareSign (b : Bool) : ℝ := if b then 1 else -1

theorem rareSign_sq (b : Bool) : rareSign b ^ 2 = 1 := by cases b <;> norm_num [rareSign]

/-- The indices on the common-oracle path do not depend on the hidden instance. -/
noncomputable def referenceIndices {State : Type*} {n p : ℕ}
    (query : State → Fin n × ℝ) (update : State → ScalarJet p → State)
    (initial : State) (q : ℕ) (μ : ℝ) : Finset (Fin n) :=
  (Finset.range q).image (fun t =>
    (query (oracleRun query update (fun z => fullJet p (quadratic μ 0) z.2) initial t)).1)

theorem referenceIndices_card_le {State : Type*} {n p : ℕ}
    (query : State → Fin n × ℝ) (update : State → ScalarJet p → State)
    (initial : State) (q : ℕ) (μ : ℝ) :
    (referenceIndices query update initial q μ).card ≤ q := queried_indices_card_le _ q

theorem rare_fullJetOutput_eq_reference {State : Type*} {n p : ℕ}
    (query : State → Fin n × ℝ) (update : State → ScalarJet p → State)
    (output : State → ℝ) (initial : State) (q : ℕ) (μ g σ : ℝ) (J : Fin n)
    (hmiss : J ∉ referenceIndices query update initial q μ) :
    fullJetOutput query update output initial q (rareComponent J μ g σ) =
      fullJetOutput query update output initial q (fun _ => quadratic μ 0) := by
  unfold fullJetOutput
  congr 1
  exact rare_index_coupling query update _ _ initial q J
    (fun z hz => rare_fullJet_eq_common J z.1 μ g σ z.2 p hz) hmiss

theorem rare_average_deriv {n : ℕ} (hn : 0 < n) (J : Fin n) (μ g σ x : ℝ) :
    deriv (average (rareComponent J μ g σ)) x = μ * x - σ * g := by
  have h : average (rareComponent J μ g σ) = quadratic μ (σ * g) :=
    funext (rare_average hn J μ g σ)
  rw [h, quadratic_deriv]

/-- On each missed index one of the two actual instances defeats the same seed. -/
theorem rare_missed_index_failure {State : Type*} {n p : ℕ} (hn : 0 < n)
    (query : State → Fin n × ℝ) (update : State → ScalarJet p → State)
    (output : State → ℝ) (initial : State) (q : ℕ) (μ g ε : ℝ) (hε : ε < g)
    (J : Fin n) (hmiss : J ∉ referenceIndices query update initial q μ) :
    ∃ b : Bool, ε < |deriv (average (rareComponent J μ g (rareSign b)))
      (fullJetOutput query update output initial q (rareComponent J μ g (rareSign b)))| := by
  let X := fullJetOutput query update output initial q (fun _ => quadratic μ 0)
  rcases two_sign_gradient_barrier (μ * X) g with h | h
  · refine ⟨true, ?_⟩
    rw [rare_fullJetOutput_eq_reference query update output initial q μ g _ J hmiss,
      rare_average_deriv hn]
    simpa [rareSign] using hε.trans_le h
  · refine ⟨false, ?_⟩
    rw [rare_fullJetOutput_eq_reference query update output initial q μ g _ J hmiss,
      rare_average_deriv hn]
    simpa [rareSign] using hε.trans_le h

/-- A deterministic counting form of the rare-index argument. -/
theorem rare_failure_count {State : Type*} {n p : ℕ} (hn : 0 < n)
    (query : State → Fin n × ℝ) (update : State → ScalarJet p → State)
    (output : State → ℝ) (initial : State) (q : ℕ) (μ g ε : ℝ) (hε : ε < g) :
    (n : ℝ) - q ≤ ∑ J : Fin n, ∑ b : Bool,
      if ε < |deriv (average (rareComponent J μ g (rareSign b)))
        (fullJetOutput query update output initial q (rareComponent J μ g (rareSign b)))|
      then (1 : ℝ) else 0 := by
  classical
  let V := referenceIndices query update initial q μ
  let F (J : Fin n) (b : Bool) : ℝ :=
    if ε < |deriv (average (rareComponent J μ g (rareSign b)))
      (fullJetOutput query update output initial q (rareComponent J μ g (rareSign b)))|
    then 1 else 0
  have hnonneg J b : 0 ≤ F J b := by dsimp [F]; split <;> norm_num
  have hpoint (J : Fin n) : (1 : ℝ) ≤ (if J ∈ V then 1 else 0) + ∑ b, F J b := by
    by_cases hj : J ∈ V
    · simp only [hj, if_true]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun b hb => hnonneg J b))
    · simp only [hj, if_false, zero_add]
      obtain ⟨b, hb⟩ := rare_missed_index_failure hn query update output initial q μ g ε hε J hj
      have heq : F J b = 1 := by simp [F, hb]
      rw [← heq]
      exact Finset.single_le_sum (fun c hc => hnonneg J c) (Finset.mem_univ b)
  have hsum := Finset.sum_le_sum (fun J (_ : J ∈ (Finset.univ : Finset (Fin n))) => hpoint J)
  have hc : (V.card : ℝ) ≤ q := by exact_mod_cast referenceIndices_card_le query update initial q μ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have hv : (∑ J : Fin n, if J ∈ V then (1 : ℝ) else 0) = V.card := by simp
  rw [hv] at hsum
  change (n : ℝ) - q ≤ ∑ J, ∑ b, F J b
  linarith

/-- A fixed-budget randomized algorithm has a fixed hard instance. This proof
integrates over arbitrary private randomness instead of assuming Yao's principle. -/
theorem rare_randomized_failure {Ω State : Type*} [MeasurableSpace Ω]
    {n p : ℕ} (hn : 0 < n) (P : Measure Ω) [IsProbabilityMeasure P]
    (query : State → Fin n × ℝ) (update : State → ScalarJet p → State)
    (output : State → ℝ) (initial : Ω → State) (q : ℕ) (hq : 2 * q ≤ n)
    (μ g ε : ℝ) (hε : ε < g)
    (hmeas : ∀ J b, MeasurableSet {ω | ε < |deriv (average (rareComponent J μ g (rareSign b)))
      (fullJetOutput query update output (initial ω) q (rareComponent J μ g (rareSign b)))|}) :
    ∃ J b, (1 / 4 : ℝ) ≤ P.real {ω | ε < |deriv (average (rareComponent J μ g (rareSign b)))
      (fullJetOutput query update output (initial ω) q (rareComponent J μ g (rareSign b)))|} := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let A (i : Fin n × Bool) : Set Ω := {ω |
    ε < |deriv (average (rareComponent i.1 μ g (rareSign i.2)))
      (fullJetOutput query update output (initial ω) q (rareComponent i.1 μ g (rareSign i.2)))|}
  have hcount (ω : Ω) : (Fintype.card (Fin n × Bool) : ℝ) * (1 / 4) ≤
      ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω := by
    have h := rare_failure_count hn query update output (initial ω) q μ g ε hε
    have hq' : (2 : ℝ) * q ≤ n := by exact_mod_cast hq
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
      Nat.cast_ofNat, Fintype.sum_prod_type, Set.indicator_apply, mem_setOf_eq]
    change (n : ℝ) * 2 * (1 / 4) ≤ ∑ J, ∑ b,
      if ε < |deriv (average (rareComponent J μ g (rareSign b)))
        (fullJetOutput query update output (initial ω) q (rareComponent J μ g (rareSign b)))|
      then (1 : ℝ) else 0
    linarith
  obtain ⟨⟨J, b⟩, h⟩ := exists_failure_probability_ge P A (fun i => hmeas i.1 i.2) (1 / 4) hcount
  exact ⟨J, b, h⟩

/-- The rare-component lower bound, with all quantifiers and the actual oracle:
for every adaptive randomized algorithm making at most `n/2` queries, there is
an admissible one-dimensional instance whose gradient exceeds `ε` with
probability at least `1/4`. Measurability is required only for the failure events. -/
theorem rare_component_lower_bound {Ω State : Type*} [MeasurableSpace Ω]
    {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p) (P : Measure Ω) [IsProbabilityMeasure P]
    (Δ ε L : ℝ) (hΔ : 0 < Δ) (hε : 0 < ε) (hL : 0 ≤ L)
    (query : State → Fin n × ℝ) (update : State → ScalarJet p → State)
    (output : State → ℝ) (initial : Ω → State) (q : ℕ) (hq : 2 * q ≤ n)
    (hmeas : ∀ f : Fin n → ℝ → ℝ, Admissible p n Δ L f →
      MeasurableSet {ω | ε < ‖deriv (average f) (fullJetOutput query update output (initial ω) q f)‖}) :
    ∃ f : Fin n → ℝ → ℝ, Admissible p n Δ L f ∧
      (1 / 4 : ℝ) ≤ P.real {ω | ε < ‖deriv (average f)
        (fullJetOutput query update output (initial ω) q f)‖} := by
  let μ := (4 * ε) ^ 2 / (2 * Δ)
  have hadm J b : Admissible p n Δ L (rareComponent J μ (4 * ε) (rareSign b)) :=
    rareComponent_admissible hn hp J Δ ε L (rareSign b) hΔ hε hL (rareSign_sq b)
  obtain ⟨J, b, h⟩ := rare_randomized_failure hn P query update output initial q hq
    μ (4 * ε) ε (by linarith) (fun J b => by
      simpa only [Real.norm_eq_abs] using hmeas _ (hadm J b))
  refine ⟨rareComponent J μ (4 * ε) (rareSign b), hadm J b, ?_⟩
  simpa only [Real.norm_eq_abs] using h

end FullJet
