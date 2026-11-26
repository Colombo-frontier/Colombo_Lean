import FullJet.VerifiedOracle
import FullJet.ConstantSuccessMethod

open MeasureTheory

namespace FullJet

theorem upperSeed_nonempty (p n : ℕ) (Δ L ε : ℝ) (m B : ℕ)
    (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hm : 0 < m) (hn : 0 < n) :
    Nonempty (UpperSeed p Δ L ε m B n) :=
  ⟨Classical.choose (upperSeedLaw p Δ L ε m B n hΔ hL hε hm hn).support_nonempty⟩

noncomputable def verifiedSeedLaw (p n : ℕ) (Δ L ε : ℝ) (m B K : ℕ)
    (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hm : 0 < m) (hn : 0 < n) :
    PMF (Fin K → UpperSeed p Δ L ε m B n) := by
  letI := upperSeed_nonempty p n Δ L ε m B hΔ hL hε hm hn
  exact PMF.uniformOfFintype _

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n : ℕ}

theorem Admissible.verifiedUpper_failure_le {f : Fin n → E → ℝ} {Δ L ε : ℝ}
    (hf : Admissible p n Δ L f) (hp : 2 ≤ p) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε)
    (m B K : ℕ) (hm : 0 < m) (hB : 0 < B) :
    ((verifiedSeedLaw p n Δ L ε m B K hΔ hL hε hm hf.n_pos).toOuterMeasure
      {seeds | ε < ‖fderiv ℝ (average f)
        (verifiedEpochOutput (p := p) (by omega) f (upperModelScale p L m B) (upperRadius p L ε m B) ε
          (upperRadius_pos p L ε m B hL hε).le K seeds)‖}).toReal ≤ (1 / 4 : ℝ) ^ K := by
  classical
  letI := upperSeed_nonempty p n Δ L ε m B hΔ hL hε hm hf.n_pos
  let candidate := upperCandidate (p := p) (by omega) f Δ L ε m B hL hε
  let accept := fun x : E => ‖fderiv ℝ (average f) x‖ ≤ ε
  have hsingle : ((PMF.uniformOfFintype (UpperSeed p Δ L ε m B n)).toOuterMeasure
      {a | ¬ accept (candidate a)}).toReal ≤ 1 / 4 := by
    simpa only [accept, not_le] using hf.upperCandidate_failure_quarter hp hΔ hL hε m B hm hB
  have h := validatedChoice_failure_probability (0 : E) accept candidate K
  have hpow := pow_le_pow_left₀ ENNReal.toReal_nonneg hsingle K
  have hfinal := h.trans hpow
  simpa only [accept, not_le] using hfinal

noncomputable def verifiedQueryBudget (p n : ℕ) (Δ L ε : ℝ) (m B K : ℕ) : ℕ :=
  K * (upperQueryBudget p n Δ L ε m B + n)

/-- Independent finite repetition with paid exact validation, as an actual
uniform family of one-reply-per-step algorithms. -/
noncomputable def verifiedJetMethod (p n : ℕ) (hp : 1 ≤ p) (hn : 0 < n)
    (Δ L ε : ℝ) (m B K : ℕ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hm : 0 < m) :
    RandomizedJetMethod n p := by
  letI : MeasurableSpace (Fin K → UpperSeed p Δ L ε m B n) := ⊤
  exact {
    Seed := Fin K → UpperSeed p Δ L ε m B n
    seedSpace := ⊤
    law := (verifiedSeedLaw p n Δ L ε m B K hΔ hL hε hm hn).toMeasure
    probability := inferInstance
    algorithm := fun E _ _ _ => verifiedJetAlgorithm hp ⟨0, hn⟩
      (upperModelScale p L m B) (upperRadius p L ε m B) ε
      (upperRadius_pos p L ε m B hL hε).le K }

theorem verifiedJetMethod_succeeds (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε : ℝ) (m B K : ℕ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε)
    (hm : 0 < m) (hB : 0 < B) :
    (verifiedJetMethod p n (by omega) hn Δ L ε m B K hΔ hL hε hm).succeeds
      (verifiedQueryBudget p n Δ L ε m B K) Δ L ε ((1 / 4 : ℝ) ^ K) := by
  letI : MeasurableSpace (Fin K → UpperSeed p Δ L ε m B n) := ⊤
  change ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    (verifiedJetAlgorithm (E := E) (H := upperEpochCount p Δ L ε m B) (m := m) (B := B)
      (by omega) ⟨0, hn⟩ (upperModelScale p L m B) (upperRadius p L ε m B) ε
      (upperRadius_pos p L ε m B hL hε).le K).succeeds
      (verifiedSeedLaw p n Δ L ε m B K hΔ hL hε hm hn).toMeasure
      (K * (upperEpochCount p Δ L ε m B * epochQueryCost n m B + n)) Δ L ε ((1 / 4 : ℝ) ^ K)
  intro E _ _ _
  constructor
  · intro f hf
    exact measurable_of_finite _
  · intro f hf
    change ((verifiedSeedLaw p n Δ L ε m B K hΔ hL hε hm hn).toMeasure
      {seeds | ε < ‖fderiv ℝ (average f)
        ((verifiedJetAlgorithm (by omega) ⟨0, hn⟩ (upperModelScale p L m B)
          (upperRadius p L ε m B) ε (upperRadius_pos p L ε m B hL hε).le K).result
          (K * (upperEpochCount p Δ L ε m B * epochQueryCost n m B + n)) f seeds)‖}).toReal ≤ _
    simp only [verifiedJetAlgorithm_result hf.smooth]
    rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ _ (Set.toFinite _).measurableSet]
    exact hf.verifiedUpper_failure_le hp hΔ hL hε m B K hm hB

theorem verifiedJetMethod_succeeds_of_pow_le (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε δ : ℝ) (m B K : ℕ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε)
    (hm : 0 < m) (hB : 0 < B) (hK : (1 / 4 : ℝ) ^ K ≤ δ) :
    (verifiedJetMethod p n (by omega) hn Δ L ε m B K hΔ hL hε hm).succeeds
      (verifiedQueryBudget p n Δ L ε m B K) Δ L ε δ := by
  have h := verifiedJetMethod_succeeds p n hp hn Δ L ε m B K hΔ hL hε hm hB
  intro E _ _ _
  exact ⟨(h E).1, fun f hf => ((h E).2 f hf).trans hK⟩

theorem oracleComplexity_verified_upper (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε δ : ℝ) (m B K : ℕ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε)
    (hm : 0 < m) (hB : 0 < B) (hK : (1 / 4 : ℝ) ^ K ≤ δ) :
    oracleComplexity n p Δ L ε δ ≤ verifiedQueryBudget p n Δ L ε m B K :=
  oracleComplexity_le_of_method (verifiedJetMethod p n (by omega) hn Δ L ε m B K hΔ hL hε hm)
    Δ L ε δ (verifiedJetMethod_succeeds_of_pow_le p n hp hn Δ L ε δ m B K hΔ hL hε hm hB hK)

theorem oracleComplexity_finite (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hδ : 0 < δ) :
    oracleComplexity n p Δ L ε δ < ⊤ := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 4 : ℝ) < 1 by norm_num)
  exact (oracleComplexity_verified_upper p n hp hn Δ L ε δ 1 1 K hΔ hL hε
    (by omega) (by omega) hK.le).trans_lt (ENNReal.natCast_lt_top _)

end FullJet
