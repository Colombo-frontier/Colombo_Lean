import Geode.LowerReduction
import Geode.UpperAlgorithm

/-! The open-ball localization model, its upper bound, and the exact reduction
of its lower bound to the closed-ball failure witness at radius 3R/4. -/
namespace Geode.Lorentz

open Geode.OracleReplay
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure StrictAdmissibleObjective (o : Point E) (R L : ℝ) (f : Point E → ℝ) : Prop where
  convex : GConvexFunction f
  lipschitz : ∀ x y, |f x - f y| ≤ L * dist x y
  minimizer : ∃ p, dist o p < R ∧ ∀ y, f p ≤ f y

theorem StrictAdmissibleObjective.toAdmissible {o : Point E} {R L : ℝ}
    {f : Point E → ℝ} (hf : StrictAdmissibleObjective o R L f) :
    AdmissibleObjective o R L f := by
  obtain ⟨p, hp, hmin⟩ := hf.minimizer
  exact ⟨hf.convex, hf.lipschitz, p, hp.le, hmin⟩

theorem AdmissibleObjective.toStrict {o : Point E} {R₀ R L : ℝ}
    {f : Point E → ℝ} (hf : AdmissibleObjective o R₀ L f) (hR : R₀ < R) :
    StrictAdmissibleObjective o R L f := by
  obtain ⟨p, hp, hmin⟩ := hf.minimizer
  exact ⟨hf.convex, hf.lipschitz, p, hp.trans_lt hR, hmin⟩

def StrictGuarantees (o : Point E) (R L ε : ℝ) (N : ℕ)
    (A : FirstOrderAlgorithm E) : Prop :=
  ∀ f : Point E → ℝ, StrictAdmissibleObjective o R L f →
    ∀ O : Point E → FirstOrderReply E, LegalOracle f O →
      ∃ history output, run A (fixedResponder O) N [] = .finished history output ∧
        ∀ p : Point E, (∀ y, f p ≤ f y) → f output - f p ≤ ε * L * R

def StrictFeasibleBudget (o : Point E) (R L ε : ℝ) (N : ℕ) : Prop :=
  ∃ A : FirstOrderAlgorithm E, StrictGuarantees o R L ε N A

noncomputable def strictQueryComplexity (o : Point E) (R L ε : ℝ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (_ : StrictFeasibleBudget o R L ε N), (N : ℝ≥0∞)

noncomputable def strictDimensionComplexity (d : ℕ) (R L ε : ℝ) : ℝ≥0∞ :=
  strictQueryComplexity (origin : HyperbolicSpace d) R L ε

noncomputable def strictUniformComplexity (R L ε : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (_ : 2 ≤ d), strictDimensionComplexity d R L ε

theorem Guarantees.toStrict {o : Point E} {R L ε : ℝ} {N : ℕ}
    {A : FirstOrderAlgorithm E} (hA : Guarantees o R L ε N A) :
    StrictGuarantees o R L ε N A := fun f hf O hO => hA f hf.toAdmissible O hO

theorem StrictGuarantees.mono_budget {o : Point E} {R L ε : ℝ} {n N : ℕ}
    {A : FirstOrderAlgorithm E} (hA : StrictGuarantees o R L ε n A) (hn : n ≤ N) :
    StrictGuarantees o R L ε N A := by
  intro f hf O hO
  obtain ⟨h, output, hrun, hgap⟩ := hA f hf O hO
  exact ⟨h, output, run_mono_fuel_of_finished A (fixedResponder O) hn [] h output hrun, hgap⟩

theorem StrictFeasibleBudget.mono_budget {o : Point E} {R L ε : ℝ} {n N : ℕ}
    (h : StrictFeasibleBudget o R L ε n) (hn : n ≤ N) :
    StrictFeasibleBudget o R L ε N := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA.mono_budget hn⟩

theorem strictQueryComplexity_le_of_feasible {o : Point E} {R L ε : ℝ} {N : ℕ}
    (h : StrictFeasibleBudget o R L ε N) :
    strictQueryComplexity o R L ε ≤ (N : ℝ≥0∞) :=
  iInf_le_of_le N (iInf_le_of_le h le_rfl)

theorem strictQueryComplexity_lower_of_no_budget {o : Point E} {R L ε : ℝ} {T : ℕ}
    (h : ∀ N ≤ T, ¬ StrictFeasibleBudget o R L ε N) :
    ((T + 1 : ℕ) : ℝ≥0∞) ≤ strictQueryComplexity o R L ε := by
  apply le_iInf
  intro N
  apply le_iInf
  intro hN
  have hlt : T < N := by
    by_contra hn
    exact h N (Nat.le_of_not_gt hn) hN
  exact_mod_cast Nat.succ_le_of_lt hlt

theorem strictDimensionComplexity_le_uniform {d : ℕ} (hd : 2 ≤ d) (R L ε : ℝ) :
    strictDimensionComplexity d R L ε ≤ strictUniformComplexity R L ε :=
  le_iSup_of_le d (le_iSup_of_le hd le_rfl)

theorem strictQueryComplexity_upper (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    strictQueryComplexity o R L ε ≤ (upperQueryBudget R ε : ℝ≥0∞) :=
  strictQueryComplexity_le_of_feasible
    ⟨projectedAlgorithm o R L ε hR.le, (projectedAlgorithm_guarantees o hR hL hε).toStrict⟩

theorem strictUniformComplexity_upper {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    strictUniformComplexity R L ε ≤ (⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ : ℝ≥0∞) := by
  apply iSup_le
  intro d
  apply iSup_le
  intro _hd
  exact (strictQueryComplexity_upper (origin : HyperbolicSpace d) hR hL hε).trans
    (by exact_mod_cast upperQueryBudget_le_three (ε := ε) hR)

theorem strict_not_feasible_of_failure_witness {o : Point E} {R L ε : ℝ} {T : ℕ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε)
    (hw : HorizonFailureWitness o (3 * R / 4) L ε T) :
    ¬ StrictFeasibleBudget o R L ε T := by
  rintro ⟨A, hA⟩
  obtain ⟨f, O, p, hf, hO, hp, hfail⟩ := hw A
  obtain ⟨history, output, hrun, hgap⟩ := hA f (hf.toStrict (by linarith)) O hO
  rw [hrun] at hfail
  change 2 * ε * L * (3 * R / 4) ≤ f output - f p at hfail
  have hgood := hgap p hp
  have hpos : 0 < ε * L * R := mul_pos (mul_pos hε hL) hR
  nlinarith only [hfail, hgood, hpos]

theorem strictQueryComplexity_lower_of_failure_witness {o : Point E} {R L ε : ℝ} {T : ℕ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε)
    (hw : HorizonFailureWitness o (3 * R / 4) L ε T) :
    ((T + 1 : ℕ) : ℝ≥0∞) ≤ strictQueryComplexity o R L ε := by
  apply strictQueryComplexity_lower_of_no_budget
  intro N hN hfeasible
  exact strict_not_feasible_of_failure_witness hR hL hε hw (hfeasible.mono_budget hN)

theorem strictUniformComplexity_lower_of_failure_witness {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hw : HorizonFailureWitness
      (origin : HyperbolicSpace (Geode.queryHorizon (3 * R / 4) ε + 2))
      (3 * R / 4) L ε (Geode.queryHorizon (3 * R / 4) ε)) :
    ENNReal.ofReal (3 * Geode.curvatureFactor R / (1040 * ε ^ 2)) ≤
      strictUniformComplexity R L ε := by
  have hR₀ : 0 < 3 * R / 4 := by linarith
  have hfactor : 3 * Geode.curvatureFactor R / (1040 * ε ^ 2) ≤
      Geode.curvatureFactor (3 * R / 4) / (260 * ε ^ 2) := by
    have h := div_le_div_of_nonneg_right (Geode.strict_localization_factor hR)
      (show 0 ≤ 260 * ε ^ 2 by positivity)
    convert h using 1 <;> ring
  have hscalar : ENNReal.ofReal (3 * Geode.curvatureFactor R / (1040 * ε ^ 2)) ≤
      ((Geode.queryHorizon (3 * R / 4) ε + 1 : ℕ) : ℝ≥0∞) := by
    apply ENNReal.ofReal_le_natCast.mpr
    exact_mod_cast (hfactor.trans_lt (Geode.uniform_horizon_bound hR₀ hε hεmax)).le
  exact hscalar.trans ((strictQueryComplexity_lower_of_failure_witness hR hL hε hw).trans
    (strictDimensionComplexity_le_uniform (by omega) R L ε))

end Geode.Lorentz
