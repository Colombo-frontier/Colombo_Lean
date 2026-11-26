import Bilevel.PolishedLiteralConditionalLower
import Bilevel.PolishedHistoryFreshConditional

/-! The coupled original run is the standard Borel adaptive execution
with an actual fixed conservative oracle. On each fixed mean instance,
the private seed and past iid coins generate the pre-query information;
actual source conditional moments follow from the fresh-oracle fields. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {dx du : ℕ}
  [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]
  {St Private : Type} [MeasurableSpace St] [MeasurableSpace Private]
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (A : BorelAdaptive.Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))
  (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
  (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V)
  (τ p : ℝ)

abbrev originalResponse : Unit → QuerySpace (dx:=dx) (du:=du) → Bool →
    QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du) :=
  fun _ q coin => originalReply P U hU V hV τ p coin q

omit [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem originalReply_measurable : Measurable (fun z : QuerySpace (dx:=dx) (du:=du) × Bool =>
    originalReply P U hU V hV τ p z.2 z.1) := by
  let I := framedParameters P U hU V hV
  have hg := (GradientJetBounds.gradient_contDiff I.sourceLower_contDiff).continuous
  have hg₀ := (GradientJetBounds.gradient_contDiff
    (I.inactiveSourceLower_contDiff τ (P.w P.J) (P.w_pos P.J le_rfl))).continuous
  have hf := (GradientJetBounds.gradient_contDiff I.upperJoint_contDiff).continuous
  exact (hf.measurable.comp measurable_fst).prodMk
    (ChiConservative.sample_measurable I.sourceLower (I.inactiveSourceLower τ (P.w P.J)) hg hg₀ p)

omit [BorelSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem originalRun_succ_last (draws : ℕ → Bool) :
    ∀ n t s,originalRun P A U hU V hV τ p draws (n+1) t s=
      originalStep P A U hU V hV τ p draws (t+n) (originalRun P A U hU V hV τ p draws n t s) := by
  intro n
  induction n with
  | zero => intros;rfl
  | succ n ih =>
    intro t s
    rw [originalRun,ih,originalRun]
    congr 1
    omega

omit [BorelSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (Joint (Space dx) (Space du))] in
/-- The actual original-gradient state is exactly the standard execution,
with the auxiliary activation counter erased. -/
theorem originalRun_first_eq_run (draws : ℕ → Bool) (s : St) :
    ∀ n,(originalRun P A U hU V hV τ p draws n 0 (s,0)).1=
      BorelAdaptive.run A (originalResponse P U hU V hV τ p) () draws s n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [originalRun_succ_last,BorelAdaptive.run]
    simp only [Nat.zero_add]
    let z := originalRun P A U hU V hV τ p draws n 0 (s,0)
    change (originalStep P A U hU V hV τ p draws n z).1=
      BorelAdaptive.step A (originalResponse P U hU V hV τ p) () (draws n) _
    rw [←ih]
    change (originalStep P A U hU V hV τ p draws n z).1=
      BorelAdaptive.step A (originalResponse P U hU V hV τ p) () (draws n) z.1
    by_cases hh : A.halt z.1=true <;> simp [originalStep,BorelAdaptive.step,hh,originalResponse]

variable (initial : Private → St) (hi : Measurable initial)

def originalPast (n : ℕ) (z : Private × (ℕ → Bool)) : Private × (Fin n → Bool) :=
  (z.1,BorelAdaptive.drawPrefix n z.2)

def originalInformation (n : ℕ) : MeasurableSpace (Private × (ℕ → Bool)) :=
  MeasurableSpace.comap (originalPast (Private:=Private) n) inferInstance

def originalLowerError (n : ℕ) (z : Private × (ℕ → Bool)) : QuerySpace (dx:=dx) (du:=du) :=
  let q := A.query (originalRun P A U hU V hV τ p z.2 n 0 (initial z.1,0)).1
  (originalReply P U hU V hV τ p (z.2 n) q).2-gradient (framedParameters P U hU V hV).sourceLower q

omit [BorelSpace (Joint (Space dx) (Space du))] in
include hi in
/-- Actual source conditional mean and variance for the original lower
reply, relative to all private information and all preceding coins.
Only a proved global signal envelope is required to build the fixed SFO. -/
theorem original_lower_conditional_moments (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (B σ : ℝ) (hB : 0<B)
    (henv : ∀ q : QuerySpace (dx:=dx) (du:=du),
      ‖gradient (framedParameters P U hU V hV).sourceLower q-
        gradient ((framedParameters P U hU V hV).inactiveSourceLower τ (P.w P.J)) q‖≤B)
    (n : ℕ) :
    let p := BernoulliOracle.probability B σ
    let μ := ρ.prod (IndependentStream.law (BernoulliOracle.law p (BernoulliOracle.probability_le_one hB)))
    Integrable (fun z => ‖originalLowerError P A U hU V hV τ p initial n z‖^2) μ ∧
    (μ[originalLowerError P A U hU V hV τ p initial n | originalInformation (Private:=Private) n] =ᵐ[μ] 0) ∧
    (∀ᵐ z ∂μ,μ[fun z => ‖originalLowerError P A U hU V hV τ p initial n z‖^2 |
      originalInformation (Private:=Private) n] z≤σ^2) := by
  let I := framedParameters P U hU V hV
  let p := BernoulliOracle.probability B σ
  let ν := BernoulliOracle.law p (BernoulliOracle.probability_le_one hB)
  have hg := (GradientJetBounds.gradient_contDiff I.sourceLower_contDiff).continuous
  have hg₀ := (GradientJetBounds.gradient_contDiff
    (I.inactiveSourceLower_contDiff τ (P.w P.J) (P.w_pos P.J le_rfl))).continuous
  let O := ChiConservative.freshOracle I.sourceLower (I.inactiveSourceLower τ (P.w P.J)) hg hg₀ (σ:=σ) hB henv
  let response := originalResponse P U hU V hV τ p
  have hr : Measurable (fun z : Unit × (QuerySpace (dx:=dx) (du:=du) × Bool) => response z.1 z.2.1 z.2.2) :=
    (originalReply_measurable P U hU V hV τ p).comp measurable_snd
  let query : Private × (Fin n → Bool) → QuerySpace (dx:=dx) (du:=du) := fun z =>
    A.query (BorelAdaptive.finiteRun A response n ((),(initial z.1,z.2)))
  have hq : Measurable query := A.query_measurable.comp ((BorelAdaptive.finiteRun_measurable A response hr n).comp
    (measurable_const.prodMk ((hi.comp measurable_fst).prodMk measurable_snd)))
  have hp := BorelAdaptive.initial_prefix_fresh_preserving ρ ν n
  have h := PolishedHistory.fresh_conditional_moments O (originalPast (Private:=Private) n)
    (fun z : Private × (ℕ → Bool) => z.2 n) hp query hq
  have he (z : Private × (ℕ → Bool)) :
      O.error (query (originalPast (Private:=Private) n z)) (z.2 n)=
        originalLowerError P A U hU V hV τ p initial n z := by
    have hs := originalRun_first_eq_run P A U hU V hV τ p z.2 (initial z.1) n
    rw [BorelAdaptive.run_eq_finiteRun] at hs
    change ChiConservative.sampleGradient I.sourceLower (I.inactiveSourceLower τ (P.w P.J)) p (z.2 n)
      (query (originalPast (Private:=Private) n z))-
      gradient I.sourceLower (query (originalPast (Private:=Private) n z))=_
    unfold originalLowerError
    rw [hs]
    rfl
  simpa only [he,originalInformation] using h


omit [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))] in
/-- Both retained vectors are gradients of globally defined scalar
potentials fixed by the actual mean and the one fresh coin. -/
theorem original_reply_global_potentials (coin : Bool) (q : QuerySpace (dx:=dx) (du:=du)) :
    HasGradientAt (framedParameters P U hU V hV).upperJoint
      (originalReply P U hU V hV τ p coin q).1 q ∧
    HasGradientAt (ChiConservative.samplePotential (framedParameters P U hU V hV).sourceLower
      ((framedParameters P U hU V hV).inactiveSourceLower τ (P.w P.J)) p coin)
      (originalReply P U hU V hV τ p coin q).2 q := by
  let I := framedParameters P U hU V hV
  refine ⟨(I.upperJoint_contDiff.differentiable (by norm_num) q).hasGradientAt,?_⟩
  exact ChiConservative.sample_hasGradientAt I.sourceLower (I.inactiveSourceLower τ (P.w P.J))
    (I.sourceLower_contDiff.differentiable (by norm_num))
    ((I.inactiveSourceLower_contDiff τ (P.w P.J) (P.w_pos P.J le_rfl)).differentiable (by norm_num)) p coin q

def originalUpperError (n : ℕ) (z : Private × (ℕ → Bool)) : QuerySpace (dx:=dx) (du:=du) :=
  let q := A.query (originalRun P A U hU V hV τ p z.2 n 0 (initial z.1,0)).1
  (originalReply P U hU V hV τ p (z.2 n) q).1-gradient (framedParameters P U hU V hV).upperJoint q

omit [MeasurableSpace Private] [BorelSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem original_upper_error_zero (n : ℕ) (z : Private × (ℕ → Bool)) :
    originalUpperError P A U hU V hV τ p initial n z=0 := sub_self _

omit [BorelSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (Joint (Space dx) (Space du))] in
/-- The upper reply is exact on the same actual execution and fresh-coin
probability space, so its source conditional error and variance are zero. -/
theorem original_upper_conditional_moments (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (hp1 : p≤1) (σf : ℝ) (n : ℕ) :
    let μ := ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))
    Integrable (fun z => ‖originalUpperError P A U hU V hV τ p initial n z‖^2) μ ∧
    (μ[originalUpperError P A U hU V hV τ p initial n | originalInformation (Private:=Private) n] =ᵐ[μ] 0) ∧
    (∀ᵐ z ∂μ,μ[fun z => ‖originalUpperError P A U hU V hV τ p initial n z‖^2 |
      originalInformation (Private:=Private) n] z≤σf^2) := by
  have he : originalUpperError P A U hU V hV τ p initial n=(0:Private × (ℕ → Bool) → QuerySpace (dx:=dx) (du:=du)) := by
    funext z
    exact original_upper_error_zero P A U hU V hV τ p initial n z
  simp only [he,Pi.zero_apply,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
  refine ⟨integrable_zero _ _ _,?_,?_⟩
  · simp only [condExp_zero]
    exact Filter.EventuallyEq.rfl
  · change ∀ᵐ z ∂(ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))),
      (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))[
        (0:Private × (ℕ → Bool) → ℝ) | originalInformation (Private:=Private) n] z≤σf^2
    rw [condExp_zero]
    exact Filter.Eventually.of_forall (fun _ => sq_nonneg σf)

end Bilevel.PolishedLiteralActualObserver
