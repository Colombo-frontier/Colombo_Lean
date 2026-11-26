import Bilevel.PolishedHistoryFreshConditional

/-! Actual random-initial source executions for every stationary fresh
instance and every randomized Borel algorithm. The pre-query sigma-algebra
contains the entire private seed and all earlier original draws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery BorelAdaptive PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (A : Algorithm G)

abbrev FreshSourceSpace := A.Private × IndependentStream.Stream I.Seed

def freshSourceLaw : Measure (FreshSourceSpace I A) :=
  A.privateLaw.prod (IndependentStream.law I.law)
instance freshSourceLaw_probability : IsProbabilityMeasure (freshSourceLaw I A) := by
  unfold freshSourceLaw
  infer_instance

def freshSourcePast (n : ℕ) (z : FreshSourceSpace I A) : A.Private × (Fin n → I.Seed) :=
  (z.1,drawPrefix n z.2)

def freshSourceInformation (n : ℕ) : MeasurableSpace (FreshSourceSpace I A) :=
  MeasurableSpace.comap (freshSourcePast I A n) inferInstance

def freshSourceState (n : ℕ) (z : FreshSourceSpace I A) : A.State :=
  BorelAdaptive.run A.program I.reply () z.2 (A.start z.1) n

def freshSourceObservation (n : ℕ) (z : FreshSourceSpace I A) : G.Reply :=
  I.reply () (A.program.query (freshSourceState I A n z)) (z.2 n)

theorem freshSourcePast_measurable (n : ℕ) : Measurable (freshSourcePast I A n) :=
  measurable_fst.prodMk ((drawPrefix_measurable n).comp measurable_snd)

theorem freshSourceInformation_le (n : ℕ) : freshSourceInformation I A n ≤ (inferInstance : MeasurableSpace (FreshSourceSpace I A)) :=
  (freshSourcePast_measurable I A n).comap_le

private theorem seed_nonempty : Nonempty I.Seed := by
  by_contra h
  have hz : I.law Set.univ=0 := by
    rw [Set.univ_eq_empty_iff.mpr (not_nonempty_iff.mp h),measure_empty]
  rw [measure_univ] at hz
  exact one_ne_zero hz

private theorem freshSourceState_prefix [Inhabited I.Seed] (n : ℕ) :
    freshSourceState I A n=(fun z => finiteRun A.program I.reply n ((),(A.start z.1,z.2))) ∘ freshSourcePast I A n := by
  funext z
  exact run_eq_finiteRun A.program I.reply () z.2 (A.start z.1) n

private theorem freshSourceFiniteState_measurable [Inhabited I.Seed] (n : ℕ) :
    Measurable (fun z : A.Private × (Fin n → I.Seed) => finiteRun A.program I.reply n ((),(A.start z.1,z.2))) :=
  (finiteRun_measurable A.program I.reply I.reply_measurable n).comp
    (measurable_const.prodMk ((A.start_measurable.comp measurable_fst).prodMk measurable_snd))

theorem freshSourceState_information (n : ℕ) :
    Measurable[freshSourceInformation I A n] (freshSourceState I A n) := by
  letI : Nonempty I.Seed := seed_nonempty I
  letI : Inhabited I.Seed := Classical.inhabited_of_nonempty (seed_nonempty I)
  rw [freshSourceState_prefix I A n]
  exact (freshSourceFiniteState_measurable I A n).comp (Measurable.of_comap_le le_rfl)

theorem freshSourceState_measurable (n : ℕ) : Measurable (freshSourceState I A n) :=
  (freshSourceState_information I A n).mono (freshSourceInformation_le I A n) le_rfl

theorem freshSourceObservation_measurable (n : ℕ) : Measurable (freshSourceObservation I A n) :=
  I.reply_measurable.comp (measurable_const.prodMk
    ((A.program.query_measurable.comp (freshSourceState_measurable I A n)).prodMk
      ((measurable_pi_apply n).comp measurable_snd)))

theorem freshSourceInformation_mono : Monotone (freshSourceInformation I A) := by
  intro n m hnm
  let truncate : A.Private × (Fin m → I.Seed) → A.Private × (Fin n → I.Seed) :=
    fun z => (z.1,fun i => z.2 ⟨i.val,lt_of_lt_of_le i.isLt hnm⟩)
  have ht : Measurable truncate := measurable_fst.prodMk
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply (⟨i.val,lt_of_lt_of_le i.isLt hnm⟩ : Fin m)).comp measurable_snd))
  have he : freshSourcePast I A n=truncate ∘ freshSourcePast I A m := rfl
  have hp : Measurable[freshSourceInformation I A m] (freshSourcePast I A m) := Measurable.of_comap_le le_rfl
  have hsmall : Measurable[freshSourceInformation I A m] (freshSourcePast I A n) := by
    rw [he]
    exact ht.comp hp
  exact hsmall.comap_le

theorem freshSourceObservation_information (n : ℕ) :
    Measurable[freshSourceInformation I A (n+1)] (freshSourceObservation I A n) := by
  have hs : Measurable[freshSourceInformation I A (n+1)] (freshSourceState I A n) :=
    (freshSourceState_information I A n).mono (freshSourceInformation_mono I A (Nat.le_succ n)) le_rfl
  have hp : Measurable[freshSourceInformation I A (n+1)] (freshSourcePast I A (n+1)) := Measurable.of_comap_le le_rfl
  have hd : Measurable[freshSourceInformation I A (n+1)] (fun z : FreshSourceSpace I A => z.2 n) :=
    ((measurable_pi_apply (Fin.last n)).comp measurable_snd).comp hp
  exact I.reply_measurable.comp (measurable_const.prodMk
    ((A.program.query_measurable.comp hs).prodMk hd))

theorem freshSourceState_initial (z : FreshSourceSpace I A) : freshSourceState I A 0 z=A.start z.1 := rfl

theorem freshSourceState_next (n : ℕ) (z : FreshSourceSpace I A) :
    freshSourceState I A (n+1) z=if A.program.halt (freshSourceState I A n z)=true
      then freshSourceState I A n z else A.program.update (freshSourceState I A n z,freshSourceObservation I A n z) := rfl

def freshSourceError {σ : ℝ} (O : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) I.law σ)
    (n : ℕ) (z : FreshSourceSpace I A) : G.Query :=
  O.error (A.program.query (freshSourceState I A n z)) (z.2 n)

/-- Actual conditional mean and variance for any one of the retained full
vectors, relative to all private information and all past original draws. -/
theorem freshSourceOracle_moments {σ : ℝ} (O : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) I.law σ)
    (n : ℕ) :
    Integrable (fun z => ‖freshSourceError I A O n z‖^2) (freshSourceLaw I A) ∧
    ((freshSourceLaw I A)[freshSourceError I A O n | freshSourceInformation I A n] =ᵐ[freshSourceLaw I A] 0) ∧
    (∀ᵐ z ∂freshSourceLaw I A,(freshSourceLaw I A)[fun z => ‖freshSourceError I A O n z‖^2 |
      freshSourceInformation I A n] z≤σ^2) := by
  letI : Nonempty I.Seed := seed_nonempty I
  letI : Inhabited I.Seed := Classical.inhabited_of_nonempty (seed_nonempty I)
  let query : A.Private × (Fin n → I.Seed) → G.Query := fun z =>
    A.program.query (finiteRun A.program I.reply n ((),(A.start z.1,z.2)))
  have hq : Measurable query := A.program.query_measurable.comp (freshSourceFiniteState_measurable I A n)
  have hp := initial_prefix_fresh_preserving A.privateLaw I.law n
  have hh := fresh_conditional_moments O (freshSourcePast I A n) (fun z : FreshSourceSpace I A => z.2 n) hp query hq
  have he : (fun z : FreshSourceSpace I A => O.error (query (freshSourcePast I A n z)) (z.2 n))=
      freshSourceError I A O n := by
    funext z
    have hs := congrFun (freshSourceState_prefix I A n) z
    change O.error (query (freshSourcePast I A n z)) (z.2 n)=
      O.error (A.program.query (freshSourceState I A n z)) (z.2 n)
    rw [hs]
    rfl
  have hePoint (z : FreshSourceSpace I A) : O.error (query (freshSourcePast I A n z)) (z.2 n)=freshSourceError I A O n z := congrFun he z
  simpa only [hePoint,freshSourceLaw,freshSourceInformation] using hh

/-- Both returned channels use the same original draw, retaining arbitrary
within-call correlation. Conservative instances retain their same globally defined scalar potentials. -/
structure ConditionalFreshRunCertificate : Prop where
  state_measurable : ∀ n,Measurable (freshSourceState I A n)
  observation_measurable : ∀ n,Measurable (freshSourceObservation I A n)
  adapted : ∀ n,Measurable[freshSourceInformation I A n] (freshSourceState I A n)
  initial : ∀ z,freshSourceState I A 0 z=A.start z.1
  next : ∀ n z,freshSourceState I A (n+1) z=if A.program.halt (freshSourceState I A n z)=true
    then freshSourceState I A n z else A.program.update (freshSourceState I A n z,freshSourceObservation I A n z)
  upper_square_integrable : ∀ n,Integrable (fun z => ‖freshSourceError I A I.upper n z‖^2) (freshSourceLaw I A)
  lower_square_integrable : ∀ n,Integrable (fun z => ‖freshSourceError I A I.lower n z‖^2) (freshSourceLaw I A)
  upper_mean : ∀ n,(freshSourceLaw I A)[freshSourceError I A I.upper n | freshSourceInformation I A n] =ᵐ[freshSourceLaw I A] 0
  lower_mean : ∀ n,(freshSourceLaw I A)[freshSourceError I A I.lower n | freshSourceInformation I A n] =ᵐ[freshSourceLaw I A] 0
  upper_variance : ∀ n,∀ᵐ z ∂freshSourceLaw I A,(freshSourceLaw I A)[fun z => ‖freshSourceError I A I.upper n z‖^2 |
    freshSourceInformation I A n] z≤σf^2
  lower_variance : ∀ n,∀ᵐ z ∂freshSourceLaw I A,(freshSourceLaw I A)[fun z => ‖freshSourceError I A I.lower n z‖^2 |
    freshSourceInformation I A n] z≤σg^2

theorem stationary_actual_source_admissible : ConditionalFreshRunCertificate I A where
  state_measurable:=freshSourceState_measurable I A
  observation_measurable:=freshSourceObservation_measurable I A
  adapted:=freshSourceState_information I A
  initial:=freshSourceState_initial I A
  next:=freshSourceState_next I A
  upper_square_integrable:=fun n => (freshSourceOracle_moments I A I.upper n).1
  lower_square_integrable:=fun n => (freshSourceOracle_moments I A I.lower n).1
  upper_mean:=fun n => (freshSourceOracle_moments I A I.upper n).2.1
  lower_mean:=fun n => (freshSourceOracle_moments I A I.lower n).2.1
  upper_variance:=fun n => (freshSourceOracle_moments I A I.upper n).2.2
  lower_variance:=fun n => (freshSourceOracle_moments I A I.lower n).2.2

/-- This is the actual source error with the retained primitive gradient,
not a surrogate truth field. -/
theorem freshSource_upper_error (n : ℕ) (z : FreshSourceSpace I A) :
    freshSourceError I A I.upper n z=(freshSourceObservation I A n z).1-
      pack (I.primitive.fx (A.program.query (freshSourceState I A n z)).fst (A.program.query (freshSourceState I A n z)).snd)
        (I.primitive.fy (A.program.query (freshSourceState I A n z)).fst (A.program.query (freshSourceState I A n z)).snd) := by
  unfold freshSourceError FreshOracle.Oracle.error
  rw [I.upper_truth]
  rfl

theorem freshSource_lower_error (n : ℕ) (z : FreshSourceSpace I A) :
    freshSourceError I A I.lower n z=(freshSourceObservation I A n z).2-
      pack (I.primitive.gx (A.program.query (freshSourceState I A n z)).fst (A.program.query (freshSourceState I A n z)).snd)
        (I.primitive.gy (A.program.query (freshSourceState I A n z)).fst (A.program.query (freshSourceState I A n z)).snd) := by
  unfold freshSourceError FreshOracle.Oracle.error
  rw [I.lower_truth]
  rfl

/-- The same source random-initial path is used for both returned
conditional moments and the original stopping cost/risk. -/
def freshSourcePath (z : FreshSourceSpace I A) : HistoryProgram.Path A.State Unit :=
  fun n => (freshSourceState I A n z,())

theorem freshSourcePath_eq_seedPath : freshSourcePath I A=seedPath I A := rfl

def freshSourceCost : ℝ≥0∞ :=
  ∫⁻ z,HistoryProgram.totalCalls A.program (freshSourcePath I A z) ∂freshSourceLaw I A

def freshSourceRisk : ℝ≥0∞ :=
  ∫⁻ z,ENNReal.ofReal (I.loss (HistoryProgram.stoppedOutput A.program
    (freshSourcePath I A z))) ∂freshSourceLaw I A

theorem freshSourceCost_eq : freshSourceCost I A=I.cost A := rfl

theorem freshSourceRisk_eq : freshSourceRisk I A=I.risk A := rfl

end Bilevel.PolishedHistory
