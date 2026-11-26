import LeanArticleAudit.Pilot.UpperInterfaces
import LeanArticleAudit.Pilot.UpperHalpern
import LeanArticleAudit.Pilot.UpperPowerMean
import LeanArticleAudit.Pilot.Resolvent
import LeanArticleAudit.Pilot.ApproxRecovery

/-!
# Executable oracle conversion for the exponent boost

This file supplies the operational layer of `thm:boost`.  In particular, a
query to `G_x(z) = F(z) + (1 / eta) • (z - x)` is compiled to exactly one
query to the original `F` oracle; the affine part of every derivative is
computed locally.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

section JetConversion

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The known affine term used in a regularized inner operator. -/
def affineRegularizer (eta : ℝ) (center : E) : E → E :=
  fun z => (1 / eta) • (z - center)

/-- The regularized inner operator from the article. -/
def regularizedOperator (F : E → E) (eta : ℝ) (center : E) : E → E :=
  fun z => F z + affineRegularizer eta center z

theorem affineRegularizer_contDiff (eta : ℝ) (center : E) :
    ContDiff ℝ ⊤ (affineRegularizer eta center) := by
  exact (contDiff_id.sub contDiff_const).const_smul (1 / eta)

theorem IsAdmissibleOperator.contDiffAt_on
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (x : E) (hx : x ∈ data.X) :
    ContDiffAt ℝ (data.p - 1 : ℕ) F x := by
  obtain ⟨U, hUopen, hXU, hreg⟩ := hF.regularity
  exact (hreg x (hXU hx)).contDiffAt (hUopen.mem_nhds (hXU hx))

theorem iteratedFDeriv_id_independent (n : ℕ) (hn : 0 < n) (x y : E) :
    iteratedFDeriv ℝ n (id : E → E) x =
      iteratedFDeriv ℝ n (id : E → E) y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  cases n with
  | zero =>
      ext v
      simp [iteratedFDeriv_one_apply, fderiv_id]
  | succ n =>
      rw [iteratedFDeriv_succ_eq_comp_right,
        iteratedFDeriv_succ_eq_comp_right]
      simp only [fderiv_id]
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)
        (ContinuousLinearMap.id ℝ E)]
      rfl

theorem affineRegularizer_iteratedFDeriv_independent
    (eta : ℝ) (center : E) (n : ℕ) (hn : 0 < n) (x y : E) :
    iteratedFDeriv ℝ n (affineRegularizer eta center) x =
      iteratedFDeriv ℝ n (affineRegularizer eta center) y := by
  have hinner : ContDiff ℝ ⊤ (fun z : E => z - center) :=
    contDiff_id.sub contDiff_const
  have hx : ContDiffAt ℝ n (fun z : E => z - center) x :=
    hinner.contDiffAt.of_le le_top
  have hy : ContDiffAt ℝ n (fun z : E => z - center) y :=
    hinner.contDiffAt.of_le le_top
  change iteratedFDeriv ℝ n (fun z : E => (1 / eta) • (z - center)) x =
    iteratedFDeriv ℝ n (fun z : E => (1 / eta) • (z - center)) y
  rw [iteratedFDeriv_const_smul_apply' hx,
    iteratedFDeriv_const_smul_apply' hy]
  congr 1
  rw [show (fun z : E => z - center) = (id : E → E) - fun _ => center by rfl]
  rw [iteratedFDeriv_sub_apply contDiff_id.contDiffAt contDiffAt_const,
    iteratedFDeriv_sub_apply contDiff_id.contDiffAt contDiffAt_const]
  rw [iteratedFDeriv_id_independent n hn x y]
  have hconst : (iteratedFDeriv ℝ n (fun _ : E => center)) = 0 :=
    iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn) center
  rw [congrFun hconst x, congrFun hconst y]
  change iteratedFDeriv ℝ n id y - 0 = iteratedFDeriv ℝ n id y - 0
  rfl

/-- Exact symmetric jet of the locally known affine correction. -/
def affineRegularizerJet (p : ℕ) (eta : ℝ) (center point : E) :
    SymmetricExactJet E p :=
  exactSymmetricJetOf E p (affineRegularizer eta center) point (fun j σ =>
    ContDiffAt.domDomCongr_iteratedFDeriv
      (affineRegularizer_contDiff eta center).contDiffAt σ)

/-- Pointwise addition in the symmetric-jet subtype. -/
def addSymmetricJet {p : ℕ} (first second : SymmetricExactJet E p) :
    SymmetricExactJet E p := fun j =>
  ⟨(first j).1 + (second j).1, by
    intro σ
    ext v
    have hfirst := congrArg (fun f : E [×j.1]→L[ℝ] E => f v) ((first j).2 σ)
    have hsecond := congrArg (fun f : E [×j.1]→L[ℝ] E => f v) ((second j).2 σ)
    simpa [ContinuousMultilinearMap.domDomCongr_apply] using
      congrArg₂ (fun a b : E => a + b) hfirst hsecond⟩

/-- Transform one returned `F` jet into the corresponding regularized jet.
No value depending on `F` other than `base` is used. -/
def regularizedJetAnswer (p : ℕ) (eta : ℝ) (center point : E)
    (base : SymmetricExactJet E p) : SymmetricExactJet E p :=
  addSymmetricJet base (affineRegularizerJet p eta center point)

theorem regularizedJetAnswer_exact
    (data : VIPublicData E) (F : E → E)
    (point : data.X)
    (base : SymmetricExactJet E data.p)
    (hbase : ∀ j : Fin data.p,
      (base j).1 = iteratedFDeriv ℝ j.1 F point.1)
    (hF : ∀ x ∈ data.X, ContDiffAt ℝ (data.p - 1 : ℕ) F x)
    (eta : ℝ) (center : E) (j : Fin data.p) :
    ((regularizedJetAnswer data.p eta center point.1
      base) j).1 =
      iteratedFDeriv ℝ j.1 (regularizedOperator F eta center) point.1 := by
  rw [show regularizedOperator F eta center = F + affineRegularizer eta center by rfl]
  rw [iteratedFDeriv_add_apply]
  · simp only [regularizedJetAnswer, addSymmetricJet, affineRegularizerJet,
      exactSymmetricJetOf]
    rw [hbase]
  · exact (hF point.1 point.2).of_le (by
      exact_mod_cast Nat.le_pred_of_lt j.2)
  · exact (affineRegularizer_contDiff eta center).contDiffAt.of_le le_top

/-- The exact regularized oracle on feasible query points.  Its answer
function visibly applies a pure local transformation to one original answer. -/
def regularizedFeasibleOracle
    (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : ∀ x ∈ data.X, ContDiffAt ℝ (data.p - 1 : ℕ) F x)
    (eta : ℝ) (center : E) :
    FeasibleExactSymmetricJetOracle data (regularizedOperator F eta center) where
  answer point := regularizedJetAnswer data.p eta center point.1 (oracle.answer point)
  exact point j := regularizedJetAnswer_exact data F point (oracle.answer point)
    (oracle.exact point) hF eta center j

end JetConversion

section ProgramConversion

variable {X Answer₁ Answer₂ Output : Type*}

/-- Compile a program for derived answers into a program for base answers.
Every derived query becomes exactly one base query at the same point. -/
def ExactJetProgram.mapAnswers
    (transform : X → Answer₁ → Answer₂) :
    ExactJetProgram X Answer₂ Output → ExactJetProgram X Answer₁ Output
  | .halt result => .halt result
  | .query point next =>
      .query point (fun answer => (next (transform point answer)).mapAnswers transform)

theorem ExactJetProgram.mapAnswers_runWithFuel
    (transform : X → Answer₁ → Answer₂)
    (oracle : X → Answer₁) (fuel : ℕ)
    (program : ExactJetProgram X Answer₂ Output) :
    (program.mapAnswers transform).runWithFuel oracle fuel =
      program.runWithFuel (fun x => transform x (oracle x)) fuel := by
  induction fuel generalizing program with
  | zero => cases program <;> rfl
  | succ fuel ih =>
      cases program with
      | halt result => rfl
      | query point next =>
          simp only [ExactJetProgram.mapAnswers, ExactJetProgram.runWithFuel]
          rw [ih (next (transform point (oracle point)))]

theorem ExactJetProgram.mapAnswers_preserves_evaluation
    (transform : X → Answer₁ → Answer₂)
    (oracle : X → Answer₁)
    {program : ExactJetProgram X Answer₂ Output}
    {used : ℕ} {result : Option Output}
    (heval : ExactJetProgram.Evaluates
      (fun x => transform x (oracle x)) program used result) :
    ExactJetProgram.Evaluates oracle (program.mapAnswers transform) used result := by
  induction heval with
  | halt result => exact .halt result
  | query point next used result hnext ih =>
      exact .query point _ used result ih

theorem ExactJetProgram.evaluation_of_mapAnswers
    (transform : X → Answer₁ → Answer₂)
    (oracle : X → Answer₁)
    {program : ExactJetProgram X Answer₂ Output}
    {used : ℕ} {result : Option Output}
    (heval : ExactJetProgram.Evaluates oracle
      (program.mapAnswers transform) used result) :
    ExactJetProgram.Evaluates (fun x => transform x (oracle x))
      program used result := by
  induction program generalizing used result with
  | halt output =>
      simp only [ExactJetProgram.mapAnswers] at heval
      cases heval
      exact .halt output
  | query point next ih =>
      simp only [ExactJetProgram.mapAnswers] at heval
      cases heval with
      | query _ _ childUsed _ hchild =>
          exact .query point _ childUsed result
            (ih (transform point (oracle point)) hchild)

theorem ExactJetProgram.evaluation_of_locallyCapped_success
    (oracle : X → Answer₁) (program : ExactJetProgram X Answer₁ Output)
    (cap used : ℕ) (value : Output)
    (heval : ExactJetProgram.Evaluates oracle
      (program.locallyCapped cap) used (some value)) :
    ExactJetProgram.Evaluates oracle program used (some value) ∧ used ≤ cap := by
  induction cap generalizing program used with
  | zero =>
      cases program with
      | halt result =>
          simp only [ExactJetProgram.locallyCapped] at heval
          cases heval
          exact ⟨.halt _, le_rfl⟩
      | query point next =>
          simp only [ExactJetProgram.locallyCapped] at heval
          cases heval
  | succ cap ih =>
      cases program with
      | halt result =>
          simp only [ExactJetProgram.locallyCapped] at heval
          cases heval
          exact ⟨.halt _, Nat.zero_le _⟩
      | query point next =>
          simp only [ExactJetProgram.locallyCapped] at heval
          cases heval with
          | query _ _ childUsed _ hchild =>
              obtain ⟨horig, hle⟩ := ih (next (oracle point)) childUsed hchild
              exact ⟨.query point next childUsed (some value) horig,
                Nat.succ_le_succ hle⟩

theorem ExactJetProgram.evaluation_bind_success
    (oracle : X → Answer₁) (program : ExactJetProgram X Answer₁ Output)
    {B : Type*} (next : Output → ExactJetProgram X Answer₁ B)
    (used : ℕ) (value : B)
    (heval : ExactJetProgram.Evaluates oracle (program.bind next)
      used (some value)) :
    ∃ middle used₁ used₂,
      ExactJetProgram.Evaluates oracle program used₁ (some middle) ∧
      ExactJetProgram.Evaluates oracle (next middle) used₂ (some value) ∧
      used = used₁ + used₂ := by
  induction program generalizing used with
  | halt result =>
      cases result with
      | none =>
          simp only [ExactJetProgram.bind] at heval
          cases heval
      | some middle =>
          refine ⟨middle, 0, used, .halt _, heval, by omega⟩
  | query point more ih =>
      simp only [ExactJetProgram.bind] at heval
      cases heval with
      | query _ _ childUsed _ hchild =>
          obtain ⟨middle, used₁, used₂, hfirst, hnext, hsum⟩ :=
            ih (oracle point) childUsed hchild
          refine ⟨middle, used₁ + 1, used₂,
            .query point more used₁ (some middle) hfirst, hnext, ?_⟩
          omega

theorem ExactJetProgram.evaluation_halt_eq
    (oracle : X → Answer₁) (result : Option Output)
    (used : ℕ) (output : Option Output)
    (heval : ExactJetProgram.Evaluates oracle (.halt result) used output) :
    used = 0 ∧ result = output := by
  cases heval
  exact ⟨rfl, rfl⟩

end ProgramConversion

section RegularizedCall

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compile a capped strong-solver call for the regularized operator to the
original oracle, preserving the very same shared cap. -/
def compileRegularizedCall (data : VIPublicData E)
    (eta : ℝ) (center : E) (call : CappedExactJetCall data) :
    CappedExactJetCall data where
  cap := call.cap
  program := call.program.mapAnswers
    (fun point base => regularizedJetAnswer data.p eta center point.1 base)

theorem compileRegularizedCall_cap (data : VIPublicData E)
    (eta : ℝ) (center : E) (call : CappedExactJetCall data) :
    (compileRegularizedCall data eta center call).cap = call.cap := rfl

theorem compileRegularizedCall_execute
    (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (eta : ℝ) (center : E) (call : CappedExactJetCall data) :
    (compileRegularizedCall data eta center call).program.runWithFuel
        oracle.answer call.cap =
      call.program.runWithFuel
        (fun point => regularizedJetAnswer data.p eta center point.1
          (oracle.answer point)) call.cap := by
  exact ExactJetProgram.mapAnswers_runWithFuel _ _ _ _

/-- Under the source regularity hypothesis, the raw transformed answer
function is the exact feasible oracle for `G_center`. -/
theorem regularizedFeasibleOracle_answer
    (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : ∀ x ∈ data.X, ContDiffAt ℝ (data.p - 1 : ℕ) F x)
    (eta : ℝ) (center : E) (point : data.X) :
    (regularizedFeasibleOracle data F oracle hF eta center).answer point =
      regularizedJetAnswer data.p eta center point.1 (oracle.answer point) := rfl

theorem regularizedOperator_stronglyMonotone
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta)
    (center : E) :
    StronglyMonotoneOn data (regularizedOperator F eta center) (1 / eta) := by
  intro x hx y hy
  have hmono := hF.monotone_on x hx y hy
  have hdiff :
      regularizedOperator F eta center x - regularizedOperator F eta center y =
        (F x - F y) + (1 / eta) • (x - y) := by
    simp only [regularizedOperator, affineRegularizer]
    module
  rw [hdiff, inner_add_left, inner_smul_left, conj_trivial,
    real_inner_self_eq_norm_sq]
  linarith

theorem regularizedOperator_admissible
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta)
    (center : E) :
    IsAdmissibleOperator data (regularizedOperator F eta center) := by
  constructor
  · obtain ⟨U, hUopen, hXU, hreg⟩ := hF.regularity
    refine ⟨U, hUopen, hXU, ?_⟩
    exact hreg.add ((affineRegularizer_contDiff eta center).contDiffOn.of_le le_top)
  · intro x hx y hy
    have hs := regularizedOperator_stronglyMonotone data F hF eta heta center
      x hx y hy
    exact (mul_nonneg (by positivity) (sq_nonneg ‖x - y‖)).trans
      hs
  · intro x hx y hy
    have hFx := hF.contDiffAt_on data F x hx
    have hFy := hF.contDiffAt_on data F y hy
    have hAx : ContDiffAt ℝ (data.p - 1 : ℕ)
        (affineRegularizer eta center) x :=
      (affineRegularizer_contDiff eta center).contDiffAt.of_le le_top
    have hAy : ContDiffAt ℝ (data.p - 1 : ℕ)
        (affineRegularizer eta center) y :=
      (affineRegularizer_contDiff eta center).contDiffAt.of_le le_top
    rw [show regularizedOperator F eta center = F + affineRegularizer eta center by rfl]
    rw [iteratedFDeriv_add_apply hFx hAx, iteratedFDeriv_add_apply hFy hAy]
    have hp := data.p_ge_two
    have hpos : 0 < data.p - 1 := by omega
    rw [affineRegularizer_iteratedFDeriv_independent eta center
      (data.p - 1) hpos x y]
    simpa only [add_sub_add_right_eq_sub] using
      hF.top_derivative_lipschitz x hx y hy

theorem admissible_continuousOn (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) : ContinuousOn F data.X := by
  intro x hx
  exact (hF.contDiffAt_on data F x hx).continuousAt.continuousWithinAt

theorem admissible_locallyLipschitzOn (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) : LocallyLipschitzOn data.X F := by
  apply ContDiffOn.locallyLipschitzOn data.X_convex
  intro x hx
  have hp := data.p_ge_two
  exact (hF.contDiffAt_on data F x hx).of_le (by
    exact_mod_cast (show 1 ≤ data.p - 1 by omega)) |>.contDiffWithinAt

theorem exists_regularizedVISolution
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta)
    (center : E) :
    ∃ zStar, IsVISolution data (regularizedOperator F eta center) zStar := by
  obtain ⟨zStar, hz⟩ := exists_resolventVI data.X data.X_nonempty data.X_compact
    data.X_convex F (admissible_continuousOn data F hF)
      (admissible_locallyLipschitzOn data F hF) hF.monotone_on eta heta center
  exact ⟨zStar, by simpa [IsVISolution, SolvesModelVI, regularizedOperator,
    resolventOperator, affineRegularizer, one_div] using hz⟩

end RegularizedCall

section FiniteAlgorithm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Replace only the public anchor point.  This is the adapter needed when a
residual solver is invoked from a restart wrapper at an arbitrary feasible
center; every class parameter and the feasible query type stay unchanged. -/
def VIPublicData.withStart (data : VIPublicData E) (center : data.X) :
    VIPublicData E where
  dimension_pos := data.dimension_pos
  p := data.p
  p_ge_two := data.p_ge_two
  Lp := data.Lp
  Lp_pos := data.Lp_pos
  D := data.D
  D_pos := data.D_pos
  X := data.X
  X_nonempty := data.X_nonempty
  X_compact := data.X_compact
  X_convex := data.X_convex
  x0 := center.1
  x0_mem := center.2
  diameter_le := data.diameter_le

def FeasibleExactSymmetricJetOracle.withStart
    (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F) (center : data.X) :
    FeasibleExactSymmetricJetOracle (data.withStart center) F where
  answer point := oracle.answer ⟨point.1, point.2⟩
  exact point j := oracle.exact ⟨point.1, point.2⟩ j

/-- Transport a certificate out of public data whose anchor was replaced.
The feasible set is unchanged, so this copies all three evaluated fields. -/
def EvaluatedNormalCertificate.fromWithStart
    (data : VIPublicData E) (center : data.X)
    (cert : EvaluatedNormalCertificate (data.withStart center)) :
    EvaluatedNormalCertificate data where
  point := ⟨cert.point.1, cert.point.2⟩
  normal := cert.normal
  value := cert.value

/-- Reinterpret a call whose public anchor is `center` as a call for the
original public data.  Queries and jet order are unchanged; successful output
is explicitly transported back to the original certificate type. -/
def CappedExactJetCall.fromWithStart
    (data : VIPublicData E) (center : data.X)
    (call : CappedExactJetCall (data.withStart center)) :
    CappedExactJetCall data where
  cap := call.cap
  program := by
    simpa only [VIPublicData.withStart] using
      call.program.bind (fun cert =>
        .halt (some (cert.fromWithStart data center)))

theorem EvaluatedNormalCertificate.fromWithStart_verified_iff
    (data : VIPublicData E) (center : data.X) (F : E → E) (epsilon : ℝ)
    (cert : EvaluatedNormalCertificate (data.withStart center)) :
    (cert.fromWithStart data center).IsVerifiedFor data F epsilon ↔
      cert.IsVerifiedFor (data.withStart center) F epsilon := by
  rfl

/-- A successful execution of a transported call comes from a successful
execution of the original call, with exactly the same number of queries. -/
theorem CappedExactJetCall.fromWithStart_success
    (data : VIPublicData E) (center : data.X) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (call : CappedExactJetCall (data.withStart center))
    (used : ℕ) (cert : EvaluatedNormalCertificate data)
    (hrun : (call.fromWithStart data center).execute data F oracle =
      .finished used (some cert)) :
    ∃ inner : EvaluatedNormalCertificate (data.withStart center),
      call.execute (data.withStart center) F (oracle.withStart data F center) =
        .finished used (some inner) ∧
      cert = inner.fromWithStart data center := by
  have heval := ExactJetProgram.evaluates_of_runWithFuel_finished hrun
  have heval' : ExactJetProgram.Evaluates
      (oracle.withStart data F center).answer
      (call.program.bind (fun inner =>
        .halt (some (inner.fromWithStart data center)))) used (some cert) := by
    simpa [CappedExactJetCall.execute, CappedExactJetCall.fromWithStart,
      FeasibleExactSymmetricJetOracle.withStart, VIPublicData.withStart] using heval
  obtain ⟨inner, used₁, used₂, hfirst, hlast, hsum⟩ :=
    ExactJetProgram.evaluation_bind_success
      (oracle.withStart data F center).answer call.program
      (fun inner => .halt (some (inner.fromWithStart data center))) used cert heval'
  obtain ⟨rfl, hcert⟩ := ExactJetProgram.evaluation_halt_eq
    (oracle.withStart data F center).answer
    (some (inner.fromWithStart data center)) used₂ (some cert) hlast
  have hused : used = used₁ := by omega
  subst used
  have hle : used₁ ≤ call.cap := by
    have := CappedExactJetCall.finished_queries_le_cap data F oracle
      (call.fromWithStart data center) hrun
    simpa [CappedExactJetCall.fromWithStart] using this
  refine ⟨inner, ?_, Option.some.inj hcert.symm⟩
  simpa [CappedExactJetCall.execute] using hfirst.runWithFuel_eq hle

/-- Conversely, transporting a completed call preserves its successful
execution and exact query count. -/
theorem CappedExactJetCall.fromWithStart_completes
    (data : VIPublicData E) (center : data.X) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (call : CappedExactJetCall (data.withStart center))
    (used : ℕ) (inner : EvaluatedNormalCertificate (data.withStart center))
    (hrun : call.execute (data.withStart center) F
      (oracle.withStart data F center) = .finished used (some inner)) :
    (call.fromWithStart data center).execute data F oracle =
      .finished used (some (inner.fromWithStart data center)) := by
  have hfirst := ExactJetProgram.evaluates_of_runWithFuel_finished hrun
  have hbind := ExactJetProgram.Evaluates.bind
    (next := fun inner => .halt (some (inner.fromWithStart data center)))
    hfirst (ExactJetProgram.Evaluates.halt
      (some (inner.fromWithStart data center)))
  have hle := CappedExactJetCall.finished_queries_le_cap
    (data.withStart center) F (oracle.withStart data F center) call hrun
  have hrun' := hbind.runWithFuel_eq (by simpa using hle)
  simpa [CappedExactJetCall.execute, CappedExactJetCall.fromWithStart,
    FeasibleExactSymmetricJetOracle.withStart, VIPublicData.withStart] using hrun'

theorem IsAdmissibleOperator.withStart
    (data : VIPublicData E) (F : E → E) (hF : IsAdmissibleOperator data F)
    (center : data.X) : IsAdmissibleOperator (data.withStart center) F where
  regularity := hF.regularity
  monotone_on := hF.monotone_on
  top_derivative_lipschitz := hF.top_derivative_lipschitz

/-- A canonical exact projection onto the public compact feasible set.  It is
noncomputable real arithmetic, but uses no information about the unknown
operator. -/
def compactProjection (data : VIPublicData E) (z : E) : data.X :=
  ⟨compactConvexProjection data.X data.X_nonempty data.X_compact data.X_convex z,
    compactConvexProjection_mem data.X data.X_nonempty data.X_compact data.X_convex z⟩

theorem compactProjection_fixed (data : VIPublicData E) (y : data.X) :
    compactProjection data y.1 = y := by
  apply Subtype.ext
  have hvar := compactConvexProjection_variational data.X data.X_nonempty
    data.X_compact data.X_convex y.1 y.1 y.2
  change inner ℝ (y.1 - (compactProjection data y.1).1)
    (y.1 - (compactProjection data y.1).1) ≤ 0 at hvar
  rw [real_inner_self_eq_norm_sq] at hvar
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp
    (le_antisymm hvar (sq_nonneg _))))).symm

theorem compactProjection_distance_to_feasible (data : VIPublicData E)
    (z : E) (y : data.X) :
    ‖(compactProjection data z).1 - y.1‖ ≤ ‖z - y.1‖ := by
  have h := compactConvexProjection_dist_le data.X data.X_nonempty
    data.X_compact data.X_convex z y.1
  rw [show compactConvexProjection data.X data.X_nonempty data.X_compact
      data.X_convex y.1 = y.1 by
    exact congrArg Subtype.val (compactProjection_fixed data y)] at h
  simpa [compactProjection] using h

/-- The ordinary feasible Halpern update after inner iteration `t`. -/
def feasibleHalpernUpdate (data : VIPublicData E) (t : ℕ)
    (y : data.X) : data.X :=
  ⟨(1 / (t + 2 : ℝ)) • data.x0 +
      ((t + 1 : ℝ) / (t + 2 : ℝ)) • y.1, by
    apply data.X_convex data.x0_mem y.2 <;> try positivity
    field_simp
    ring⟩

/-- Recover the original `F` value from a saved `G_center` value, with no
additional query. -/
def recoverBaseCertificate (data : VIPublicData E) (eta : ℝ) (center : E)
    (cert : EvaluatedNormalCertificate data) : EvaluatedNormalCertificate data where
  point := cert.point
  normal := cert.normal
  value := cert.value - affineRegularizer eta center cert.point.1

theorem recoverBaseCertificate_value
    (data : VIPublicData E) (F : E → E) (eta : ℝ) (center : E)
    (cert : EvaluatedNormalCertificate data)
    (hvalue : cert.value = regularizedOperator F eta center cert.point.1) :
    (recoverBaseCertificate data eta center cert).value = F cert.point.1 := by
  simp [recoverBaseCertificate, hvalue, regularizedOperator]

/-- The final kernel check from Algorithm 1.  Failure is explicit and no
query is performed by this check. -/
def checkedRecoveredCertificate (data : VIPublicData E) (eta epsilon : ℝ)
    (center : E) (cert : EvaluatedNormalCertificate data) :
    Option (EvaluatedNormalCertificate data) :=
  let recovered := recoverBaseCertificate data eta center cert
  if ‖recovered.value + recovered.normal‖ ≤ epsilon then some recovered else none

/-- One strong-solver call, locally capped and compiled to the original jet.
The surrounding program may additionally impose one shared outer cap. -/
def compiledStrongProgram (data : VIPublicData E) (S : StrongSolver data)
    (eta delta : ℝ) (center warm : data.X) :
    ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data) :=
  let call := compileRegularizedCall data eta center.1
    (S.solve warm (1 / eta) delta)
  call.program.locallyCapped call.cap

theorem compiledStrongProgram_success_verified
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta) (center warm : data.X)
    (used : ℕ) (cert : EvaluatedNormalCertificate data)
    (heval : ExactJetProgram.Evaluates oracle.answer
      (compiledStrongProgram data S eta delta center warm) used (some cert)) :
    cert.IsVerifiedFor data (regularizedOperator F eta center.1) delta := by
  let baseCall := S.solve warm (1 / eta) delta
  let compiled := compileRegularizedCall data eta center.1 baseCall
  have hlocal : ExactJetProgram.Evaluates oracle.answer
      (compiled.program.locallyCapped compiled.cap) used (some cert) := by
    simpa [compiledStrongProgram, baseCall, compiled] using heval
  obtain ⟨hmapped, hused⟩ :=
    ExactJetProgram.evaluation_of_locallyCapped_success
      oracle.answer compiled.program compiled.cap used cert hlocal
  have hmapped' : ExactJetProgram.Evaluates oracle.answer
      (baseCall.program.mapAnswers
        (fun point base => regularizedJetAnswer data.p eta center.1 point.1 base))
      used (some cert) := by
    simpa [compiled, compileRegularizedCall] using hmapped
  have hraw := ExactJetProgram.evaluation_of_mapAnswers
    (fun point base => regularizedJetAnswer data.p eta center.1 point.1 base)
    oracle.answer hmapped'
  let regOracle := regularizedFeasibleOracle data F oracle
    (fun x hx => hF.contDiffAt_on data F x hx) eta center.1
  have hreg : ExactJetProgram.Evaluates regOracle.answer
      baseCall.program used (some cert) := by
    simpa [compiled, compileRegularizedCall, regOracle,
      regularizedFeasibleOracle] using hraw
  have husedBase : used ≤ baseCall.cap := by
    simpa [compiled, compileRegularizedCall] using hused
  have hrun := hreg.runWithFuel_eq husedBase
  have hexec : baseCall.execute data (regularizedOperator F eta center.1)
      regOracle = .finished used (some cert) := by
    simpa [CappedExactJetCall.execute, baseCall] using hrun
  have hG := regularizedOperator_admissible data F hF eta heta center.1
  exact hS.1 (regularizedOperator F eta center.1) regOracle warm
    (1 / eta) delta used cert hG (by positivity) hdelta hexec

theorem compiledStrongProgram_completes
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta)
    (center warm : data.X) (zStar : E)
    (hz : IsVISolution data (regularizedOperator F eta center.1) zStar) :
    ∃ used cert,
      ExactJetProgram.Evaluates oracle.answer
        (compiledStrongProgram data S eta delta center warm) used (some cert) ∧
      cert.IsVerifiedFor data (regularizedOperator F eta center.1) delta ∧
      (used : ℝ) ≤ strongInterfaceCost data S.leadingConstant gamma b
        ‖warm.1 - zStar‖ (1 / eta) delta := by
  let regOracle := regularizedFeasibleOracle data F oracle
    (fun x hx => hF.contDiffAt_on data F x hx) eta center.1
  have hG := regularizedOperator_admissible data F hF eta heta center.1
  have hstrong := regularizedOperator_stronglyMonotone data F hF eta heta center.1
  obtain ⟨used, cert, hrun, hcert, hcost⟩ := hS.2
    (regularizedOperator F eta center.1) regOracle warm (1 / eta) delta hG
      (by positivity) hdelta hstrong zStar hz
  let baseCall := S.solve warm (1 / eta) delta
  have hevalG : ExactJetProgram.Evaluates regOracle.answer
      baseCall.program used (some cert) := by
    exact ExactJetProgram.evaluates_of_runWithFuel_finished hrun
  have hevalMapped := ExactJetProgram.mapAnswers_preserves_evaluation
    (fun point base => regularizedJetAnswer data.p eta center.1 point.1 base)
    oracle.answer (by
      simpa [regOracle, regularizedFeasibleOracle] using hevalG)
  have hused : used ≤ baseCall.cap := by
    exact CappedExactJetCall.finished_queries_le_cap data
      (regularizedOperator F eta center.1) regOracle baseCall hrun
  have hevalLocal := hevalMapped.locallyCapped hused
  refine ⟨used, cert, ?_, hcert, hcost⟩
  simpa [compiledStrongProgram, baseCall, compileRegularizedCall] using hevalLocal

theorem checkedRecoveredCertificate_verified
    (data : VIPublicData E) (F : E → E) (eta epsilon delta : ℝ)
    (center : E) (inner output : EvaluatedNormalCertificate data)
    (hinner : inner.IsVerifiedFor data
      (regularizedOperator F eta center) delta)
    (hcheck : checkedRecoveredCertificate data eta epsilon center inner =
      some output) :
    output.IsVerifiedFor data F epsilon := by
  let recovered := recoverBaseCertificate data eta center inner
  change (if ‖recovered.value + recovered.normal‖ ≤ epsilon then some recovered else none) =
    some output at hcheck
  split_ifs at hcheck with hnorm
  have hout : recovered = output := Option.some.inj hcheck
  rw [← hout]
  refine ⟨hinner.1, ?_, hnorm⟩
  exact recoverBaseCertificate_value data F eta center inner hinner.2.1

/-- Iterations `t,t+1,...,t+remaining`; the last inner certificate is
converted to an original-operator certificate and kernel checked. -/
def extrapolatedHalpernTail (data : VIPublicData E) (S : StrongSolver data)
    (eta delta epsilon : ℝ) :
    (remaining t : ℕ) → (center previous before : data.X) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data)
  | 0, _, center, previous, before =>
      let warm := compactProjection data
        ((2 : ℝ) • previous.1 - before.1)
      (compiledStrongProgram data S eta delta center warm).bind (fun cert =>
        .halt (checkedRecoveredCertificate data eta epsilon center.1 cert))
  | remaining + 1, t, center, previous, before =>
      let warm := compactProjection data
        ((2 : ℝ) • previous.1 - before.1)
      (compiledStrongProgram data S eta delta center warm).bind (fun cert =>
        extrapolatedHalpernTail data S eta delta epsilon remaining (t + 1)
          (feasibleHalpernUpdate data t cert.point) cert.point previous)

theorem extrapolatedHalpernTail_success_verified
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta epsilon : ℝ) (heta : 0 < eta) (hdelta : 0 < delta)
    (remaining t : ℕ)
    (center previous before : data.X) (used : ℕ)
    (output : EvaluatedNormalCertificate data)
    (heval : ExactJetProgram.Evaluates oracle.answer
      (extrapolatedHalpernTail data S eta delta epsilon remaining t
        center previous before) used (some output)) :
    output.IsVerifiedFor data F epsilon := by
  induction remaining generalizing t center previous before used with
  | zero =>
      simp only [extrapolatedHalpernTail] at heval
      obtain ⟨inner, used₁, used₂, hinnerRun, hcheckRun, _⟩ :=
        ExactJetProgram.evaluation_bind_success oracle.answer
          (compiledStrongProgram data S eta delta center
            (compactProjection data ((2 : ℝ) • previous.1 - before.1)))
          (fun cert => .halt
            (checkedRecoveredCertificate data eta epsilon center.1 cert))
          used output heval
      have hinner := compiledStrongProgram_success_verified data S gamma b hS
        F oracle hF eta delta heta hdelta center
        (compactProjection data ((2 : ℝ) • previous.1 - before.1))
        used₁ inner hinnerRun
      have hcheck := (ExactJetProgram.evaluation_halt_eq oracle.answer
        (checkedRecoveredCertificate data eta epsilon center.1 inner)
        used₂ (some output) hcheckRun).2
      exact checkedRecoveredCertificate_verified data F eta epsilon delta
        center.1 inner output hinner hcheck
  | succ remaining ih =>
      simp only [extrapolatedHalpernTail] at heval
      obtain ⟨inner, _used₁, used₂, _hinnerRun, htail, _⟩ :=
        ExactJetProgram.evaluation_bind_success oracle.answer
          (compiledStrongProgram data S eta delta center
            (compactProjection data ((2 : ℝ) • previous.1 - before.1)))
          (fun cert => extrapolatedHalpernTail data S eta delta epsilon
            remaining (t + 1) (feasibleHalpernUpdate data t cert.point)
              cert.point previous)
          used output heval
      exact ih (t + 1) (feasibleHalpernUpdate data t inner.point)
        inner.point previous used₂ htail

/-- The finite `K+1`-solve ExtrapolatedHalpern syntax tree (`K≥2`). -/
def extrapolatedHalpernProgram (data : VIPublicData E) (S : StrongSolver data)
    (K : ℕ) (eta delta epsilon : ℝ) :
    ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data) :=
  (compiledStrongProgram data S eta delta ⟨data.x0, data.x0_mem⟩
      ⟨data.x0, data.x0_mem⟩).bind (fun cert₀ =>
    (compiledStrongProgram data S eta delta
      (feasibleHalpernUpdate data 0 cert₀.point) cert₀.point).bind (fun cert₁ =>
      extrapolatedHalpernTail data S eta delta epsilon (K - 2) 2
        (feasibleHalpernUpdate data 1 cert₁.point) cert₁.point cert₀.point))

theorem extrapolatedHalpernProgram_success_verified
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (K : ℕ) (eta delta epsilon : ℝ) (heta : 0 < eta)
    (hdelta : 0 < delta) (used : ℕ)
    (output : EvaluatedNormalCertificate data)
    (heval : ExactJetProgram.Evaluates oracle.answer
      (extrapolatedHalpernProgram data S K eta delta epsilon)
      used (some output)) :
    output.IsVerifiedFor data F epsilon := by
  unfold extrapolatedHalpernProgram at heval
  obtain ⟨cert₀, _used₀, usedRest, _hfirst, hrest, _⟩ :=
    ExactJetProgram.evaluation_bind_success oracle.answer
      (compiledStrongProgram data S eta delta
        ⟨data.x0, data.x0_mem⟩ ⟨data.x0, data.x0_mem⟩)
      (fun cert₀ =>
        (compiledStrongProgram data S eta delta
          (feasibleHalpernUpdate data 0 cert₀.point) cert₀.point).bind
            (fun cert₁ => extrapolatedHalpernTail data S eta delta epsilon
              (K - 2) 2 (feasibleHalpernUpdate data 1 cert₁.point)
                cert₁.point cert₀.point))
      used output heval
  obtain ⟨cert₁, _used₁, usedTail, _hsecond, htail, _⟩ :=
    ExactJetProgram.evaluation_bind_success oracle.answer
      (compiledStrongProgram data S eta delta
        (feasibleHalpernUpdate data 0 cert₀.point) cert₀.point)
      (fun cert₁ => extrapolatedHalpernTail data S eta delta epsilon
        (K - 2) 2 (feasibleHalpernUpdate data 1 cert₁.point)
          cert₁.point cert₀.point)
      usedRest output hrest
  exact extrapolatedHalpernTail_success_verified data S gamma b hS F oracle hF
    eta delta epsilon heta hdelta (K - 2) 2
    (feasibleHalpernUpdate data 1 cert₁.point) cert₁.point cert₀.point
    usedTail output htail

/-- `U_a(K)` in the explicit source cap, as a finite computable sum. -/
def boostUa (a : ℝ) (K : ℕ) : ℝ :=
  2 * Real.rpow 3 a + Real.rpow 16 a *
    ∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
      Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
        Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2))

/-- The public cap from Equation (explicit-cap), rounded up with one unit of
slack. -/
def boostSharedCap (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b K : ℕ) (R eta e : ℝ) : ℕ :=
  Nat.ceil (S.leadingConstant * (strongLog data (1 / eta) (e / eta)) ^ b *
    (K + 1 + Real.rpow (eta * data.Lp) gamma *
      Real.rpow R ((data.p - 1 : ℕ) * gamma) *
        boostUa ((data.p - 1 : ℕ) * gamma) K)) + 1

/-- Complete finite call with one interruptible cap shared by every nested
strong-solver query. -/
def extrapolatedHalpernCall (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b K : ℕ) (R epsilon e eta : ℝ) :
    CappedExactJetCall data where
  cap := boostSharedCap data S gamma b K R eta e
  program := extrapolatedHalpernProgram data S K eta (e / eta) epsilon

/-- Source parameter `alpha = gamma/(1+gamma)`. -/
def boostAlpha (gamma : ℝ) : ℝ := gamma / (1 + gamma)

/-- Source horizon `max {2, ceil(Q_R^alpha)}`. -/
def boostHorizon (data : VIPublicData E) (gamma R epsilon : ℝ) : ℕ :=
  max 2 (Nat.ceil (Real.rpow (residualCondition data R epsilon)
    (boostAlpha gamma)))

def boostOuterError (R : ℝ) (K : ℕ) : ℝ := R / (K + 2 : ℝ) ^ 4

def boostStepsize (R epsilon : ℝ) (K : ℕ) : ℝ :=
  8 * R * (1 + harmonicR (K + 1)) / (epsilon * (K + 1 : ℝ))

/-- The fully specialized source call; no horizon, tolerance, or stepsize is
supplied by the unknown operator. -/
def boostedResidualCall (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (R epsilon : ℝ) : CappedExactJetCall data :=
  let K := boostHorizon data gamma R epsilon
  let e := boostOuterError R K
  let eta := boostStepsize R epsilon K
  extrapolatedHalpernCall data S gamma b K R epsilon e eta

theorem boostHorizon_ge_two (data : VIPublicData E) (gamma R epsilon : ℝ) :
    2 ≤ boostHorizon data gamma R epsilon := by
  simp [boostHorizon]

theorem boostOuterError_pos {R : ℝ} (hR : 0 < R) (K : ℕ) :
    0 < boostOuterError R K := by
  simp [boostOuterError]
  positivity

theorem boostStepsize_pos {R epsilon : ℝ} (hR : 0 < R)
    (hepsilon : 0 < epsilon) (K : ℕ) :
    0 < boostStepsize R epsilon K := by
  rw [boostStepsize]
  have hH : 0 < 1 + harmonicR (K + 1) := by
    linarith [harmonicR_nonneg (K + 1)]
  positivity

theorem extrapolatedHalpernCall_cap (data : VIPublicData E)
    (S : StrongSolver data) (gamma : ℝ) (b K : ℕ)
    (R epsilon e eta : ℝ) :
    (extrapolatedHalpernCall data S gamma b K R epsilon e eta).cap =
      boostSharedCap data S gamma b K R eta e := rfl

theorem extrapolatedHalpernCall_noFalseSuccess
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (K : ℕ) (R epsilon e eta : ℝ) (heta : 0 < eta) (he : 0 < e) (used : ℕ)
    (output : EvaluatedNormalCertificate data)
    (hrun : CappedExactJetCall.execute data F oracle
      (extrapolatedHalpernCall data S gamma b K R epsilon e eta) =
        CappedRunResult.finished used (some output)) :
    output.IsVerifiedFor data F epsilon ∧
      used ≤ boostSharedCap data S gamma b K R eta e := by
  have heval := ExactJetProgram.evaluates_of_runWithFuel_finished hrun
  refine ⟨extrapolatedHalpernProgram_success_verified data S gamma b hS
    F oracle hF K eta (e / eta) epsilon heta (div_pos he heta) used output heval, ?_⟩
  exact CappedExactJetCall.finished_queries_le_cap data F oracle
    (extrapolatedHalpernCall data S gamma b K R epsilon e eta) hrun

/-- Audit-facing operational content of `thm:boost`: the public finite call
uses the source cap, every regularized jet is obtained by one original jet,
and any reported success is a genuinely evaluated, kernel-verified original
certificate.  The separate analytic cost/noninterruption implication is not
folded into this executable contract. -/
def BoostExecutionClaim : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ), S.SatisfiesInterface data gamma b →
    ∀ (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F),
      IsAdmissibleOperator data F →
      ∀ (K : ℕ) (R epsilon e eta : ℝ), 0 < eta → 0 < e → ∀ (used : ℕ)
        (output : EvaluatedNormalCertificate data),
        CappedExactJetCall.execute data F oracle
            (extrapolatedHalpernCall data S gamma b K R epsilon e eta) =
              CappedRunResult.finished used (some output) →
        output.IsVerifiedFor data F epsilon ∧
          used ≤ boostSharedCap data S gamma b K R eta e

theorem boostExecutionClaim_proof : BoostExecutionClaim := by
  intro E _ _ _ data S gamma b hS F oracle hF K R epsilon e eta heta he used output hrun
  exact extrapolatedHalpernCall_noFalseSuccess data S gamma b hS F oracle hF
    K R epsilon e eta heta he used output hrun

section AnalyticTrace

/-- A trace ties every analytic iterate to an actual evaluation of the
compiled strong-solver program.  No success or cost theorem is stored in the
trace: both are derived from `S.SatisfiesInterface`. -/
structure ExtrapolatedHalpernTrace
    (data : VIPublicData E) (S : StrongSolver data)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (eta delta : ℝ) (K : ℕ) where
  x : ℕ → data.X
  yHat : ℕ → data.X
  warm : ℕ → data.X
  cert : ℕ → EvaluatedNormalCertificate data
  used : ℕ → ℕ
  x_zero : x 0 = ⟨data.x0, data.x0_mem⟩
  warm_zero : warm 0 = ⟨data.x0, data.x0_mem⟩
  warm_one : warm 1 = yHat 0
  warm_later : ∀ t, 2 ≤ t → t ≤ K →
    warm t = compactProjection data
      ((2 : ℝ) • (yHat (t - 1)).1 - (yHat (t - 2)).1)
  call_evaluates : ∀ t, t ≤ K →
    ExactJetProgram.Evaluates oracle.answer
      (compiledStrongProgram data S eta delta (x t) (warm t))
      (used t) (some (cert t))
  point_eq : ∀ t, t ≤ K → (cert t).point = yHat t
  update : ∀ t, t < K → x (t + 1) =
    feasibleHalpernUpdate data t (yHat t)

def analysisResolvent (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta) : E → E :=
  fun center => resolventPoint data.X data.X_nonempty data.X_compact data.X_convex
    F (admissible_continuousOn data F hF)
      (admissible_locallyLipschitzOn data F hF) hF.monotone_on eta heta center

theorem analysisResolvent_mem
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta)
    (center : E) : analysisResolvent data F hF eta heta center ∈ data.X := by
  exact (resolventPoint_spec data.X data.X_nonempty data.X_compact data.X_convex
    F (admissible_continuousOn data F hF)
      (admissible_locallyLipschitzOn data F hF) hF.monotone_on eta heta center).1

theorem analysisResolvent_solves
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta)
    (center : E) :
    IsVISolution data (regularizedOperator F eta center)
      (analysisResolvent data F hF eta heta center) := by
  simpa [IsVISolution, SolvesModelVI, regularizedOperator,
    resolventOperator, affineRegularizer, analysisResolvent, one_div] using
    (resolventPoint_spec data.X data.X_nonempty data.X_compact data.X_convex
      F (admissible_continuousOn data F hF)
        (admissible_locallyLipschitzOn data F hF) hF.monotone_on
          eta heta center)

theorem analysisResolvent_firmlyNonexpansive
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta) :
    FirmlyNonexpansive (analysisResolvent data F hF eta heta) := by
  intro a b
  have hinner := resolventPoint_firmly_nonexpansive data.X data.X_nonempty data.X_compact
    data.X_convex F (admissible_continuousOn data F hF)
      (admissible_locallyLipschitzOn data F hF) hF.monotone_on eta heta a b
  let d := analysisResolvent data F hF eta heta a -
    analysisResolvent data F hF eta heta b
  let e := a - b
  rw [show (a - analysisResolvent data F hF eta heta a) -
      (b - analysisResolvent data F hF eta heta b) = e - d by
    dsimp [d, e]
    abel]
  change ‖d‖ ^ 2 + ‖e - d‖ ^ 2 ≤ ‖e‖ ^ 2
  have hnorm : ‖e - d‖ ^ 2 = ‖e‖ ^ 2 - 2 * inner ℝ e d + ‖d‖ ^ 2 := by
    exact norm_sub_sq_real e d
  rw [hnorm]
  change ‖d‖ ^ 2 ≤ inner ℝ e d at hinner
  nlinarith

theorem ExtrapolatedHalpernTrace.isProjectedPredictor
    (data : VIPublicData E) (S : StrongSolver data)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta)
    (delta : ℝ) (K : ℕ)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K) :
    IsProjectedLinearPredictor (analysisResolvent data F hF eta heta) data.x0
      (fun t => (trace.x t).1) (fun t => (trace.yHat t).1)
      (fun t => (trace.warm t).1) K := by
  refine ⟨congrArg Subtype.val trace.warm_zero,
    congrArg Subtype.val trace.warm_one, ?_⟩
  intro t ht hK
  change ‖(trace.warm t).1 - analysisResolvent data F hF eta heta (trace.x t).1‖ ≤ _
  rw [congrArg Subtype.val (trace.warm_later t ht hK)]
  exact compactProjection_distance_to_feasible data
    ((2 : ℝ) • (trace.yHat (t - 1)).1 - (trace.yHat (t - 2)).1)
    ⟨analysisResolvent data F hF eta heta (trace.x t).1,
      analysisResolvent_mem data F hF eta heta _⟩

/-- The proof obligations attached to one selected strong-solver result. -/
def CompletedStrongPairValid
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta)
    (center warm : data.X) (pair : ℕ × EvaluatedNormalCertificate data) : Prop :=
  ExactJetProgram.Evaluates oracle.answer
      (compiledStrongProgram data S eta delta center warm)
      pair.1 (some pair.2) ∧
    pair.2.IsVerifiedFor data (regularizedOperator F eta center.1) delta ∧
    (pair.1 : ℝ) ≤ strongInterfaceCost data S.leadingConstant gamma b
      ‖warm.1 - analysisResolvent data F hF eta heta center.1‖
      (1 / eta) delta

/-- The successful evaluated result selected from the strong-interface
completion theorem.  This choice is used only to prove existence of an
execution trace; it is not exposed to the executable program. -/
noncomputable def completedStrongPair
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta)
    (center warm : data.X) : ℕ × EvaluatedNormalCertificate data :=
  Classical.choose (show ∃ pair,
      CompletedStrongPairValid data S gamma b F oracle hF eta delta heta
        center warm pair from by
    obtain ⟨used, cert, heval, hverified, hcost⟩ :=
      compiledStrongProgram_completes data S gamma b hS F oracle hF
        eta delta heta hdelta center warm
          (analysisResolvent data F hF eta heta center.1)
          (analysisResolvent_solves data F hF eta heta center.1)
    exact ⟨(used, cert), heval, hverified, hcost⟩)

theorem completedStrongPair_spec
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta)
    (center warm : data.X) :
    ExactJetProgram.Evaluates oracle.answer
        (compiledStrongProgram data S eta delta center warm)
        (completedStrongPair data S gamma b hS F oracle hF eta delta heta hdelta
          center warm).1
        (some (completedStrongPair data S gamma b hS F oracle hF eta delta heta hdelta
          center warm).2) ∧
      (completedStrongPair data S gamma b hS F oracle hF eta delta heta hdelta
          center warm).2.IsVerifiedFor data
        (regularizedOperator F eta center.1) delta ∧
      ((completedStrongPair data S gamma b hS F oracle hF eta delta heta hdelta
          center warm).1 : ℝ) ≤
        strongInterfaceCost data S.leadingConstant gamma b
          ‖warm.1 - analysisResolvent data F hF eta heta center.1‖
          (1 / eta) delta := by
  exact Classical.choose_spec (show ∃ pair,
      CompletedStrongPairValid data S gamma b F oracle hF eta delta heta
        center warm pair from by
    obtain ⟨used, cert, heval, hverified, hcost⟩ :=
      compiledStrongProgram_completes data S gamma b hS F oracle hF
        eta delta heta hdelta center warm
          (analysisResolvent data F hF eta heta center.1)
          (analysisResolvent_solves data F hF eta heta center.1)
    exact ⟨(used, cert), heval, hverified, hcost⟩)

structure ExtrapolatedHalpernState (data : VIPublicData E) where
  center : data.X
  previous : data.X
  before : data.X

def traceWarm (data : VIPublicData E) (t : ℕ)
    (state : ExtrapolatedHalpernState data) : data.X :=
  match t with
  | 0 => ⟨data.x0, data.x0_mem⟩
  | 1 => state.previous
  | _ + 2 => compactProjection data
      ((2 : ℝ) • state.previous.1 - state.before.1)

noncomputable def canonicalTraceState
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta) :
    ℕ → ExtrapolatedHalpernState data
  | 0 => ⟨⟨data.x0, data.x0_mem⟩, ⟨data.x0, data.x0_mem⟩,
      ⟨data.x0, data.x0_mem⟩⟩
  | t + 1 =>
      let state := canonicalTraceState data S gamma b hS F oracle hF
        eta delta heta hdelta t
      let pair := completedStrongPair data S gamma b hS F oracle hF
        eta delta heta hdelta state.center (traceWarm data t state)
      ⟨feasibleHalpernUpdate data t pair.2.point, pair.2.point, state.previous⟩

noncomputable def canonicalTracePair
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta) (t : ℕ) :=
  let state := canonicalTraceState data S gamma b hS F oracle hF
    eta delta heta hdelta t
  completedStrongPair data S gamma b hS F oracle hF eta delta heta hdelta
    state.center (traceWarm data t state)

noncomputable def canonicalExtrapolatedHalpernTrace
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta) (K : ℕ) :
    ExtrapolatedHalpernTrace data S F oracle eta delta K where
  x t := (canonicalTraceState data S gamma b hS F oracle hF
    eta delta heta hdelta t).center
  yHat t := (canonicalTracePair data S gamma b hS F oracle hF
    eta delta heta hdelta t).2.point
  warm t := traceWarm data t (canonicalTraceState data S gamma b hS F oracle hF
    eta delta heta hdelta t)
  cert t := (canonicalTracePair data S gamma b hS F oracle hF
    eta delta heta hdelta t).2
  used t := (canonicalTracePair data S gamma b hS F oracle hF
    eta delta heta hdelta t).1
  x_zero := rfl
  warm_zero := rfl
  warm_one := by rfl
  warm_later t ht hK := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le ht
    simp [traceWarm, canonicalTraceState, canonicalTracePair, Nat.add_comm]
  call_evaluates t ht := by
    exact (completedStrongPair_spec data S gamma b hS F oracle hF eta delta
      heta hdelta
      (canonicalTraceState data S gamma b hS F oracle hF eta delta heta hdelta t).center
      (traceWarm data t (canonicalTraceState data S gamma b hS F oracle hF
        eta delta heta hdelta t))).1
  point_eq t ht := rfl
  update t ht := by
    simp [canonicalTraceState, canonicalTracePair]

theorem ExtrapolatedHalpernTrace.call_verified
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta) (K : ℕ)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K)
    (t : ℕ) (ht : t ≤ K) :
    (trace.cert t).IsVerifiedFor data
      (regularizedOperator F eta (trace.x t).1) delta := by
  exact compiledStrongProgram_success_verified data S gamma b hS F oracle hF
    eta delta heta hdelta (trace.x t) (trace.warm t) (trace.used t) (trace.cert t)
      (trace.call_evaluates t ht)

theorem ExtrapolatedHalpernTrace.call_cost
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta) (K : ℕ)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K)
    (hcanonical : trace = canonicalExtrapolatedHalpernTrace data S gamma b hS
      F oracle hF eta delta heta hdelta K)
    (t : ℕ) :
    (trace.used t : ℝ) ≤
      strongInterfaceCost data S.leadingConstant gamma b
        ‖(trace.warm t).1 - analysisResolvent data F hF eta heta (trace.x t).1‖
        (1 / eta) delta := by
  subst trace
  exact (completedStrongPair_spec data S gamma b hS F oracle hF eta delta
    heta hdelta
    (canonicalTraceState data S gamma b hS F oracle hF eta delta heta hdelta t).center
    (traceWarm data t (canonicalTraceState data S gamma b hS F oracle hF
      eta delta heta hdelta t))).2.2

theorem ExtrapolatedHalpernTrace.isInexactOrbit
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta e : ℝ) (heta : 0 < eta) (hdelta : 0 < delta)
    (hscale : eta * delta ≤ e) (K : ℕ)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K) :
    IsInexactHalpernOrbit (analysisResolvent data F hF eta heta) data.x0 e K
      (fun t => (trace.x t).1) (fun t => (trace.yHat t).1) := by
  refine ⟨congrArg Subtype.val trace.x_zero, ?_, ?_⟩
  · intro t ht
    have hver := ExtrapolatedHalpernTrace.call_verified data S gamma b hS F oracle
      hF eta delta heta hdelta K trace t ht
    have hpoint := trace.point_eq t ht
    have hcert : ‖F (trace.yHat t).1 + (trace.cert t).normal +
        eta⁻¹ • ((trace.yHat t).1 - (trace.x t).1)‖ ≤ delta := by
      have hv := hver.2.1
      have hn := hver.2.2
      rw [hpoint] at hv
      rw [hv] at hn
      simpa [regularizedOperator, affineRegularizer, one_div, add_assoc,
        add_left_comm, add_comm] using hn
    have hprox := approximateProximal_core data F
      (admissible_continuousOn data F hF)
      (admissible_locallyLipschitzOn data F hF) hF.monotone_on
      (trace.x t).1 (trace.yHat t).1 (trace.x t).2 (trace.yHat t).2
      (trace.cert t).normal (by simpa [hpoint] using hver.1)
      eta delta heta hdelta.le hcert
    exact hprox.1.trans hscale
  · intro t ht
    exact congrArg Subtype.val (trace.update t ht)

/-- Canonical exact Halpern orbit used solely as the analytic shadow. -/
noncomputable def exactHalpernX (P : E → E) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => (1 / (t + 2 : ℝ)) • x0 +
      ((t + 1 : ℝ) / (t + 2 : ℝ)) • P (exactHalpernX P x0 t)

noncomputable def exactHalpernY (P : E → E) (x0 : E) (t : ℕ) : E :=
  P (exactHalpernX P x0 t)

theorem exactHalpernOrbit (P : E → E) (x0 : E) :
    IsHalpernOrbit P x0 (exactHalpernX P x0) (exactHalpernY P x0) := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro t
  rw [exactHalpernX]
  rfl

theorem ExtrapolatedHalpernTrace.warmEnergy
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (R e eta : ℝ) (hR : 0 < R) (heta : 0 < eta) (K : ℕ) (hK : 2 ≤ K)
    (he : e = R / (K + 2 : ℝ) ^ 4)
    (zStar : E) (hzStar : IsVISolution data F zStar)
    (hdistance : ‖data.x0 - zStar‖ ≤ R)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta (e / eta) K) :
    (‖(trace.warm 0).1 -
        analysisResolvent data F hF eta heta (trace.x 0).1‖ ≤ 3 * R ∧
      ‖(trace.warm 1).1 -
        analysisResolvent data F hF eta heta (trace.x 1).1‖ ≤ 3 * R) ∧
    (∀ k ell, 2 ≤ k → k ≤ ell → ell ≤ 2 * k - 1 → ell ≤ K →
      (∑ t ∈ Finset.Icc k ell,
          ‖(trace.warm t).1 -
            analysisResolvent data F hF eta heta (trace.x t).1‖ ^ 2) ≤
        256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2) := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hdistance
  have he0 : 0 < e := by rw [he]; positivity
  have hdelta : 0 < e / eta := div_pos he0 heta
  have hscale : eta * (e / eta) ≤ e := by
    field_simp [heta.ne']
    norm_num
  let P := analysisResolvent data F hF eta heta
  have hactual := ExtrapolatedHalpernTrace.isInexactOrbit data S gamma b hS F oracle
    hF eta (e / eta) e heta hdelta hscale K trace
  have hfirm := analysisResolvent_firmlyNonexpansive data F hF eta heta
  have hfix : P zStar = zStar := by
    exact (solvesModelVI_iff_resolventPoint_fixed data.X data.X_nonempty
      data.X_compact data.X_convex F (admissible_continuousOn data F hF)
      (admissible_locallyLipschitzOn data F hF) hF.monotone_on eta heta zStar).mp
        hzStar
  have hpredict := trace.isProjectedPredictor data S F oracle hF eta heta
  have hwarm := warmEnergyClaim_proof P zStar data.x0 R e K
    (fun t => (trace.x t).1) (fun t => (trace.yHat t).1)
    (fun t => (trace.warm t).1) (exactHalpernX P data.x0)
    (exactHalpernY P data.x0) hfirm hfix hdistance (by omega) hactual
      (exactHalpernOrbit P data.x0) hpredict he
  exact ⟨hwarm.1, hwarm.2.2⟩

theorem ExtrapolatedHalpernTrace.final_check_succeeds
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (R epsilon e eta : ℝ) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (K : ℕ) (hK : 2 ≤ K)
    (he : e = R / (K + 2 : ℝ) ^ 4)
    (hetadef : eta = 8 * R * (1 + harmonicR (K + 1)) /
      (epsilon * (K + 1 : ℝ)))
    (zStar : E) (hzStar : IsVISolution data F zStar)
    (hdistance : ‖data.x0 - zStar‖ ≤ R)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta (e / eta) K) :
    checkedRecoveredCertificate data eta epsilon (trace.x K).1 (trace.cert K) =
      some (recoverBaseCertificate data eta (trace.x K).1 (trace.cert K)) := by
  have hepos : 0 < e := by rw [he]; positivity
  have hdelta : 0 < e / eta := div_pos hepos heta
  have hscale : eta * (e / eta) ≤ e := by
    field_simp [heta.ne']
    norm_num
  have hactual := ExtrapolatedHalpernTrace.isInexactOrbit data S gamma b hS F oracle
    hF eta (e / eta) e heta hdelta hscale K trace
  have hfirm := analysisResolvent_firmlyNonexpansive data F hF eta heta
  have hfix : analysisResolvent data F hF eta heta zStar = zStar := by
    exact (solvesModelVI_iff_resolventPoint_fixed data.X data.X_nonempty
      data.X_compact data.X_convex F (admissible_continuousOn data F hF)
      (admissible_locallyLipschitzOn data F hF) hF.monotone_on eta heta zStar).mp
        hzStar
  have hver := ExtrapolatedHalpernTrace.call_verified data S gamma b hS F oracle
    hF eta (e / eta) heta hdelta K trace K le_rfl
  have hpoint := trace.point_eq K le_rfl
  let P := analysisResolvent data F hF eta heta
  let v := (trace.cert K).value + (trace.cert K).normal
  have hvnorm : ‖v‖ ≤ e / eta := hver.2.2
  have hvEq : F (trace.yHat K).1 + (trace.cert K).normal =
      v - (1 / eta) • ((trace.yHat K).1 - (trace.x K).1) := by
    have hvalue := hver.2.1
    rw [hpoint] at hvalue
    dsimp [v]
    rw [hvalue]
    simp only [regularizedOperator, affineRegularizer]
    module
  have hfinal := finalCertificateClaim_proof data.X F P zStar data.x0
    (trace.cert K).normal v R epsilon e eta K
    (fun t => (trace.x t).1) (fun t => (trace.yHat t).1)
    (exactHalpernX P data.x0) (exactHalpernY P data.x0)
    hfirm hfix hdistance hR hepsilon hK hactual
    (exactHalpernOrbit P data.x0)
    (by simpa [hpoint] using hver.1) hvEq hvnorm he hetadef
  unfold checkedRecoveredCertificate
  rw [if_pos]
  have hrecover := recoverBaseCertificate_value data F eta (trace.x K).1
    (trace.cert K) (by simpa [hpoint] using hver.2.1)
  rw [hrecover, hpoint]
  exact hfinal.2

theorem ExtrapolatedHalpernTrace.final_recovered_verified
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (R epsilon e eta : ℝ) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (K : ℕ) (hK : 2 ≤ K)
    (he : e = R / (K + 2 : ℝ) ^ 4)
    (hetadef : eta = 8 * R * (1 + harmonicR (K + 1)) /
      (epsilon * (K + 1 : ℝ)))
    (zStar : E) (hzStar : IsVISolution data F zStar)
    (hdistance : ‖data.x0 - zStar‖ ≤ R)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta (e / eta) K) :
    (recoverBaseCertificate data eta (trace.x K).1 (trace.cert K)).IsVerifiedFor
      data F epsilon := by
  have hcheck := trace.final_check_succeeds data S gamma b hS F oracle hF
    R epsilon e eta hR hepsilon heta K hK he hetadef zStar hzStar hdistance
  have hver := ExtrapolatedHalpernTrace.call_verified data S gamma b hS F oracle
    hF eta (e / eta) heta (by
      rw [he]
      exact div_pos (by positivity) heta) K trace K le_rfl
  exact checkedRecoveredCertificate_verified data F eta epsilon (e / eta)
    (trace.x K).1 (trace.cert K)
    (recoverBaseCertificate data eta (trace.x K).1 (trace.cert K)) hver hcheck

def traceTailUsed
    {data : VIPublicData E} {S : StrongSolver data}
    {F : E → E} {oracle : FeasibleExactSymmetricJetOracle data F}
    {eta delta : ℝ} {K : ℕ}
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K) :
    ℕ → ℕ → ℕ
  | t, 0 => trace.used t
  | t, remaining + 1 => trace.used t + traceTailUsed trace (t + 1) remaining

def traceTailPower
    {data : VIPublicData E} {S : StrongSolver data}
    {F : E → E} {oracle : FeasibleExactSymmetricJetOracle data F}
    {eta delta : ℝ} {K : ℕ}
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K)
    (P : E → E) (a : ℝ) : ℕ → ℕ → ℝ
  | t, 0 => Real.rpow ‖(trace.warm t).1 - P (trace.x t).1‖ a
  | t, remaining + 1 =>
      Real.rpow ‖(trace.warm t).1 - P (trace.x t).1‖ a +
        traceTailPower trace P a (t + 1) remaining

theorem harmonicR_le_one_add_log (n : ℕ) (hn : 1 ≤ n) :
    harmonicR n ≤ 1 + Real.log n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num [harmonicR]
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have hspos : 0 < (n + 1 : ℝ) := by positivity
        have hratio : 0 < (n : ℝ) / (n + 1 : ℝ) := div_pos hnpos hspos
        have hlog := Real.log_le_sub_one_of_pos hratio
        rw [Real.log_div hnpos.ne' hspos.ne'] at hlog
        have hstep : 1 / (n + 1 : ℝ) ≤
            Real.log (n + 1 : ℝ) - Real.log (n : ℝ) := by
          have hnreal : (n : ℝ) ≠ 0 := hnpos.ne'
          have hsreal : (n + 1 : ℝ) ≠ 0 := hspos.ne'
          field_simp [hnreal, hsreal] at hlog ⊢
          nlinarith
        rw [harmonicR]
        have hi := ih (by omega)
        norm_num at hi ⊢
        rw [one_div] at hstep
        linarith

theorem traceTailPower_eq_sum_Icc
    {data : VIPublicData E} {S : StrongSolver data}
    {F : E → E} {oracle : FeasibleExactSymmetricJetOracle data F}
    {eta delta : ℝ} {K : ℕ}
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K)
    (P : E → E) (a : ℝ) (t remaining : ℕ) :
    traceTailPower trace P a t remaining =
      ∑ i ∈ Finset.Icc t (t + remaining),
        Real.rpow ‖(trace.warm i).1 - P (trace.x i).1‖ a := by
  induction remaining generalizing t with
  | zero => simp [traceTailPower]
  | succ remaining ih =>
      rw [traceTailPower, ih]
      have hset : Finset.Icc t (t + (remaining + 1)) =
          insert t (Finset.Icc (t + 1) ((t + 1) + remaining)) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.sum_insert]
      simp

theorem regularized_strong_cost_rewrite
    (data : VIPublicData E) (C gamma : ℝ) (b : ℕ)
    (r eta delta : ℝ) (hr : 0 ≤ r) (heta : 0 < eta) :
    strongInterfaceCost data C gamma b r (1 / eta) delta =
      C * (strongLog data (1 / eta) delta) ^ b *
        (1 + Real.rpow (eta * data.Lp) gamma *
          Real.rpow r ((data.p - 1 : ℕ) * gamma)) := by
  have hLp : 0 ≤ data.Lp := data.Lp_pos.le
  have heta0 : 0 ≤ eta := heta.le
  have hpow : 0 ≤ r ^ (data.p - 1) := by positivity
  have hbase : data.Lp * r ^ (data.p - 1) / (1 / eta) =
      (eta * data.Lp) * r ^ (data.p - 1) := by
    field_simp [heta.ne']
  have hrnat : r ^ (data.p - 1) =
      Real.rpow r ((data.p - 1 : ℕ) : ℝ) := by
    exact (Real.rpow_natCast r (data.p - 1)).symm
  rw [strongInterfaceCost, hbase, Real.mul_rpow (mul_nonneg heta0 hLp) hpow,
    hrnat]
  change C * (1 + Real.rpow (eta * data.Lp) gamma *
      Real.rpow (Real.rpow r ((data.p - 1 : ℕ) : ℝ)) gamma) *
      strongLog data (1 / eta) delta ^ b = _
  have hrmul : Real.rpow (Real.rpow r ((data.p - 1 : ℕ) : ℝ)) gamma =
      Real.rpow r (((data.p - 1 : ℕ) : ℝ) * gamma) :=
    (Real.rpow_mul hr ((data.p - 1 : ℕ) : ℝ) gamma).symm
  rw [hrmul]
  ring

theorem canonical_trace_tail_cost
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 < delta) (K : ℕ)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K)
    (hcanonical : trace = canonicalExtrapolatedHalpernTrace data S gamma b hS
      F oracle hF eta delta heta hdelta K)
    (t remaining : ℕ) :
    (traceTailUsed trace t remaining : ℝ) ≤
      S.leadingConstant * (strongLog data (1 / eta) delta) ^ b *
        ((remaining + 1 : ℕ) +
          Real.rpow (eta * data.Lp) gamma *
            traceTailPower trace (analysisResolvent data F hF eta heta)
              ((data.p - 1 : ℕ) * gamma) t remaining) := by
  induction remaining generalizing t with
  | zero =>
      simp only [traceTailUsed, traceTailPower]
      have hcall := ExtrapolatedHalpernTrace.call_cost data S gamma b hS F oracle
        hF eta delta heta hdelta K trace hcanonical t
      rw [regularized_strong_cost_rewrite data S.leadingConstant gamma b
        ‖(trace.warm t).1 - analysisResolvent data F hF eta heta (trace.x t).1‖
        eta delta (norm_nonneg _) heta] at hcall
      convert hcall using 1 <;> norm_num
  | succ remaining ih =>
      simp only [traceTailUsed, traceTailPower, Nat.cast_add, Nat.cast_one]
      have hcall := ExtrapolatedHalpernTrace.call_cost data S gamma b hS F oracle
        hF eta delta heta hdelta K trace hcanonical t
      rw [regularized_strong_cost_rewrite data S.leadingConstant gamma b
        ‖(trace.warm t).1 - analysisResolvent data F hF eta heta (trace.x t).1‖
        eta delta (norm_nonneg _) heta] at hcall
      have htail := ih (t + 1)
      calc
        (trace.used t : ℝ) + (traceTailUsed trace (t + 1) remaining : ℝ) ≤
            S.leadingConstant * (strongLog data (1 / eta) delta) ^ b *
              (1 + Real.rpow (eta * data.Lp) gamma *
                Real.rpow ‖(trace.warm t).1 -
                  analysisResolvent data F hF eta heta (trace.x t).1‖
                    ((data.p - 1 : ℕ) * gamma)) +
            S.leadingConstant * (strongLog data (1 / eta) delta) ^ b *
              ((remaining + 1 : ℕ) + Real.rpow (eta * data.Lp) gamma *
                traceTailPower trace (analysisResolvent data F hF eta heta)
                  ((data.p - 1 : ℕ) * gamma) (t + 1) remaining) :=
          add_le_add hcall htail
        _ = S.leadingConstant * (strongLog data (1 / eta) delta) ^ b *
              ((↑remaining + 1 + 1 : ℝ) + Real.rpow (eta * data.Lp) gamma *
                (Real.rpow ‖(trace.warm t).1 -
                    analysisResolvent data F hF eta heta (trace.x t).1‖
                      ((data.p - 1 : ℕ) * gamma) +
                  traceTailPower trace (analysisResolvent data F hF eta heta)
                    ((data.p - 1 : ℕ) * gamma) (t + 1) remaining)) := by
          push_cast
          ring

theorem traceTailUsed_zero_eq_programUsed
    {data : VIPublicData E} {S : StrongSolver data}
    {F : E → E} {oracle : FeasibleExactSymmetricJetOracle data F}
    {eta delta : ℝ} {K : ℕ}
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K)
    (hK : 2 ≤ K) :
    traceTailUsed trace 0 K =
      trace.used 0 + trace.used 1 + traceTailUsed trace 2 (K - 2) := by
  cases K with
  | zero => omega
  | succ K =>
      cases K with
      | zero => omega
      | succ q =>
          have hsub : 1 + (q + 1) - 2 = q := by omega
          simp [traceTailUsed, hsub, Nat.add_comm]
          omega

theorem traceTailPower_zero_split
    {data : VIPublicData E} {S : StrongSolver data}
    {F : E → E} {oracle : FeasibleExactSymmetricJetOracle data F}
    {eta delta : ℝ} {K : ℕ}
    (trace : ExtrapolatedHalpernTrace data S F oracle eta delta K)
    (P : E → E) (a : ℝ) (hK : 2 ≤ K) :
    traceTailPower trace P a 0 K =
      Real.rpow ‖(trace.warm 0).1 - P (trace.x 0).1‖ a +
      Real.rpow ‖(trace.warm 1).1 - P (trace.x 1).1‖ a +
        traceTailPower trace P a 2 (K - 2) := by
  cases K with
  | zero => omega
  | succ K =>
      cases K with
      | zero => omega
      | succ q => simp [traceTailPower, add_assoc]

theorem ExtrapolatedHalpernTrace.warmPower_le_boostUa
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (R e eta a : ℝ) (hR : 0 < R) (heta : 0 < eta)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (K : ℕ) (hK : 2 ≤ K)
    (he : e = R / (K + 2 : ℝ) ^ 4)
    (zStar : E) (hzStar : IsVISolution data F zStar)
    (hdistance : ‖data.x0 - zStar‖ ≤ R)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta (e / eta) K) :
    traceTailPower trace (analysisResolvent data F hF eta heta) a 0 K ≤
      Real.rpow R a * boostUa a K := by
  let P := analysisResolvent data F hF eta heta
  let r := fun t => ‖(trace.warm t).1 - P (trace.x t).1‖
  have hwarm := trace.warmEnergy data S gamma b hS F oracle hF R e eta hR heta K hK
    he zStar hzStar hdistance
  have hrpow0 : Real.rpow (r 0) a ≤ Real.rpow (3 * R) a :=
    Real.rpow_le_rpow (norm_nonneg _) hwarm.1.1 ha0
  have hrpow1 : Real.rpow (r 1) a ≤ Real.rpow (3 * R) a :=
    Real.rpow_le_rpow (norm_nonneg _) hwarm.1.2 ha0
  have hmul3 : Real.rpow (3 * R) a = Real.rpow 3 a * Real.rpow R a :=
    Real.mul_rpow (by positivity) hR.le
  have hblocks :
      ∑ t ∈ Finset.Icc 2 K, Real.rpow (r t) a ≤
        ∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
          Real.rpow 16 a * Real.rpow R a *
            Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
              Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2)) := by
    refine (sum_Icc_two_le_dyadic_blocks K hK
      (fun t => Real.rpow (r t) a)
        (fun t => Real.rpow_nonneg (norm_nonneg _) a)).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    let k := 2 ^ j
    let ell := min (2 ^ (j + 1) - 1) K
    have hkpos : 0 < k := by dsimp [k]; positivity
    have hk2 : 2 ≤ k := by
      exact (show 2 ^ 1 ≤ 2 ^ j from Nat.pow_le_pow_right (by omega) hj'.1)
    have hkK : k ≤ K := by
      have hjlog : 2 ^ j ≤ 2 ^ Nat.log 2 K :=
        Nat.pow_le_pow_right (by omega) hj'.2
      exact hjlog.trans (Nat.pow_log_le_self 2 (by omega : K ≠ 0))
    have hkell : k ≤ ell := by
      apply Nat.le_min.mpr
      constructor
      · have : 2 ^ (j + 1) = 2 * k := by simp [k, pow_succ, mul_comm]
        omega
      · exact hkK
    have helltwice : ell ≤ 2 * k - 1 := by
      exact (min_le_left _ _).trans_eq (by simp [k, pow_succ, mul_comm])
    have hellK : ell ≤ K := min_le_right _ _
    have henergy := hwarm.2 k ell hk2 hkell helltwice hellK
    have hB0 : 0 ≤ 256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) /
        (k : ℝ) ^ 2 := by positivity
    have hmean := dyadic_power_sum_of_energy r hkell
      (fun t ht => norm_nonneg _) a
      (256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2)
      ha0 ha2 hB0 henergy
    have hcardNat : (Finset.Icc k ell).card ≤ k := by
      rw [Nat.card_Icc]
      omega
    have hcard : ((Finset.Icc k ell).card : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hcardNat
    have hq : 0 ≤ 1 - a / 2 := by linarith
    have hcardpow := Real.rpow_le_rpow (by positivity :
      (0 : ℝ) ≤ (Finset.Icc k ell).card) hcard hq
    have hnorm := dyadic_warm_power_normalization a R
      (1 + harmonicR (2 * k)) (k : ℝ) hR.le
      (by linarith [harmonicR_nonneg (2 * k)]) (by exact_mod_cast hkpos)
    have hkpow : Real.rpow (k : ℝ) (1 - 3 * a / 2) =
        Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2)) := by
      dsimp [k]
      rw [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast (2 : ℝ) j]
      exact (Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2) (j : ℝ)
        (1 - 3 * a / 2)).symm
    calc
      ∑ t ∈ Finset.Icc k ell, Real.rpow (r t) a ≤
          Real.rpow ((Finset.Icc k ell).card : ℝ) (1 - a / 2) *
            Real.rpow (256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) /
              (k : ℝ) ^ 2) (a / 2) := hmean
      _ ≤ Real.rpow (k : ℝ) (1 - a / 2) *
            Real.rpow (256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) /
              (k : ℝ) ^ 2) (a / 2) := by
        exact mul_le_mul_of_nonneg_right hcardpow
          (Real.rpow_nonneg hB0 (a / 2))
      _ = Real.rpow 16 a * Real.rpow R a *
            Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
              Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2)) := by
        rw [hnorm, hkpow]
        simp only [k, show 2 * 2 ^ j = 2 ^ (j + 1) by rw [pow_succ]; ring]
  rw [traceTailPower_zero_split trace P a hK,
    traceTailPower_eq_sum_Icc trace P a 2 (K - 2)]
  have hsumend : 2 + (K - 2) = K := by omega
  rw [hsumend]
  change Real.rpow (r 0) a + Real.rpow (r 1) a +
      (∑ t ∈ Finset.Icc 2 K, Real.rpow (r t) a) ≤ _
  calc
    Real.rpow (r 0) a + Real.rpow (r 1) a +
        (∑ t ∈ Finset.Icc 2 K, Real.rpow (r t) a) ≤
      2 * (Real.rpow 3 a * Real.rpow R a) +
        ∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
          Real.rpow 16 a * Real.rpow R a *
            Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
              Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2)) := by
      rw [← hmul3]
      linarith
    _ = Real.rpow R a * boostUa a K := by
      unfold boostUa
      have hfactor :
          (∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
            Real.rpow 16 a * Real.rpow R a *
              Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
                Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2))) =
          (Real.rpow R a * Real.rpow 16 a) *
            ∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
              Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
                Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hfactor]
      rw [mul_add]
      ring

theorem ExtrapolatedHalpernTrace.tail_evaluates
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (R epsilon e eta : ℝ) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (K : ℕ) (hK : 2 ≤ K)
    (he : e = R / (K + 2 : ℝ) ^ 4)
    (hetadef : eta = 8 * R * (1 + harmonicR (K + 1)) /
      (epsilon * (K + 1 : ℝ)))
    (zStar : E) (hzStar : IsVISolution data F zStar)
    (hdistance : ‖data.x0 - zStar‖ ≤ R)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta (e / eta) K)
    (t remaining : ℕ) (ht : 2 ≤ t) (hsum : t + remaining = K) :
    ExactJetProgram.Evaluates oracle.answer
      (extrapolatedHalpernTail data S eta (e / eta) epsilon remaining t
        (trace.x t) (trace.yHat (t - 1)) (trace.yHat (t - 2)))
      (traceTailUsed trace t remaining)
      (some (recoverBaseCertificate data eta (trace.x K).1 (trace.cert K))) := by
  induction remaining generalizing t with
  | zero =>
      have htK : t = K := by omega
      subst t
      simp only [extrapolatedHalpernTail, traceTailUsed]
      have hwarm := trace.warm_later K hK le_rfl
      rw [← hwarm]
      have hhalt : ExactJetProgram.Evaluates oracle.answer
          (.halt (checkedRecoveredCertificate data eta epsilon (trace.x K).1
            (trace.cert K))) 0
          (some (recoverBaseCertificate data eta (trace.x K).1 (trace.cert K))) := by
        rw [trace.final_check_succeeds data S gamma b hS F oracle hF
          R epsilon e eta hR hepsilon heta K hK he hetadef zStar hzStar hdistance]
        exact .halt _
      simpa using ExactJetProgram.Evaluates.bind
        (next := fun cert => .halt
          (checkedRecoveredCertificate data eta epsilon (trace.x K).1 cert))
        (trace.call_evaluates K le_rfl) hhalt
  | succ remaining ih =>
      have htK : t ≤ K := by omega
      have htlt : t < K := by omega
      simp only [extrapolatedHalpernTail, traceTailUsed]
      have hwarm := trace.warm_later t ht htK
      rw [← hwarm]
      apply ExactJetProgram.Evaluates.bind (trace.call_evaluates t htK)
      have hpoint := trace.point_eq t htK
      have hupdate := trace.update t htlt
      rw [hpoint, ← hupdate]
      have htm1 : t + 1 - 1 = t := by omega
      have htm2 : t + 1 - 2 = t - 1 := by omega
      simpa [htm1, htm2, Nat.add_assoc] using
        ih (t + 1) (by omega) (by omega)

theorem ExtrapolatedHalpernTrace.program_evaluates
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (R epsilon e eta : ℝ) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (K : ℕ) (hK : 2 ≤ K)
    (he : e = R / (K + 2 : ℝ) ^ 4)
    (hetadef : eta = 8 * R * (1 + harmonicR (K + 1)) /
      (epsilon * (K + 1 : ℝ)))
    (zStar : E) (hzStar : IsVISolution data F zStar)
    (hdistance : ‖data.x0 - zStar‖ ≤ R)
    (trace : ExtrapolatedHalpernTrace data S F oracle eta (e / eta) K) :
    ExactJetProgram.Evaluates oracle.answer
      (extrapolatedHalpernProgram data S K eta (e / eta) epsilon)
      (trace.used 0 + trace.used 1 + traceTailUsed trace 2 (K - 2))
      (some (recoverBaseCertificate data eta (trace.x K).1 (trace.cert K))) := by
  have htail := trace.tail_evaluates data S gamma b hS F oracle hF
    R epsilon e eta hR hepsilon heta K hK he hetadef zStar hzStar hdistance
    2 (K - 2) (by omega) (by omega)
  have hpoint0 := trace.point_eq 0 (by omega : 0 ≤ K)
  have hpoint1 := trace.point_eq 1 (by omega : 1 ≤ K)
  have hupdate0 := trace.update 0 (by omega : 0 < K)
  have hupdate1 := trace.update 1 (by omega : 1 < K)
  have hwarm0 := trace.warm_zero
  have hx0 := trace.x_zero
  have hwarm1 := trace.warm_one
  have htail' : ExactJetProgram.Evaluates oracle.answer
      (extrapolatedHalpernTail data S eta (e / eta) epsilon (K - 2) 2
        (feasibleHalpernUpdate data 1 (trace.cert 1).point)
        (trace.cert 1).point (trace.cert 0).point)
      (traceTailUsed trace 2 (K - 2))
      (some (recoverBaseCertificate data eta (trace.x K).1 (trace.cert K))) := by
    rw [hpoint0, hpoint1, ← hupdate1]
    simpa using htail
  have hbind1 := ExactJetProgram.Evaluates.bind
    (next := fun cert₁ => extrapolatedHalpernTail data S eta (e / eta) epsilon
      (K - 2) 2 (feasibleHalpernUpdate data 1 cert₁.point) cert₁.point
        (trace.cert 0).point)
    (trace.call_evaluates 1 (by omega : 1 ≤ K)) htail'
  have hbind1' : ExactJetProgram.Evaluates oracle.answer
      ((compiledStrongProgram data S eta (e / eta)
        (feasibleHalpernUpdate data 0 (trace.cert 0).point)
        (trace.cert 0).point).bind (fun cert₁ =>
          extrapolatedHalpernTail data S eta (e / eta) epsilon (K - 2) 2
            (feasibleHalpernUpdate data 1 cert₁.point) cert₁.point
              (trace.cert 0).point))
      (trace.used 1 + traceTailUsed trace 2 (K - 2))
      (some (recoverBaseCertificate data eta (trace.x K).1 (trace.cert K))) := by
    simpa [hpoint0, hupdate0, hwarm1] using hbind1
  have hbind0 := ExactJetProgram.Evaluates.bind
    (next := fun cert₀ =>
      (compiledStrongProgram data S eta (e / eta)
        (feasibleHalpernUpdate data 0 cert₀.point) cert₀.point).bind (fun cert₁ =>
          extrapolatedHalpernTail data S eta (e / eta) epsilon (K - 2) 2
            (feasibleHalpernUpdate data 1 cert₁.point) cert₁.point cert₀.point))
    (trace.call_evaluates 0 (by omega : 0 ≤ K)) hbind1'
  simpa [extrapolatedHalpernProgram, hx0, hwarm0, hpoint0, hupdate0,
    hwarm1, Nat.add_assoc] using hbind0

theorem extrapolatedHalpernCall_completes
    (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ) (hS : S.SatisfiesInterface data gamma b)
    (hgamma : 0 < gamma)
    (ha2 : ((data.p - 1 : ℕ) : ℝ) * gamma ≤ 2)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F)
    (K : ℕ) (hK : 2 ≤ K) (R epsilon : ℝ)
    (hR : 0 < R) (hepsilon : 0 < epsilon)
    (zStar : E) (hzStar : IsVISolution data F zStar)
    (hdistance : ‖data.x0 - zStar‖ ≤ R) :
    ∃ used cert,
      CappedExactJetCall.execute data F oracle
        (extrapolatedHalpernCall data S gamma b K R epsilon
          (boostOuterError R K) (boostStepsize R epsilon K)) =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data F epsilon ∧
      used ≤ boostSharedCap data S gamma b K R
        (boostStepsize R epsilon K) (boostOuterError R K) := by
  let e := boostOuterError R K
  let eta := boostStepsize R epsilon K
  have hedef : e = R / (K + 2 : ℝ) ^ 4 := rfl
  have hetadef : eta = 8 * R * (1 + harmonicR (K + 1)) /
      (epsilon * (K + 1 : ℝ)) := rfl
  have heta : 0 < eta := boostStepsize_pos hR hepsilon K
  have hepos : 0 < e := boostOuterError_pos hR K
  have hdelta : 0 < e / eta := div_pos hepos heta
  let trace := canonicalExtrapolatedHalpernTrace data S gamma b hS F oracle hF
    eta (e / eta) heta hdelta K
  have heval := ExtrapolatedHalpernTrace.program_evaluates data S gamma b hS F
    oracle hF R epsilon e eta hR hepsilon heta K hK hedef hetadef zStar hzStar
      hdistance trace
  have hcost := canonical_trace_tail_cost data S gamma b hS F oracle hF eta
    (e / eta) heta hdelta K trace rfl 0 K
  have ha0 : 0 ≤ ((data.p - 1 : ℕ) : ℝ) * gamma := by positivity
  have hpower := ExtrapolatedHalpernTrace.warmPower_le_boostUa data S gamma b hS
    F oracle hF R e eta (((data.p - 1 : ℕ) : ℝ) * gamma) hR heta ha0 ha2 K hK
      hedef zStar hzStar hdistance trace
  have hfactor : 0 ≤ Real.rpow (eta * data.Lp) gamma :=
    Real.rpow_nonneg (mul_nonneg heta.le data.Lp_pos.le) gamma
  have hA : 0 ≤ S.leadingConstant *
      (strongLog data (1 / eta) (e / eta)) ^ b := by
    have hlogArg : 1 ≤ 2 + data.Lp * data.D ^ (data.p - 1) / (1 / eta) +
        data.Lp * data.D ^ data.p / (e / eta) +
          (1 / eta) * data.D / (e / eta) := by
      have hD := data.D_pos.le
      have hmu : 0 < 1 / eta := by positivity
      have hdel : 0 < e / eta := hdelta
      have h1 : 0 ≤ data.Lp * data.D ^ (data.p - 1) / (1 / eta) :=
        div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hD _)) hmu.le
      have h2 : 0 ≤ data.Lp * data.D ^ data.p / (e / eta) :=
        div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hD _)) hdel.le
      have h3 : 0 ≤ (1 / eta) * data.D / (e / eta) :=
        div_nonneg (mul_nonneg hmu.le hD) hdel.le
      linarith
    have hlog : 0 ≤ strongLog data (1 / eta) (e / eta) := by
      unfold strongLog
      linarith [Real.log_nonneg hlogArg]
    exact mul_nonneg S.leadingConstant_pos.le (pow_nonneg hlog b)
  have htotal :
      ((trace.used 0 + trace.used 1 + traceTailUsed trace 2 (K - 2) : ℕ) : ℝ) ≤
        S.leadingConstant * (strongLog data (1 / eta) (e / eta)) ^ b *
          (K + 1 + Real.rpow (eta * data.Lp) gamma *
            Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) *
              boostUa (((data.p - 1 : ℕ) : ℝ) * gamma) K) := by
    rw [← traceTailUsed_zero_eq_programUsed trace hK]
    calc
      (traceTailUsed trace 0 K : ℝ) ≤
          S.leadingConstant * (strongLog data (1 / eta) (e / eta)) ^ b *
            ((K + 1 : ℕ) + Real.rpow (eta * data.Lp) gamma *
              traceTailPower trace (analysisResolvent data F hF eta heta)
                (((data.p - 1 : ℕ) : ℝ) * gamma) 0 K) := hcost
      _ ≤ S.leadingConstant * (strongLog data (1 / eta) (e / eta)) ^ b *
          (K + 1 + Real.rpow (eta * data.Lp) gamma *
            Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) *
              boostUa (((data.p - 1 : ℕ) : ℝ) * gamma) K) := by
        apply mul_le_mul_of_nonneg_left _ hA
        have hp := mul_le_mul_of_nonneg_left hpower hfactor
        norm_num at ⊢
        calc
          Real.rpow (eta * data.Lp) gamma *
              traceTailPower trace (analysisResolvent data F hF eta heta)
                (((data.p - 1 : ℕ) : ℝ) * gamma) 0 K ≤
            Real.rpow (eta * data.Lp) gamma *
              (Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) *
                boostUa (((data.p - 1 : ℕ) : ℝ) * gamma) K) := hp
          _ = Real.rpow (eta * data.Lp) gamma *
              Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) *
                boostUa (((data.p - 1 : ℕ) : ℝ) * gamma) K := by ring
  let core := S.leadingConstant * (strongLog data (1 / eta) (e / eta)) ^ b *
    (K + 1 + Real.rpow (eta * data.Lp) gamma *
      Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) *
        boostUa (((data.p - 1 : ℕ) : ℝ) * gamma) K)
  have hceilReal :
      ((trace.used 0 + trace.used 1 + traceTailUsed trace 2 (K - 2) : ℕ) : ℝ) ≤
        (Nat.ceil core : ℕ) := htotal.trans (Nat.le_ceil core)
  have hceilNat : trace.used 0 + trace.used 1 + traceTailUsed trace 2 (K - 2) ≤
      Nat.ceil core := by exact_mod_cast hceilReal
  have hcap : trace.used 0 + trace.used 1 + traceTailUsed trace 2 (K - 2) ≤
      boostSharedCap data S gamma b K R eta e := by
    change trace.used 0 + trace.used 1 + traceTailUsed trace 2 (K - 2) ≤
      Nat.ceil core + 1
    omega
  have hrun := heval.runWithFuel_eq hcap
  let cert := recoverBaseCertificate data eta (trace.x K).1 (trace.cert K)
  refine ⟨trace.used 0 + trace.used 1 + traceTailUsed trace 2 (K - 2), cert, ?_,
    ?_, hcap⟩
  · simpa [CappedExactJetCall.execute, extrapolatedHalpernCall, e, eta, cert]
      using hrun
  · exact ExtrapolatedHalpernTrace.final_recovered_verified data S gamma b hS F
      oracle hF R epsilon e eta hR hepsilon heta K hK hedef hetadef zStar hzStar
        hdistance trace

/-- Audit-facing completed operational core of `thm:boost`.  Unlike
`BoostExecutionClaim`, this statement does not assume a successful execution:
under a true radius promise it proves that the source's shared cap is large
enough for the finite `K+1`-call program to finish and return a verified
original-operator certificate. -/
def BoostCapCompletionClaim : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (S : StrongSolver data)
    (gamma : ℝ) (b : ℕ), S.SatisfiesInterface data gamma b →
    0 < gamma → (((data.p - 1 : ℕ) : ℝ) * gamma ≤ 2) →
    ∀ (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F),
      IsAdmissibleOperator data F →
      ∀ K, 2 ≤ K → ∀ R epsilon, 0 < R → 0 < epsilon →
      ∀ zStar, IsVISolution data F zStar → ‖data.x0 - zStar‖ ≤ R →
      ∃ used cert,
        CappedExactJetCall.execute data F oracle
          (extrapolatedHalpernCall data S gamma b K R epsilon
            (boostOuterError R K) (boostStepsize R epsilon K)) =
          .finished used (some cert) ∧
        cert.IsVerifiedFor data F epsilon ∧
        used ≤ boostSharedCap data S gamma b K R
          (boostStepsize R epsilon K) (boostOuterError R K)

theorem boostCapCompletionClaim_proof : BoostCapCompletionClaim := by
  intro E _ _ _ data S gamma b hS hgamma ha2 F oracle hF K hK R epsilon
    hR hepsilon zStar hzStar hdistance
  exact extrapolatedHalpernCall_completes data S gamma b hS hgamma ha2 F oracle
    hF K hK R epsilon hR hepsilon zStar hzStar hdistance

end AnalyticTrace

end FiniteAlgorithm

end

end LeanArticleAudit.Pilot
