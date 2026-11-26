import MinimaxAudit.CriterionFull
import MinimaxAudit.ScalarVI
import VIReference.Pilot.UpperBorelFinalAssembly
import MinimaxAudit.MeasurableExecution
import MinimaxAudit.EvaluatedPolicy
import VIReference.Pilot.UpperBorelComplexity

/-!
Executable scalar-oracle upper reduction. An arbitrary scalar response is
converted to a symmetric operator response by a total fixed rule; on genuine
responses the conversion is exactly the actual saddle-operator jet.
-/
open Set MeasureTheory
namespace MinimaxAudit.ScalarUpper
open VIReference.Pilot
open MeasurableExecution

noncomputable section

/-- Total conversion on fake histories as well as genuine oracle responses.
The fallback is used only for an input tensor failing symmetry. -/
def makeSymmetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E) :
    SymmetricContinuousMultilinearMap E k := by
  classical
  exact if h : IsSymmetricContinuousMultilinearMap E A then ⟨A, h⟩ else ⟨0, fun _ => rfl⟩

@[simp] theorem make_symmetric_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E)
    (h : IsSymmetricContinuousMultilinearMap E A) : (makeSymmetric A).1 = A := by
  simp [makeSymmetric, h]

/-- A fixed complete scalar p-jet determines one full order-p operator jet.
The response value at operator arity zero comes from scalar derivative one. -/
def scalarJetToSymmetricOperatorJet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (p : ℕ) (S : E ≃ₗᵢ[ℝ] E)
    (J : ScalarJet p E) : SymmetricExactJet E p :=
  fun k => makeSymmetric (scalarToSaddleTensor S (J ⟨k.1 + 1, by omega⟩))

/-- The total history conversion returns the actual operator tensor on
every genuine scalar jet. Finite differentiability proves its symmetry. -/
theorem scalar_jet_conversion_exact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (p : ℕ) (S : E ≃ₗᵢ[ℝ] E)
    (f : E → ℝ) (z : E) (hOp : ContDiffAt ℝ (↑(p - 1 : ℕ)) (S ∘ gradient f) z)
    (k : Fin p) :
    ((scalarJetToSymmetricOperatorJet p S (exactScalarJet p f z)) k).1 =
      iteratedFDeriv ℝ k.1 (S ∘ gradient f) z := by
  unfold scalarJetToSymmetricOperatorJet exactScalarJet
  rw [← scalar_jet_to_saddle_jet S f k.1 z]
  apply make_symmetric_eq
  intro sigma
  exact finiteContDiffAt_iteratedFDeriv_symmetric
    (hOp.of_le (by exact_mod_cast (by omega : k.1 ≤ p - 1))) sigma

section Compiler
variable {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}
variable {Answer : Type*} [MeasurableSpace Answer]

/-- Fixed answer conversion of an arbitrary feasible scalar list history. -/
def convertedHistory (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (h : ScalarHistory p dx dy) (hfeas : ∀ e ∈ h, e.1 ∈ productDomain X Y) :
    OracleHistory (productDomain X Y) Answer h.length :=
  fun i => (⟨(h.get i).1, hfeas (h.get i) (List.get_mem _ _)⟩, convertAnswer (h.get i).2)


/-- A converted record retains its exact length in a dependent pair. -/
def convertedRecord (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (h : ScalarHistory p dx dy) (hfeas : ∀ e ∈ h, e.1 ∈ productDomain X Y) :
    Σ n : ℕ, OracleHistory (productDomain X Y) Answer n :=
  ⟨h.length, convertedHistory convertAnswer h hfeas⟩

/-- A reference rule extended to all history lengths by a public stop. -/
def boundedRule
    (P : BorelStoppingPolicy (Answer := Answer) (productDomain X Y) N)
    (seed : P.Seed) (fill : productDomain X Y)
    (record : Σ n : ℕ, OracleHistory (productDomain X Y) Answer n) :
    OracleAction (productDomain X Y) := by
  classical
  exact if hn : record.1 ≤ N then P.rule ⟨record.1, by omega⟩ (seed, record.2)
    else Sum.inl fill

/-- The fixed operator policy acts on exactly the converted source history.
Malformed/off-budget histories are stopped at a public feasible point. -/
def compiledAction
    (P : BorelStoppingPolicy (Answer := Answer) (productDomain X Y) N)
    (seed : P.Seed) (fill : productDomain X Y)
    (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (h : ScalarHistory p dx dy) : OracleAction (productDomain X Y) := by
  classical
  exact if hf : ∀ e ∈ h, e.1 ∈ productDomain X Y then
    boundedRule P seed fill (convertedRecord convertAnswer h hf)
  else Sum.inl fill

/-- A concrete total, feasible, capped source deterministic scalar policy.
Only public data, the fixed operator policy, and scalar responses are used. -/
def compileScalarPolicy
    (P : BorelStoppingPolicy (Answer := Answer) (productDomain X Y) N)
    (seed : P.Seed) (fill : productDomain X Y)
    (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer) :
    DeterministicScalarPolicy p dx dy N X Y where
  query h := match compiledAction P seed fill convertAnswer h with
    | Sum.inl _ => none
    | Sum.inr q => some q.1
  output h := match compiledAction P seed fill convertAnswer h with
    | Sum.inl out => out.1
    | Sum.inr _ => fill.1
  cap h hn := by
    unfold compiledAction
    split_ifs with hfeas
    · unfold boundedRule convertedRecord
      split_ifs with hlen
      · have heq : h.length = N := Nat.le_antisymm hlen hn
        subst N
        obtain ⟨out, ho⟩ := P.cap_stops (seed, convertedHistory convertAnswer h hfeas)
        rw [ho]
      · rfl
    · rfl
  feasible_query h z hq := by
    cases ha : compiledAction P seed fill convertAnswer h with
    | inl out => simp [ha] at hq
    | inr q =>
      simp only [ha, Option.some.injEq] at hq
      simpa [← hq] using q.property
  feasible_output h := by
    cases ha : compiledAction P seed fill convertAnswer h with
    | inl out => exact out.property
    | inr q => exact fill.property

/-- Finite scalar records have feasible points independently of their answers. -/
theorem finite_scalar_history_feasible {n : ℕ}
    (h : FiniteHistory (p := p) X Y n) :
    ∀ e ∈ finiteHistoryList h, e.1 ∈ productDomain X Y := by
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact (h i).1.property

/-- The response compiler preserves every record entry and its position. -/
theorem converted_record_of_finite {n : ℕ}
    (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (h : FiniteHistory (p := p) X Y n)
    (hf : ∀ e ∈ finiteHistoryList h, e.1 ∈ productDomain X Y) :
    convertedRecord convertAnswer (finiteHistoryList h) hf =
      ⟨n, fun i => ((h i).1, convertAnswer (h i).2)⟩ := by
  apply Sigma.ext (by simp [convertedRecord])
  apply (Fin.heq_fun_iff (by simp [convertedRecord])).2
  intro i
  apply Prod.ext
  · apply Subtype.ext
    simp [convertedRecord, convertedHistory, finiteHistoryList]
  · simp [convertedRecord, convertedHistory, finiteHistoryList]

/-- On any feasible finite scalar transcript, the compiled action is
exactly the original reference rule on the converted answers. -/
theorem compiled_action_of_finite {n : ℕ}
    (P : BorelStoppingPolicy (Answer := Answer) (productDomain X Y) N)
    (seed : P.Seed) (fill : productDomain X Y)
    (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (h : FiniteHistory (p := p) X Y n) (hn : n ≤ N) :
    compiledAction P seed fill convertAnswer (finiteHistoryList h) =
      P.rule ⟨n, by omega⟩ (seed, fun i => ((h i).1, convertAnswer (h i).2)) := by
  unfold compiledAction
  rw [dif_pos (finite_scalar_history_feasible h), converted_record_of_finite]
  simp [boundedRule, hn]

/-- Replace only the answers of a feasible operator transcript by actual
scalar-oracle answers at exactly the same points. -/
def scalarHistoryFromOracle
    (scalarOracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    {n : ℕ} (h : OracleHistory (productDomain X Y) Answer n) : FiniteHistory (p := p) X Y n :=
  fun i => ((h i).1, scalarOracle (h i).1.1)

/-- On a genuine oracle transcript, scalar-response conversion reconstructs
the original operator history entry by entry. -/
theorem compiled_action_on_oracle_history {n : ℕ}
    (P : BorelStoppingPolicy (Answer := Answer) (productDomain X Y) N)
    (seed : P.Seed) (fill : productDomain X Y)
    (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (scalarOracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (h : OracleHistory (productDomain X Y) Answer n) (hn : n ≤ N)
    (hanswers : ∀ i, (h i).2 = convertAnswer (scalarOracle (h i).1.1)) :
    compiledAction P seed fill convertAnswer
      (finiteHistoryList (scalarHistoryFromOracle scalarOracle h)) =
      P.rule ⟨n, by omega⟩ (seed, h) := by
  rw [compiled_action_of_finite P seed fill convertAnswer _ hn]
  congr 2
  funext i
  exact Prod.ext rfl (hanswers i).symm

/-- Actual scalar execution of the compiled policy has exactly the same
output as every genuine reference unpadded run, using no extra queries. -/
theorem scalar_run_of_reference_unpadded {n : ℕ}
    (P : BorelStoppingPolicy (Answer := Answer) (productDomain X Y) N)
    (seed : P.Seed) (fill : productDomain X Y)
    (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (scalarOracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (operatorOracle : SaddleSpace dx dy → Answer)
    (hconvert : ∀ z ∈ productDomain X Y, convertAnswer (scalarOracle z) = operatorOracle z)
    (hn : n ≤ N) (h : OracleHistory (productDomain X Y) Answer n) (out : productDomain X Y)
    (hrun : P.IsUnpaddedRun operatorOracle seed n hn h out) :
    Deterministic.runScalarPolicy (compileScalarPolicy P seed fill convertAnswer) scalarOracle N [] = out.1 := by
  have hanswers (i : Fin n) : (h i).2 = convertAnswer (scalarOracle (h i).1.1) := by
    rw [(hrun.1 i).2, hconvert _ (h i).1.property]
  let hS := scalarHistoryFromOracle scalarOracle h
  have hlast := compiled_action_on_oracle_history P seed fill convertAnswer scalarOracle h hn hanswers
  have hlast' : compiledAction P seed fill convertAnswer (finiteHistoryList hS) = Sum.inl out :=
    hlast.trans hrun.2
  apply run_eq_of_recorded_list (compileScalarPolicy P seed fill convertAnswer) scalarOracle
    (finiteHistoryList hS) [] out.1 N (by simpa using hn)
  · intro i hi
    have hin : i < n := by simpa using hi
    let j : Fin n := ⟨i, hin⟩
    have hprefix := compiled_action_on_oracle_history P seed fill convertAnswer scalarOracle
      (OracleHistory.restrict h (Nat.le_of_lt j.2)) (Nat.le_trans (Nat.le_of_lt j.2) hn)
      (fun k => hanswers ⟨k.1, Nat.lt_of_lt_of_le k.2 (Nat.le_of_lt j.2)⟩)
    have hSrestrict : scalarHistoryFromOracle scalarOracle
        (OracleHistory.restrict h (Nat.le_of_lt j.2)) =
        OracleHistory.restrict hS (Nat.le_of_lt j.2) := rfl
    rw [hSrestrict, finite_history_list_restrict] at hprefix
    have hq : (compileScalarPolicy P seed fill convertAnswer).query
        ((finiteHistoryList hS).take i) = some (h j).1.1 := by
      change (match compiledAction P seed fill convertAnswer ((finiteHistoryList hS).take i) with
        | Sum.inl _ => none | Sum.inr q => some q.1) = _
      rw [hprefix, (hrun.1 j).1]
    simpa [finiteHistoryList, scalarHistoryFromOracle, hS, j] using And.intro hq (rfl :
      scalarOracle (h j).1.1 = scalarOracle (h j).1.1)
  · change (match compiledAction P seed fill convertAnswer (finiteHistoryList hS) with
      | Sum.inl _ => none | Sum.inr q => some q.1) = none
    rw [hlast']
  · change (match compiledAction P seed fill convertAnswer (finiteHistoryList hS) with
      | Sum.inl out => out.1 | Sum.inr _ => fill.1) = out.1
    rw [hlast']

end Compiler
/-- Exact source display, including its additive low-ratio constant. -/
def scalarUpperCost (p : ℕ) (C L D epsilon : ℝ) : ℝ :=
  C * (1 + (L * D ^ p / epsilon) ^ (2 / (3 * p - 1 : ℝ))) *
    (1 + Real.log (3 + L * D ^ p / epsilon)) ^ (6 * (p - 1))

/-- A single objective-independent source policy attains the inherited
VI upper bound on every compatible scalar instance. The budget is the
actual public call cap of the constructed finite solver hierarchy. -/
theorem uniform_scalar_upper_positive_dimension (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (dx dy : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
      (hL : 0 < L) (hD : 0 < D) (hdim : 0 < dx + dy)
      (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
      (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
      (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
      (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
      (epsilon : ℝ) (hepsilon : 0 < epsilon),
      ∃ N : ℕ, ∃ A : DeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarUpperCost p C L D epsilon ∧
        ∀ (phi : SaddleSpace dx dy → ℝ), AdmissibleScalar p L D X Y phi →
          let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
          auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) output ≤ epsilon ∧
          ∃ normal, normal ∈ MinimaxAudit.normalCone (productDomain X Y) output ∧
            ‖scalarSaddleOperator phi output + normal‖ ≤ epsilon := by
  obtain ⟨family, hinterface, hBorel⟩ := final_upper_joint_borel_hierarchy p hp
  refine ⟨family.leadingConstant, family.leadingConstant_pos, ?_⟩
  intro dx dy L D X Y hL hD hdim hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  let data := ScalarVI.scalarVIData p L D X Y hp hL hD hdim hneX hneY hcX hcY hvX hvY hdiam z0 hz0
  let center : data.X := ⟨z0, hz0⟩
  let call := (family.atData data rfl).solve center D epsilon
  obtain ⟨P, hcontract, hdet, hcapstop, hsuccess⟩ :=
    family.exists_uniformCompiledBorelPolicy hBorel.isBorel
      (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) hinterface data rfl center D epsilon
  obtain ⟨seed⟩ := hdet.1
  letI : Subsingleton P.Seed := hdet.2
  let convertAnswer := scalarJetToSymmetricOperatorJet p (euclideanSaddleSign dx dy)
  let A := compileScalarPolicy P seed center convertAnswer
  refine ⟨call.cap, A, ?_, ?_⟩
  · have hcap := (hinterface (SaddleSpace dx dy) data rfl).1 center D epsilon hD le_rfl hepsilon
    change (call.cap : ℝ) ≤ residualInterfaceCost data family.leadingConstant
      (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) D epsilon at hcap
    simpa only [scalarUpperCost, residualInterfaceCost, residualCondition, residualLog,
      data, ScalarVI.scalarVIData, div_self hD.ne', show (2 : ℝ) + 1 = 3 by norm_num] using hcap
  · intro phi hadm
    let F := scalarSaddleOperator phi
    have hF : IsAdmissibleOperator data F :=
      ScalarVI.scalar_operator_is_admissible data rfl rfl rfl hadm
    obtain ⟨zstar, hzstar, hvi⟩ := ScalarVI.scalar_saddle_gives_vi_solution hadm
    have hsolution : IsVISolution data F zstar := ⟨hzstar, hvi⟩
    have hdist : ‖center.1 - zstar‖ ≤ D := hdiam z0 hz0 zstar hzstar
    obtain ⟨seed', used, cert, hn, history, hexecute, hrun, hcert, hcost⟩ :=
      hsuccess F hF hD le_rfl hepsilon zstar hsolution hdist
    have hseed : seed' = seed := Subsingleton.elim _ _
    subst seed'
    let oracle := hF.feasibleExactSymmetricJetOracle data F
    let operatorOracle := oracle.totalAnswer data F center
    have hconvert : ∀ z ∈ productDomain X Y,
        convertAnswer (exactScalarJet p phi z) = operatorOracle z := by
      intro z hz
      have htotal : operatorOracle z = oracle.answer ⟨z, hz⟩ := by
        exact FeasibleExactSymmetricJetOracle.totalAnswer_coe data F oracle center ⟨z, hz⟩
      rw [htotal]
      funext k
      apply Subtype.ext
      obtain ⟨O, hO, hZO, hreg⟩ := ScalarVI.scalar_operator_regularity hadm
      have hOp : ContDiffAt ℝ (↑(p - 1 : ℕ)) ((euclideanSaddleSign dx dy) ∘ gradient phi) z :=
        hreg.contDiffAt (hO.mem_nhds (hZO hz))
      exact (scalar_jet_conversion_exact p (euclideanSaddleSign dx dy) phi z hOp k).trans
        (oracle.exact ⟨z, hz⟩ k).symm
    have hout := scalar_run_of_reference_unpadded P seed center convertAnswer
      (exactScalarJet p phi) operatorOracle hconvert hn history cert.point hrun.1
    change auditedTangentResidual (productDomain X Y) F
        (Deterministic.runScalarPolicy A (exactScalarJet p phi) call.cap []) ≤ epsilon ∧ _
    have hout' : Deterministic.runScalarPolicy A (exactScalarJet p phi) call.cap [] = cert.point.1 := hout
    rw [hout']
    constructor
    · have hres := cert.tangentResidual_le data F epsilon hcert
      rwa [ScalarVI.tangent_residual_eq_source data rfl F cert.point.1] at hres
    · exact ⟨cert.normal, hcert.1, by simpa only [hcert.2.1] using hcert.2.2⟩

/-- Uniform source success with a genuine same-point normal certificate. -/
def ScalarResidualPolicySucceeds {p dx dy N : ℕ} (L D epsilon : ℝ)
    (X : Set (Primal dx)) (Y : Set (Dual dy))
    (A : DeterministicScalarPolicy p dx dy N X Y) : Prop :=
  ∀ (phi : SaddleSpace dx dy → ℝ), AdmissibleScalar p L D X Y phi →
    let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
    auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) output ≤ epsilon ∧
    ∃ normal, normal ∈ MinimaxAudit.normalCone (productDomain X Y) output ∧
      ‖scalarSaddleOperator phi output + normal‖ ≤ epsilon

theorem scalar_upper_cost_mono_constant {p : ℕ} {C C' L D epsilon : ℝ}
    (hC : C ≤ C') (hL : 0 < L) (hD : 0 < D) (hepsilon : 0 < epsilon) :
    scalarUpperCost p C L D epsilon ≤ scalarUpperCost p C' L D epsilon := by
  have hQ : 0 ≤ L * D ^ p / epsilon := by positivity
  have hpow := Real.rpow_nonneg hQ (2 / (3 * p - 1 : ℝ))
  have hlog : 0 ≤ Real.log (3 + L * D ^ p / epsilon) := Real.log_nonneg (by linarith)
  unfold scalarUpperCost
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (by linarith)) (by positivity)

theorem scalar_upper_cost_ge_constant {p : ℕ} {C L D epsilon : ℝ}
    (hC : 0 ≤ C) (hL : 0 < L) (hD : 0 < D) (hepsilon : 0 < epsilon) :
    C ≤ scalarUpperCost p C L D epsilon := by
  have hQ : 0 ≤ L * D ^ p / epsilon := by positivity
  have hpow : 1 ≤ 1 + (L * D ^ p / epsilon) ^ (2 / (3 * p - 1 : ℝ)) := by
    have := Real.rpow_nonneg hQ (2 / (3 * p - 1 : ℝ))
    linarith
  have hlog : 0 ≤ Real.log (3 + L * D ^ p / epsilon) := Real.log_nonneg (by linarith)
  have hlogpow : 1 ≤ (1 + Real.log (3 + L * D ^ p / epsilon)) ^ (6 * (p - 1)) :=
    one_le_pow₀ (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hpow hC
  have h2 := mul_le_mul_of_nonneg_left hlogpow
    (mul_nonneg hC (le_trans zero_le_one hpow))
  unfold scalarUpperCost
  calc
    C ≤ C * (1 + (L * D ^ p / epsilon) ^ (2 / (3 * p - 1 : ℝ))) := by simpa using h1
    _ ≤ _ := by simpa using h2

/-- An evaluated constant-output policy for the zero-dimensional edge case. -/
def oneQueryPolicy {p dx dy : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y) :
    DeterministicScalarPolicy p dx dy 1 X Y := by
  classical
  exact {
    query := fun h => if h = [] then some z0 else none
    output := fun _ => z0
    cap := by
      intro h hh
      have hn : h ≠ [] := by intro he; simp [he] at hh
      simp [hn]
    feasible_query := by
      intro h z hz
      split_ifs at hz with hh
      · simp only [Option.some.injEq] at hz
        simpa [← hz] using hz0
    feasible_output := fun _ => hz0 }

theorem one_query_policy_run {p dx dy : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) :
    Deterministic.runScalarPolicy (oneQueryPolicy (p := p) z0 hz0) oracle 1 [] = z0 := by
  simp [Deterministic.runScalarPolicy, oneQueryPolicy]

/-- Full all-dimension uniform scalar upper bound, with one fixed source
policy for all unknown objectives compatible with each public domain. -/
theorem uniform_scalar_upper (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (dx dy : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
      (hL : 0 < L) (hD : 0 < D)
      (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
      (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
      (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
      (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
      (epsilon : ℝ) (hepsilon : 0 < epsilon),
      ∃ N : ℕ, ∃ A : DeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarUpperCost p C L D epsilon ∧
        ScalarResidualPolicySucceeds L D epsilon X Y A := by
  obtain ⟨C0, hC0, hupper⟩ := uniform_scalar_upper_positive_dimension p hp
  let C : ℝ := max C0 1
  have hC : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  by_cases hdim : 0 < dx + dy
  · obtain ⟨N, A, hcost, hsuc⟩ :=
      hupper dx dy L D X Y hL hD hdim hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
    exact ⟨N, A, hcost.trans (scalar_upper_cost_mono_constant (le_max_left _ _) hL hD hepsilon), hsuc⟩
  · refine ⟨1, oneQueryPolicy z0 hz0, ?_, ?_⟩
    · have hge : C ≤ scalarUpperCost p C L D epsilon :=
        scalar_upper_cost_ge_constant hC.le hL hD hepsilon
      have h1 : (1 : ℝ) ≤ C := le_max_right C0 1
      simpa using h1.trans hge
    · intro phi hadm
      rw [one_query_policy_run]
      have hF : scalarSaddleOperator phi z0 = 0 := by
        ext i
        cases i with
        | inl j => have := j.2; omega
        | inr j => have := j.2; omega
      have hnormal : (0 : SaddleSpace dx dy) ∈ MinimaxAudit.normalCone (productDomain X Y) z0 := by
        intro z hz
        simp
      have hzero : (0 : SaddleSpace dx dy) ∈ normalCorrections
          (productDomain X Y) (scalarSaddleOperator phi) z0 := by
        exact ⟨0, hnormal, by simp [hF]⟩
      have hres : auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) z0 = 0 :=
        Metric.infDist_zero_of_mem hzero
      exact ⟨by simpa only [hres] using hepsilon.le,
        0, hnormal, by simpa only [hF, add_zero, norm_zero] using hepsilon.le⟩

/-- The policy really queried its saved output: this is a complete genuine
scalar-jet run, including the value/derivative response at that point. -/
def HasEvaluatedOutput {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (A : DeterministicScalarPolicy p dx dy N X Y) (phi : SaddleSpace dx dy → ℝ) : Prop :=
  let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
  ∃ h : ScalarHistory p dx dy, h.length ≤ N ∧
    EvaluatedPolicy.ScalarListRun A (exactScalarJet p phi) h output ∧
    (output, exactScalarJet p phi output) ∈ h

/-- One extra endpoint query is absorbed by increasing only the p-dependent
constant. The policy is fixed before the unknown objective is quantified. -/
theorem uniform_evaluated_scalar_upper (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (dx dy : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
      (hL : 0 < L) (hD : 0 < D)
      (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
      (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
      (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
      (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
      (epsilon : ℝ) (hepsilon : 0 < epsilon),
      ∃ N : ℕ, ∃ A : DeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarUpperCost p C L D epsilon ∧
        ScalarResidualPolicySucceeds L D epsilon X Y A ∧
        ∀ phi, AdmissibleScalar p L D X Y phi → HasEvaluatedOutput A phi := by
  obtain ⟨C0, hC0, hupper⟩ := uniform_scalar_upper p hp
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  obtain ⟨N, A, hcost, hsuc⟩ :=
    hupper dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  refine ⟨N + 1, EvaluatedPolicy.evaluatedPolicy A, ?_, ?_, ?_⟩
  · have h1 := scalar_upper_cost_ge_constant (p := p) (C := 1) zero_le_one hL hD hepsilon
    have hadd : scalarUpperCost p (C0 + 1) L D epsilon =
        scalarUpperCost p C0 L D epsilon + scalarUpperCost p 1 L D epsilon := by
      unfold scalarUpperCost
      ring
    rw [hadd]
    push_cast
    linarith
  · intro phi hadm
    have hout := (EvaluatedPolicy.evaluated_policy_preserves_output A (exactScalarJet p phi)).1
    change auditedTangentResidual _ _ _ ≤ epsilon ∧ _
    rw [hout]
    exact hsuc phi hadm
  · intro phi hadm
    exact (EvaluatedPolicy.evaluated_policy_preserves_output A (exactScalarJet p phi)).2

/-- The source gap display uses Q=L D^(p+1)/epsilon. -/
def scalarGapUpperCost (p : ℕ) (C L D epsilon : ℝ) : ℝ :=
  C * (1 + (L * D ^ (p + 1) / epsilon) ^ (2 / (3 * p - 1 : ℝ))) *
    (1 + Real.log (3 + L * D ^ (p + 1) / epsilon)) ^ (6 * (p - 1))

theorem scalar_upper_gap_cost {p : ℕ} {C L D epsilon : ℝ} (hD : D ≠ 0) :
    scalarUpperCost p C L D (epsilon / D) = scalarGapUpperCost p C L D epsilon := by
  have heq : L * D ^ p / (epsilon / D) = L * D ^ (p + 1) / epsilon := by
    rw [div_div_eq_mul_div, pow_succ]
    ring
  simp only [scalarUpperCost, scalarGapUpperCost, heq]

/-- Extract the saddle-operator value from the first derivative in one
complete scalar answer, with no additional objective call. -/
def scalarJetOperatorValue {p dx dy : ℕ} (hp : 0 < p)
    (J : ScalarJet p (SaddleSpace dx dy)) : SaddleSpace dx dy :=
  scalarToSaddleTensor (euclideanSaddleSign dx dy) (J ⟨1, by omega⟩) (fun i => Fin.elim0 i)

theorem scalar_jet_operator_value_exact {p dx dy : ℕ} (hp : 0 < p)
    (phi : SaddleSpace dx dy → ℝ) (z : SaddleSpace dx dy) :
    scalarJetOperatorValue hp (exactScalarJet p phi z) = scalarSaddleOperator phi z := by
  unfold scalarJetOperatorValue exactScalarJet
  rw [← scalar_jet_to_saddle_jet (euclideanSaddleSign dx dy) phi 0 z]
  simp only [iteratedFDeriv_zero_apply, Function.comp_apply, scalarSaddleOperator]

/-- A total public certificate readout on arbitrary scalar answers. It
selects a qualifying normal when one exists; genuine successful endpoint
answers always enter that branch. This uses known-domain computation only. -/
def normalReadout {p dx dy : ℕ} (hp : 0 < p)
    (X : Set (Primal dx)) (Y : Set (Dual dy)) (epsilon : ℝ)
    (z : SaddleSpace dx dy) (J : ScalarJet p (SaddleSpace dx dy)) : SaddleSpace dx dy := by
  classical
  exact if hn : ∃ n, n ∈ MinimaxAudit.normalCone (productDomain X Y) z ∧
      ‖scalarJetOperatorValue hp J + n‖ ≤ epsilon then Classical.choose hn else 0

theorem normal_readout_valid {p dx dy : ℕ} (hp : 0 < p)
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {epsilon : ℝ}
    (phi : SaddleSpace dx dy → ℝ) (z : SaddleSpace dx dy)
    (hn : ∃ n, n ∈ MinimaxAudit.normalCone (productDomain X Y) z ∧
      ‖scalarSaddleOperator phi z + n‖ ≤ epsilon) :
    normalReadout hp X Y epsilon z (exactScalarJet p phi z) ∈
        MinimaxAudit.normalCone (productDomain X Y) z ∧
      ‖scalarSaddleOperator phi z + normalReadout hp X Y epsilon z (exactScalarJet p phi z)‖ ≤ epsilon := by
  have hex : ∃ n, n ∈ MinimaxAudit.normalCone (productDomain X Y) z ∧
      ‖scalarJetOperatorValue hp (exactScalarJet p phi z) + n‖ ≤ epsilon := by
    simpa only [scalar_jet_operator_value_exact] using hn
  unfold normalReadout
  rw [dif_pos hex]
  simpa only [scalar_jet_operator_value_exact] using Classical.choose_spec hex

/-- Complete source `prop:upper`: a uniform evaluated scalar policy with
same-point true normal certificate and exact displayed query cost, and a
separate evaluated policy for the requested max/min gap tolerance. Both
policies are selected from public data before any unknown objective. -/
theorem prop_upper_source (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (dx dy : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
      (hL : 0 < L) (hD : 0 < D)
      (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
      (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
      (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
      (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
      (epsilon : ℝ) (hepsilon : 0 < epsilon),
      (∃ N : ℕ, ∃ A : DeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarUpperCost p C L D epsilon ∧
        ∀ phi, AdmissibleScalar p L D X Y phi →
          let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
          output ∈ productDomain X Y ∧ HasEvaluatedOutput A phi ∧
          auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) output ≤ epsilon ∧
          let normal := normalReadout (by omega : 0 < p) X Y epsilon output (exactScalarJet p phi output)
          normal ∈ MinimaxAudit.normalCone (productDomain X Y) output ∧
            ‖scalarSaddleOperator phi output + normal‖ ≤ epsilon) ∧
      (∃ N : ℕ, ∃ A : DeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarGapUpperCost p C L D epsilon ∧
        ∀ phi, AdmissibleScalar p L D X Y phi →
          let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
          output ∈ productDomain X Y ∧ HasEvaluatedOutput A phi ∧
          sSup ((fun v => phi (joinBlocks (primalBlock output) v)) '' Y) -
            sInf ((fun u => phi (joinBlocks u (dualBlock output))) '' X) ≤ epsilon) := by
  obtain ⟨C, hC, hupper⟩ := uniform_evaluated_scalar_upper p hp
  refine ⟨C, hC, ?_⟩
  intro dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  constructor
  · obtain ⟨N, A, hcost, hsuc, heval⟩ :=
      hupper dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
    refine ⟨N, A, hcost, ?_⟩
    intro phi hadm
    refine ⟨Deterministic.runScalarPolicy_feasible A _ N [], heval phi hadm, (hsuc phi hadm).1, ?_⟩
    exact normal_readout_valid (by omega) phi _ (hsuc phi hadm).2
  · obtain ⟨N, A, hcost, hsuc, heval⟩ :=
      hupper dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0
        (epsilon / D) (div_pos hepsilon hD)
    refine ⟨N, A, ?_, ?_⟩
    · simpa only [scalar_upper_gap_cost hD.ne'] using hcost
    · intro phi hadm
      have hz := Deterministic.runScalarPolicy_feasible A (exactScalarJet p phi) N []
      refine ⟨hz, heval phi hadm, ?_⟩
      have hgap := admissible_maxmin_gap_le_diameter_tangent hadm hz
      have hres := (hsuc phi hadm).1
      have hmul := mul_le_mul_of_nonneg_left hres hD.le
      have heq : D * (epsilon / D) = epsilon := by field_simp
      exact hgap.trans (heq ▸ hmul)

end
end MinimaxAudit.ScalarUpper
