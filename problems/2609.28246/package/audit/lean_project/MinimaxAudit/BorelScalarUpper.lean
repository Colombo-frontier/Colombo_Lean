import MinimaxAudit.BorelScalarUpperCore
import MinimaxAudit.BorelEvaluatedPolicy

open Set MeasureTheory
namespace MinimaxAudit.BorelScalarUpper
open VIReference.Pilot ScalarUpper BorelHistory
attribute [local instance] BorelStoppingPolicy.seedMeasurable
noncomputable section
variable {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

theorem uniform_borel_scalar_upper_positive_dimension (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (dx dy : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
      (hL : 0 < L) (hD : 0 < D) (hdim : 0 < dx + dy)
      (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
      (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
      (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
      (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
      (epsilon : ℝ) (hepsilon : 0 < epsilon),
      ∃ N : ℕ, ∃ A : BorelDeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarUpperCost p C L D epsilon ∧
        ∀ (phi : SaddleSpace dx dy → ℝ), AdmissibleScalar p L D X Y phi →
          let output := Deterministic.runScalarPolicy A.policy (exactScalarJet p phi) N []
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
  have hmeas := compileScalarPolicy_borel P seed center convertAnswer
    (scalarJetToSymmetricOperatorJet_measurable p dx dy)
    (ScalarVI.product_domain_compact hcX hcY).isClosed.measurableSet
  let A : BorelDeterministicScalarPolicy p dx dy call.cap X Y :=
    ⟨compileScalarPolicy P seed center convertAnswer, hmeas.1, hmeas.2⟩
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
        (Deterministic.runScalarPolicy A.policy (exactScalarJet p phi) call.cap []) ≤ epsilon ∧ _
    have hout' : Deterministic.runScalarPolicy A.policy (exactScalarJet p phi) call.cap [] = cert.point.1 := hout
    rw [hout']
    constructor
    · have hres := cert.tangentResidual_le data F epsilon hcert
      rwa [ScalarVI.tangent_residual_eq_source data rfl F cert.point.1] at hres
    · exact ⟨cert.normal, hcert.1, by simpa only [hcert.2.1] using hcert.2.2⟩


/-- The actual one-query zero-dimensional policy is Borel on every history. -/
def oneQueryBorelPolicy (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y) :
    BorelDeterministicScalarPolicy p dx dy 1 X Y where
  policy := oneQueryPolicy z0 hz0
  measurable_query := by
    classical
    apply (measurable_history_iff _).2
    intro n
    by_cases hn : n = 0
    · subst n
      simpa [oneQueryPolicy] using (measurable_const : Measurable
        (fun _ : Fin 0 → Entry p dx dy => (some z0 : Option (SaddleSpace dx dy))))
    · have hne : ∀ v : Fin n → Entry p dx dy, List.ofFn v ≠ [] := by
        intro v hv
        have := congrArg List.length hv
        simp only [List.length_ofFn, List.length_nil] at this
        contradiction
      simpa [oneQueryPolicy, hne] using (measurable_const : Measurable
        (fun _ : Fin n → Entry p dx dy => (none : Option (SaddleSpace dx dy))))
  measurable_output := measurable_const

theorem uniform_borel_scalar_upper (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (dx dy : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
      (hL : 0 < L) (hD : 0 < D)
      (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
      (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
      (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
      (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
      (epsilon : ℝ) (hepsilon : 0 < epsilon),
      ∃ N : ℕ, ∃ A : BorelDeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarUpperCost p C L D epsilon ∧
        ScalarResidualPolicySucceeds L D epsilon X Y A.policy := by
  obtain ⟨C0, hC0, hupper⟩ := uniform_borel_scalar_upper_positive_dimension p hp
  let C : ℝ := max C0 1
  have hC : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  by_cases hdim : 0 < dx + dy
  · obtain ⟨N, A, hcost, hsuc⟩ :=
      hupper dx dy L D X Y hL hD hdim hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
    exact ⟨N, A, hcost.trans (scalar_upper_cost_mono_constant (le_max_left _ _) hL hD hepsilon), hsuc⟩
  · refine ⟨1, oneQueryBorelPolicy z0 hz0, ?_, ?_⟩
    · have hge : C ≤ scalarUpperCost p C L D epsilon :=
        scalar_upper_cost_ge_constant hC.le hL hD hepsilon
      have h1 : (1 : ℝ) ≤ C := le_max_right C0 1
      simpa using h1.trans hge
    · intro phi hadm
      simp only [oneQueryBorelPolicy]
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


theorem uniform_evaluated_borel_scalar_upper (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (dx dy : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
      (hL : 0 < L) (hD : 0 < D)
      (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
      (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
      (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
      (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
      (epsilon : ℝ) (hepsilon : 0 < epsilon),
      ∃ N : ℕ, ∃ A : BorelDeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarUpperCost p C L D epsilon ∧
        ScalarResidualPolicySucceeds L D epsilon X Y A.policy ∧
        ∀ phi, AdmissibleScalar p L D X Y phi → HasEvaluatedOutput A.policy phi := by
  obtain ⟨C0, hC0, hupper⟩ := uniform_borel_scalar_upper p hp
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  obtain ⟨N, A, hcost, hsuc⟩ :=
    hupper dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  refine ⟨N + 1, BorelEvaluatedPolicy.evaluatedPolicy A ⟨z0, hz0⟩, ?_, ?_, ?_⟩
  · have h1 := scalar_upper_cost_ge_constant (p := p) (C := 1) zero_le_one hL hD hepsilon
    have hadd : scalarUpperCost p (C0 + 1) L D epsilon =
        scalarUpperCost p C0 L D epsilon + scalarUpperCost p 1 L D epsilon := by
      unfold scalarUpperCost
      ring
    rw [hadd]
    push_cast
    linarith
  · intro phi hadm
    simp only [BorelEvaluatedPolicy.evaluatedPolicy]
    have hout := (EvaluatedPolicy.evaluated_policy_preserves_output A.policy (exactScalarJet p phi)).1
    change auditedTangentResidual _ _ _ ≤ epsilon ∧ _
    rw [hout]
    exact hsuc phi hadm
  · intro phi hadm
    exact (EvaluatedPolicy.evaluated_policy_preserves_output A.policy (exactScalarJet p phi)).2


theorem prop_upper_borel_source (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (dx dy : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
      (hL : 0 < L) (hD : 0 < D)
      (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
      (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
      (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
      (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y)
      (epsilon : ℝ) (hepsilon : 0 < epsilon),
      (∃ N : ℕ, ∃ A : BorelDeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarUpperCost p C L D epsilon ∧
        ∀ phi, AdmissibleScalar p L D X Y phi →
          let output := Deterministic.runScalarPolicy A.policy (exactScalarJet p phi) N []
          output ∈ productDomain X Y ∧ HasEvaluatedOutput A.policy phi ∧
          auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) output ≤ epsilon ∧
          let normal := normalReadout (by omega : 0 < p) X Y epsilon output (exactScalarJet p phi output)
          normal ∈ MinimaxAudit.normalCone (productDomain X Y) output ∧
            ‖scalarSaddleOperator phi output + normal‖ ≤ epsilon) ∧
      (∃ N : ℕ, ∃ A : BorelDeterministicScalarPolicy p dx dy N X Y,
        (N : ℝ) ≤ scalarGapUpperCost p C L D epsilon ∧
        ∀ phi, AdmissibleScalar p L D X Y phi →
          let output := Deterministic.runScalarPolicy A.policy (exactScalarJet p phi) N []
          output ∈ productDomain X Y ∧ HasEvaluatedOutput A.policy phi ∧
          sSup ((fun v => phi (joinBlocks (primalBlock output) v)) '' Y) -
            sInf ((fun u => phi (joinBlocks u (dualBlock output))) '' X) ≤ epsilon) := by
  obtain ⟨C, hC, hupper⟩ := uniform_evaluated_borel_scalar_upper p hp
  refine ⟨C, hC, ?_⟩
  intro dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
  constructor
  · obtain ⟨N, A, hcost, hsuc, heval⟩ :=
      hupper dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0 epsilon hepsilon
    refine ⟨N, A, hcost, ?_⟩
    intro phi hadm
    refine ⟨Deterministic.runScalarPolicy_feasible A.policy _ N [], heval phi hadm, (hsuc phi hadm).1, ?_⟩
    exact normal_readout_valid (by omega) phi _ (hsuc phi hadm).2
  · obtain ⟨N, A, hcost, hsuc, heval⟩ :=
      hupper dx dy L D X Y hL hD hneX hneY hcX hcY hvX hvY hdiam z0 hz0
        (epsilon / D) (div_pos hepsilon hD)
    refine ⟨N, A, ?_, ?_⟩
    · simpa only [scalar_upper_gap_cost hD.ne'] using hcost
    · intro phi hadm
      have hz := Deterministic.runScalarPolicy_feasible A.policy (exactScalarJet p phi) N []
      refine ⟨hz, heval phi hadm, ?_⟩
      have hgap := admissible_maxmin_gap_le_diameter_tangent hadm hz
      have hres := (hsuc phi hadm).1
      have hmul := mul_le_mul_of_nonneg_left hres hD.le
      have heq : D * (epsilon / D) = epsilon := by field_simp
      exact hgap.trans (heq ▸ hmul)

end
end MinimaxAudit.BorelScalarUpper
