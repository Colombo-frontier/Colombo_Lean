import LeanArticleAudit.Pilot.ApproxRecovery
import LeanArticleAudit.Pilot.UpperBaseSuccess

open Set
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def proxAffine (eta : ℝ) (center : E) : E → E :=
  fun w ↦ eta⁻¹ • (w - center)

theorem proxAffine_contDiff (eta : ℝ) (center : E) :
    ContDiff ℝ ⊤ (proxAffine eta center) := by
  exact (contDiff_id.sub contDiff_const).const_smul eta⁻¹

private theorem iteratedFDeriv_id_independent_prox
    (n : ℕ) (hn : 0 < n) (x y : E) :
    iteratedFDeriv ℝ n (id : E → E) x = iteratedFDeriv ℝ n (id : E → E) y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  cases n with
  | zero =>
      ext v
      simp [iteratedFDeriv_one_apply, fderiv_id]
  | succ n =>
      rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
      simp only [fderiv_id]
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)
        (ContinuousLinearMap.id ℝ E)]
      rfl

private theorem proxAffine_iteratedFDeriv_independent
    (eta : ℝ) (center : E) (n : ℕ) (hn : 0 < n) (x y : E) :
    iteratedFDeriv ℝ n (proxAffine eta center) x =
      iteratedFDeriv ℝ n (proxAffine eta center) y := by
  have hinner : ContDiff ℝ ⊤ (fun z : E ↦ z - center) :=
    contDiff_id.sub contDiff_const
  have hx : ContDiffAt ℝ n (fun z : E ↦ z - center) x :=
    hinner.contDiffAt.of_le le_top
  have hy : ContDiffAt ℝ n (fun z : E ↦ z - center) y :=
    hinner.contDiffAt.of_le le_top
  change iteratedFDeriv ℝ n (fun z : E ↦ eta⁻¹ • (z - center)) x =
    iteratedFDeriv ℝ n (fun z : E ↦ eta⁻¹ • (z - center)) y
  rw [iteratedFDeriv_const_smul_apply' hx, iteratedFDeriv_const_smul_apply' hy]
  congr 1
  rw [show (fun z : E ↦ z - center) =
      (id : E → E) - fun _ ↦ center by rfl]
  rw [iteratedFDeriv_sub_apply contDiff_id.contDiffAt contDiffAt_const,
    iteratedFDeriv_sub_apply contDiff_id.contDiffAt contDiffAt_const]
  rw [iteratedFDeriv_id_independent_prox n hn x y]
  have hconst : iteratedFDeriv ℝ n (fun _ : E ↦ center) = 0 :=
    iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn) center
  rw [congrFun hconst x, congrFun hconst y]
  change iteratedFDeriv ℝ n id y - 0 = iteratedFDeriv ℝ n id y - 0
  rfl

def proxAffineJet (p : ℕ) (eta : ℝ) (center point : E) :
    SymmetricExactJet E p :=
  exactSymmetricJetOf E p (proxAffine eta center) point (fun j σ ↦
    ContDiffAt.domDomCongr_iteratedFDeriv
      (proxAffine_contDiff eta center).contDiffAt σ)

def addSymmetricJetProx {p : ℕ}
    (first second : SymmetricExactJet E p) : SymmetricExactJet E p := fun j ↦
  ⟨(first j).1 + (second j).1, by
    intro σ
    ext v
    have hfirst := congrArg (fun f : E [×j.1]→L[ℝ] E ↦ f v) ((first j).2 σ)
    have hsecond := congrArg (fun f : E [×j.1]→L[ℝ] E ↦ f v) ((second j).2 σ)
    simpa [ContinuousMultilinearMap.domDomCongr_apply] using
      congrArg₂ (fun a b : E ↦ a + b) hfirst hsecond⟩

def proxJetAnswer (p : ℕ) (eta : ℝ) (center point : E)
    (base : SymmetricExactJet E p) : SymmetricExactJet E p :=
  addSymmetricJetProx base (proxAffineJet p eta center point)

theorem continuous_proxJetAnswer (p : ℕ) (eta : ℝ) (center point : E) :
    Continuous (proxJetAnswer p eta center point) := by
  unfold proxJetAnswer addSymmetricJetProx
  fun_prop

/-- The first-answer continuation of proximal model correction is a total
norm-Borel next-query rule on all ambient jets. -/
theorem proximal_model_query_normBorel (data : VIPublicData E)
    (eta : ℝ) (center : data.X) :
    @Measurable (SymmetricExactJet E data.p) data.X
      (upperJetBorelMeasurableSpace data.p)
      (upperFeasibleBorelMeasurableSpace data)
      (fun base ↦ (knownModelStep data center
        (proxJetAnswer data.p eta center.1 center.1 base)).1) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (SymmetricExactJet E data.p) :=
    upperJetBorelMeasurableSpace data.p
  letI : BorelSpace (SymmetricExactJet E data.p) := ⟨rfl⟩
  have hprox : Measurable
      (proxJetAnswer data.p eta center.1 center.1) :=
    (continuous_proxJetAnswer data.p eta center.1 center.1).measurable
  exact (measurable_borelKnownModelPoint_fixedCenter data center).comp hprox

private theorem admissible_contDiffAt_nat (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (x : E) (hx : x ∈ data.X) :
    ContDiffAt ℝ (data.p - 1 : ℕ) F x := by
  obtain ⟨U, hU, hXU, hreg⟩ := hF.regularity
  exact (hreg x (hXU hx)).contDiffAt (hU.mem_nhds (hXU hx))

theorem proxJetAnswer_exact (data : VIPublicData E) (F : E → E)
    (point : data.X) (base : SymmetricExactJet E data.p)
    (hbase : ∀ j : Fin data.p,
      (base j).1 = iteratedFDeriv ℝ j.1 F point.1)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (center : E)
    (j : Fin data.p) :
    ((proxJetAnswer data.p eta center point.1 base) j).1 =
      iteratedFDeriv ℝ j.1 (resolventOperator F eta center) point.1 := by
  rw [show resolventOperator F eta center = F + proxAffine eta center by rfl]
  rw [iteratedFDeriv_add_apply]
  · simp only [proxJetAnswer, addSymmetricJetProx, proxAffineJet,
      exactSymmetricJetOf]
    rw [hbase]
  · exact (admissible_contDiffAt_nat data F hF point.1 point.2).of_le (by
      exact_mod_cast Nat.le_pred_of_lt j.2)
  · exact (proxAffine_contDiff eta center).contDiffAt.of_le le_top

def proximalFeasibleOracle (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (center : E) :
    FeasibleExactSymmetricJetOracle data (resolventOperator F eta center) where
  answer point := proxJetAnswer data.p eta center point.1 (oracle.answer point)
  exact point j := proxJetAnswer_exact data F point (oracle.answer point)
    (oracle.exact point) hF eta center j

theorem resolventOperator_admissible (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (eta : ℝ) (heta : 0 < eta)
    (center : E) : IsAdmissibleOperator data (resolventOperator F eta center) := by
  constructor
  · obtain ⟨U, hU, hXU, hreg⟩ := hF.regularity
    exact ⟨U, hU, hXU,
      hreg.add ((proxAffine_contDiff eta center).contDiffOn.of_le le_top)⟩
  · intro x hx y hy
    have hm := hF.monotone_on x hx y hy
    simp only [resolventOperator]
    rw [show (F x + eta⁻¹ • (x - center)) - (F y + eta⁻¹ • (y - center)) =
      (F x - F y) + eta⁻¹ • (x - y) by module,
      inner_add_left, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
    exact add_nonneg hm (mul_nonneg (inv_nonneg.mpr heta.le) (sq_nonneg _))
  · intro x hx y hy
    have hFx := admissible_contDiffAt_nat data F hF x hx
    have hFy := admissible_contDiffAt_nat data F hF y hy
    have hAx : ContDiffAt ℝ (data.p - 1 : ℕ)
        (proxAffine eta center) x :=
      (proxAffine_contDiff eta center).contDiffAt.of_le le_top
    have hAy : ContDiffAt ℝ (data.p - 1 : ℕ)
        (proxAffine eta center) y :=
      (proxAffine_contDiff eta center).contDiffAt.of_le le_top
    rw [show resolventOperator F eta center = F + proxAffine eta center by rfl]
    rw [iteratedFDeriv_add_apply hFx hAx, iteratedFDeriv_add_apply hFy hAy]
    rw [proxAffine_iteratedFDeriv_independent eta center (data.p - 1)
      (Nat.sub_pos_of_lt (lt_of_lt_of_le (by omega : 1 < 2) data.p_ge_two)) x y]
    simpa only [add_sub_add_right_eq_sub] using
      hF.top_derivative_lipschitz x hx y hy

private theorem admissible_continuousOn_prox (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) : ContinuousOn F data.X := by
  intro x hx
  exact (admissible_contDiffAt_nat data F hF x hx).continuousAt.continuousWithinAt

private theorem admissible_locallyLipschitzOn_prox
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) : LocallyLipschitzOn data.X F := by
  apply ContDiffOn.locallyLipschitzOn data.X_convex
  intro x hx
  have hp := data.p_ge_two
  exact (admissible_contDiffAt_nat data F hF x hx).of_le (by
    exact_mod_cast (show 1 ≤ data.p - 1 by omega)) |>.contDiffWithinAt

/-- The model correction specialized to the proximal operator.  Each derived
jet is computed from one original answer, and the second original query
evaluates the returned tangent certificate. -/
noncomputable def proximalModelCorrectionProgram (data : VIPublicData E)
    (eta : ℝ) (center : data.X) :
    ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data) :=
  .query center (fun baseCenter ↦
    let proxJet := proxJetAnswer data.p eta center.1 center.1 baseCenter
    let yn := knownModelStep data center proxJet
    .query yn.1 (fun baseY ↦
      .halt (some {
        point := yn.1
        normal := yn.2
        value := symmetricJetValue data baseY })))

/-- Operational final clause of `prop:approx-recovery`: the actual proximal
model correction consumes exactly two original oracle queries and returns a
verified original-operator tangent certificate with the source bound. -/
theorem proximalModelCorrection_twoQueries
    (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (hF : IsAdmissibleOperator data F) (center : data.X)
    (eta : ℝ) (heta : 0 < eta) :
    let yStar := resolventPoint data.X data.X_nonempty data.X_compact
      data.X_convex F (admissible_continuousOn_prox data F hF)
        (admissible_locallyLipschitzOn_prox data F hF) hF.monotone_on
          eta heta center.1
    let Rz := ‖center.1 - yStar‖
    let delta := correctionConstant data.p * data.Lp * Rz ^ data.p
    ∃ cert, ExactJetProgram.Evaluates oracle.answer
        (proximalModelCorrectionProgram data eta center) 2 (some cert) ∧
      cert.IsVerifiedFor data F (Rz / eta + 2 * delta) := by
  dsimp only
  let hcont := admissible_continuousOn_prox data F hF
  let hloc := admissible_locallyLipschitzOn_prox data F hF
  let yStar := resolventPoint data.X data.X_nonempty data.X_compact
    data.X_convex F hcont hloc hF.monotone_on eta heta center.1
  let Rz := ‖center.1 - yStar‖
  let delta := correctionConstant data.p * data.Lp * Rz ^ data.p
  let G := resolventOperator F eta center.1
  let proxOracle := proximalFeasibleOracle data F oracle hF eta center.1
  have hG : IsAdmissibleOperator data G :=
    resolventOperator_admissible data F hF eta heta center.1
  have hspec : IsKnownModelStep data center (proxOracle.answer center)
      (knownModelStep data center (proxOracle.answer center)) :=
    knownModelStep_genuine_spec data G hG proxOracle center
  let yn := knownModelStep data center (proxOracle.answer center)
  let y : E := yn.1.1
  let n : E := yn.2
  have hyStar : IsVISolution data G yStar := by
    exact resolventPoint_spec data.X data.X_nonempty data.X_compact data.X_convex
      F hcont hloc hF.monotone_on eta heta center.1
  have hGbound : ‖G y + n‖ ≤ delta := by
    exact knownModelStep_correction_bound data G proxOracle hG center Rz yStar
      hyStar (le_refl Rz) hspec
  have hdelta : 0 ≤ delta := by
    have hc : 0 ≤ correctionConstant data.p := by
      unfold correctionConstant
      positivity
    exact mul_nonneg (mul_nonneg hc data.Lp_pos.le) (pow_nonneg (norm_nonneg _) _)
  have hy : y ∈ data.X := yn.1.2
  have hn : n ∈ normalCone data.X y := hspec.1
  have hcertReg : ‖F y + n + eta⁻¹ • (y - center.1)‖ ≤ delta := by
    rw [show F y + n + eta⁻¹ • (y - center.1) =
      G y + n by simp [G, resolventOperator]; abel]
    exact hGbound
  have happrox := approximateProximal_core data F hcont hloc hF.monotone_on
    center.1 y center.2 hy n hn eta delta heta hdelta hcertReg
  have hdist : ‖y - yStar‖ ≤ eta * delta := by
    simpa [yStar] using happrox.1
  have hyz : ‖y - center.1‖ ≤ Rz + eta * delta := by
    rw [show y - center.1 = (y - yStar) + (yStar - center.1) by abel]
    calc
      ‖(y - yStar) + (yStar - center.1)‖ ≤
          ‖y - yStar‖ + ‖yStar - center.1‖ := norm_add_le _ _
      _ ≤ eta * delta + Rz := by
        have hrev : ‖yStar - center.1‖ = Rz := by simp [Rz, norm_sub_rev]
        rw [hrev]
        exact add_le_add hdist (le_refl Rz)
      _ = Rz + eta * delta := add_comm _ _
  have hinv : 0 ≤ eta⁻¹ := (inv_pos.mpr heta).le
  have hFbound : ‖F y + n‖ ≤ Rz / eta + 2 * delta := by
    have hdecomp : F y + n =
        (F y + n + eta⁻¹ • (y - center.1)) - eta⁻¹ • (y - center.1) := by abel
    rw [hdecomp]
    calc
      ‖(F y + n + eta⁻¹ • (y - center.1)) -
          eta⁻¹ • (y - center.1)‖ ≤
          ‖F y + n + eta⁻¹ • (y - center.1)‖ +
            ‖eta⁻¹ • (y - center.1)‖ := norm_sub_le _ _
      _ ≤ delta + eta⁻¹ * (Rz + eta * delta) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
        gcongr
      _ = Rz / eta + 2 * delta := by
        field_simp [heta.ne']
        ring
  let cert : EvaluatedNormalCertificate data := {
    point := yn.1
    normal := n
    value := symmetricJetValue data (oracle.answer yn.1) }
  refine ⟨cert, ?_, ?_⟩
  · simp only [proximalModelCorrectionProgram]
    apply ExactJetProgram.Evaluates.query
    change ExactJetProgram.Evaluates oracle.answer
      (.query yn.1 fun baseY ↦ .halt (some {
        point := yn.1, normal := yn.2, value := symmetricJetValue data baseY }))
      1 (some cert)
    exact .query _ _ _ _ (.halt _)
  · refine ⟨hn, ?_, ?_⟩
    · exact symmetricJetValue_feasible_exact data F oracle yn.1
    · change ‖symmetricJetValue data (oracle.answer yn.1) + n‖ ≤ _
      rw [symmetricJetValue_feasible_exact data F oracle yn.1]
      exact hFbound

/-- Source-facing executable third clause of `prop:approx-recovery`.  The
program itself receives neither the analysis-only resolvent radius `Rz` nor
the derived tolerance `delta`; nevertheless, on every admissible exact oracle
it consumes exactly two original-operator queries and returns the claimed
certificate. -/
def ApproxRecoveryModelCorrectionClaim : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F),
    ∀ (hF : IsAdmissibleOperator data F),
    ∀ (center : data.X) (eta : ℝ), ∀ heta : 0 < eta,
    let yStar := resolventPoint data.X data.X_nonempty data.X_compact
      data.X_convex F (admissible_continuousOn_prox data F hF)
        (admissible_locallyLipschitzOn_prox data F hF) hF.monotone_on
          eta heta center.1
    let Rz := ‖center.1 - yStar‖
    let delta := correctionConstant data.p * data.Lp * Rz ^ data.p
    ∃ cert, ExactJetProgram.Evaluates oracle.answer
        (proximalModelCorrectionProgram data eta center) 2 (some cert) ∧
      cert.IsVerifiedFor data F (Rz / eta + 2 * delta)

theorem approxRecoveryModelCorrectionClaim_proof :
    ApproxRecoveryModelCorrectionClaim.{u} := by
  intro E _ _ _ data F oracle hF center eta heta
  exact proximalModelCorrection_twoQueries data F oracle hF center eta heta

/-- Complete source-facing `prop:approx-recovery`: the two analytic recovery
inequalities and the executable two-query model-correction specialization. -/
def ApproxRecoveryClaim : Prop :=
  ApproximateProximalCoreClaim.{u} ∧ ApproxRecoveryModelCorrectionClaim.{u}

theorem approxRecoveryClaim_proof : ApproxRecoveryClaim.{u} :=
  ⟨approximateProximalCoreClaim_proof, approxRecoveryModelCorrectionClaim_proof⟩

end
end LeanArticleAudit.Pilot
