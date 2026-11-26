import LeanArticleAudit.Pilot.UpperHalvingExecution

open Set
open Filter
open scoped RealInnerProductSpace Topology

namespace LeanArticleAudit.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : DecidableEq E := Classical.decEq E

theorem symmetricJetValue_feasible_exact (data : VIPublicData E)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (x : data.X) : symmetricJetValue data (oracle.answer x) = F x.1 := by
  rw [symmetricJetValue, oracle.exact]
  simp [iteratedFDeriv_zero_eq_comp]

theorem taylorModelFromJet_feasible_exact (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F) (x : data.X) (y : E) :
    taylorModelFromJet data x.1 (oracle.answer x) y =
      taylorModel data.p F x.1 y := by
  rw [taylorModelFromJet, taylorModel]
  simp_rw [oracle.exact]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    (Nat.factorial j : ℝ)⁻¹ • iteratedFDeriv ℝ j F x.1 (fun _ ↦ y - x.1)) data.p

/-- One ordinary branch of the executable Halve program satisfies the exact
source TEG energy inequality. This is the semantic bridge from an oracle
answer and model-step witness to `lem:teg-energy`. -/
theorem knownModelStep_teg_energy
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (x : data.X)
    (hspec : IsKnownModelStep data x (oracle.answer x)
      (knownModelStep data x (oracle.answer x)))
    (hxy : (knownModelStep data x (oracle.answer x)).1.1 ≠ x.1)
    (u : E) (hu : u ∈ data.X) :
    let yn := knownModelStep data x (oracle.answer x)
    let y := yn.1.1
    let lambda := 1 / ((tensorBetaCoefficient data.p * data.Lp) *
      ‖y - x.1‖ ^ (data.p - 1))
    let xp := compactConvexProjection data.X data.X_nonempty data.X_compact
      data.X_convex (x.1 - lambda • G y)
    2 * lambda * inner ℝ (G y) (y - u) ≤
      ‖x.1 - u‖ ^ 2 - ‖xp - u‖ ^ 2 - (3 / 4 : ℝ) * ‖y - x.1‖ ^ 2 := by
  dsimp only
  let yn := knownModelStep data x (oracle.answer x)
  let y : E := yn.1.1
  let n : E := yn.2
  let err : E := G y - taylorModel data.p G x.1 y
  let lambda : ℝ := 1 / ((tensorBetaCoefficient data.p * data.Lp) *
    ‖y - x.1‖ ^ (data.p - 1))
  let xp := compactConvexProjection data.X data.X_nonempty data.X_compact
    data.X_convex (x.1 - lambda • G y)
  have hy : y ∈ data.X := yn.1.2
  have hn : n ∈ normalCone data.X y := hspec.1
  have hmodel : G y + n = err -
      ((2 * (data.p : ℝ) / data.p.factorial) * data.Lp *
        ‖y - x.1‖ ^ (data.p - 1)) • (y - x.1) := by
    have heq := hspec.2
    rw [taylorModelFromJet_feasible_exact data G oracle x y] at heq
    dsimp [yn, y, n, err] at *
    unfold tensorBetaCoefficient at heq
    calc
      G y + n = (G y - taylorModel data.p G x.1 y) +
          (taylorModel data.p G x.1 y +
            ((2 * (data.p : ℝ) / data.p.factorial) * data.Lp *
              ‖y - x.1‖ ^ (data.p - 1)) • (y - x.1) + n) -
          ((2 * (data.p : ℝ) / data.p.factorial) * data.Lp *
            ‖y - x.1‖ ^ (data.p - 1)) • (y - x.1) := by module
      _ = (G y - taylorModel data.p G x.1 y) -
          ((2 * (data.p : ℝ) / data.p.factorial) * data.Lp *
            ‖y - x.1‖ ^ (data.p - 1)) • (y - x.1) := by rw [heq]; module
  obtain ⟨U, hU, hXU, hreg⟩ := hG.regularity
  have htaylor : ‖err‖ ≤ data.Lp / data.p.factorial * ‖y - x.1‖ ^ data.p := by
    have ht := taylorRemainderClaim_proof data.p data.Lp data.X U G
      data.p_ge_two data.Lp_pos.le hU hXU data.X_convex hreg
      hG.top_derivative_lipschitz x x.2 y hy
    exact ht.1
  have hxp : xp ∈ data.X := compactConvexProjection_mem data.X
    data.X_nonempty data.X_compact data.X_convex _
  have hproj : inner ℝ (x.1 - lambda • G y - xp) (u - xp) ≤ 0 :=
    compactConvexProjection_variational data.X data.X_nonempty data.X_compact
      data.X_convex (x.1 - lambda • G y) u hu
  exact lem_teg_energy data.X G data.p data.p_ge_two data.Lp data.Lp_pos
    x.1 y xp u n err hxy hy hxp hu hn hmodel htaylor (by
      simpa [lambda, tensorBetaCoefficient] using hproj)

/-- A full non-early execution of the exact Halve recurrence has the claimed
distance guarantee. The hypotheses are precisely the states and transition
equalities extracted from the executable loop, not an energy certificate. -/
theorem halving_full_schedule_halves
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (mu r : ℝ) (hmu : 0 < mu) (hr : 0 < r)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (x : ℕ → data.X)
    (hx0 : ‖(x 0).1 - zStar‖ ≤ r)
    (hspec : ∀ i < halvingIterationCount data.p data.Lp r mu,
      IsKnownModelStep data (x i) (oracle.answer (x i))
        (knownModelStep data (x i) (oracle.answer (x i))))
    (hnone : ∀ i < halvingIterationCount data.p data.Lp r mu,
      (knownModelStep data (x i) (oracle.answer (x i))).1.1 ≠ (x i).1)
    (hxnext : ∀ i < halvingIterationCount data.p data.Lp r mu,
      (x (i + 1)).1 = compactConvexProjection data.X data.X_nonempty
        data.X_compact data.X_convex
        ((x i).1 - (1 / ((tensorBetaCoefficient data.p * data.Lp) *
          ‖(knownModelStep data (x i) (oracle.answer (x i))).1.1 - (x i).1‖ ^
            (data.p - 1))) •
          G (knownModelStep data (x i) (oracle.answer (x i))).1.1)) :
    let T := halvingIterationCount data.p data.Lp r mu
    let y : ℕ → E := fun i ↦
      (knownModelStep data (x i) (oracle.answer (x i))).1.1
    let s : ℕ → E := fun i ↦ y i - (x i).1
    let lambda : ℕ → ℝ := fun i ↦
      1 / ((tensorBetaCoefficient data.p * data.Lp) * ‖s i‖ ^ (data.p - 1))
    let Lambda := ∑ i ∈ Finset.range T, lambda i
    let ybar := (1 / Lambda) • (∑ i ∈ Finset.range T, lambda i • y i)
    ybar ∈ data.X ∧ ‖ybar - zStar‖ ≤ r / 2 := by
  dsimp only
  let T := halvingIterationCount data.p data.Lp r mu
  let y : ℕ → E := fun i ↦
    (knownModelStep data (x i) (oracle.answer (x i))).1.1
  let s : ℕ → E := fun i ↦ y i - (x i).1
  let lambda : ℕ → ℝ := fun i ↦
    1 / ((tensorBetaCoefficient data.p * data.Lp) * ‖s i‖ ^ (data.p - 1))
  let Lambda := ∑ i ∈ Finset.range T, lambda i
  have hT : 0 < T := halvingIterationCount_pos _ _ _ _
  have hy : ∀ i < T, y i ∈ data.X := by
    intro i hi
    exact (knownModelStep data (x i) (oracle.answer (x i))).1.2
  have hsne : ∀ i < T, s i ≠ 0 := by
    intro i hi
    exact sub_ne_zero.mpr (hnone i hi)
  have hlambdaEq : ∀ i < T,
      lambda i = 1 / ((tensorBetaCoefficient data.p * data.Lp) *
        ‖s i‖ ^ (data.p - 1)) := by intro i hi; rfl
  have hlambda : ∀ i < T, 0 ≤ lambda i := by
    intro i hi
    dsimp [lambda]
    have hbeta : 0 < tensorBetaCoefficient data.p := by
      unfold tensorBetaCoefficient
      exact div_pos (mul_pos (by norm_num) (by exact_mod_cast
        (lt_of_lt_of_le (by omega : 0 < 2) data.p_ge_two))) (by positivity)
    have hspos : 0 < ‖s i‖ := norm_pos_iff.mpr (hsne i hi)
    exact (one_div_pos.mpr (mul_pos (mul_pos hbeta data.Lp_pos)
      (pow_pos hspos _))).le
  have hstrongSeq : ∀ i < T,
      mu * ‖y i - zStar‖ ^ 2 ≤ inner ℝ (G (y i)) (y i - zStar) := by
    intro i hi
    have hm := hstrong (y i) (hy i hi) zStar hz.1
    have hv := hz.2 (y i) (hy i hi)
    rw [inner_sub_left] at hm
    linarith
  have henergy : ∀ i < T,
      2 * lambda i * inner ℝ (G (y i)) (y i - zStar) ≤
        ‖(x i).1 - zStar‖ ^ 2 - ‖(x (i + 1)).1 - zStar‖ ^ 2 -
          (3 / 4 : ℝ) * ‖s i‖ ^ 2 := by
    intro i hi
    have he := knownModelStep_teg_energy data G oracle hG (x i)
      (hspec i hi) (hnone i hi) zStar hz.1
    dsimp only at he
    rw [← hxnext i hi] at he
    simpa [y, s, lambda] using he
  have hsum := tensorExtragradient_energy_sum T (fun i ↦ (x i).1) y s G lambda
    zStar mu r hmu.le hlambda hx0 hstrongSeq henergy
  have hsteps : (3 / 4 : ℝ) * (∑ i ∈ Finset.range T, ‖s i‖ ^ 2) ≤ r ^ 2 := by
    have hweighted : 0 ≤ 2 * mu *
        (∑ i ∈ Finset.range T, lambda i * ‖y i - zStar‖ ^ 2) := by
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range T,
          lambda i * ‖y i - zStar‖ ^ 2 := by
        exact Finset.sum_nonneg fun i hi ↦
          mul_nonneg (hlambda i (Finset.mem_range.mp hi)) (sq_nonneg _)
      positivity
    linarith
  have hbeta : 0 < tensorBetaCoefficient data.p * data.Lp := by
    unfold tensorBetaCoefficient
    exact mul_pos (div_pos (mul_pos (by norm_num) (by exact_mod_cast
      (lt_of_lt_of_le (by omega : 0 < 2) data.p_ge_two))) (by positivity)) data.Lp_pos
  have hpone : 1 ≤ data.p := le_trans (by omega : 1 ≤ 2) data.p_ge_two
  have hraw := halving_lambda_sum_lower_raw data.p T hpone hT s r
    (tensorBetaCoefficient data.p * data.Lp) hr hbeta hsne lambda hlambdaEq hsteps
  rw [mul_assoc, halving_raw_constant_normalize data.p hpone T hT r hr] at hraw
  have hLambdaLower : 2 / mu ≤ Lambda :=
    halving_count_forces_lambda_lower data.p data.p_ge_two data.Lp r mu Lambda
      data.Lp_pos hr hmu (by
        dsimp [T, Lambda]
        convert hraw using 1 <;> ring)
  exact weighted_average_halves data.X data.X_convex T y s lambda zStar mu r Lambda
    hmu hr.le hy hlambda rfl hLambdaLower hsum

/-- The final correction is an actual two-query program.  It constructs its
candidate solely from the first exact jet, then evaluates the operator at that
candidate and returns it only after both public certificate checks pass. -/
noncomputable def correctionProgram (data : VIPublicData E) (center : data.X)
    (delta : ℝ) : ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data) := by
  classical
  exact .query center (fun jetx =>
    let yn := knownModelStep data center jetx
    .query yn.1 (fun jety =>
      let cert : EvaluatedNormalCertificate data := {
        point := yn.1
        normal := yn.2
        value := symmetricJetValue data jety }
      if hn : cert.normal ∈ normalCone data.X cert.point.1 then
        if hres : ‖cert.value + cert.normal‖ ≤ delta then
          .halt (some cert)
        else .halt none
      else .halt none))

theorem correctionProgram_no_false_success (data : VIPublicData E)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    (center : data.X) (delta : ℝ)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (heval : ExactJetProgram.Evaluates oracle.answer
      (correctionProgram data center delta) used (some cert)) :
    cert.IsVerifiedFor data F delta := by
  simp only [correctionProgram] at heval
  cases heval with
  | query _ _ used₁ _ hnext =>
      dsimp only at hnext
      cases hnext with
      | query point₂ next₂ used₂ result hhalt =>
          dsimp only at hhalt
          split at hhalt <;> rename_i hn
          · split at hhalt <;> rename_i hres
            · cases hhalt
              exact ⟨hn, symmetricJetValue_feasible_exact data F oracle _, hres⟩
            · cases hhalt
          · cases hhalt

/-- A finite base trial: run the requested number of source Halve calls and
then one genuinely evaluated correction.  Failure of any Halve is propagated. -/
noncomputable def baseTrialProgram (data : VIPublicData E) (mu delta : ℝ) :
    (halvings : ℕ) → (center : data.X) → (r : ℝ) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data)
  | 0, center, _ => correctionProgram data center delta
  | halvings + 1, center, r => by
      classical
      exact (halvingProgram data center mu r).bind (fun out =>
        if hmem : out.point ∈ data.X then
          baseTrialProgram data mu delta halvings ⟨out.point, hmem⟩ (r / 2)
        else .halt none)

theorem ExactJetProgram.evaluates_bind_some_right
    {X Answer A B : Type*} (oracle : X → Answer)
    (program : ExactJetProgram X Answer A)
    (next : A → ExactJetProgram X Answer B)
    {used : ℕ} {result : B}
    (heval : ExactJetProgram.Evaluates oracle (program.bind next) used (some result)) :
    ∃ value used₁ used₂,
      ExactJetProgram.Evaluates oracle program used₁ (some value) ∧
      ExactJetProgram.Evaluates oracle (next value) used₂ (some result) := by
  induction program generalizing used with
  | halt outcome =>
      cases outcome with
      | none => cases heval
      | some value => exact ⟨value, 0, used, .halt _, heval⟩
  | query point more ih =>
      cases heval with
      | query _ _ childUsed _ hchild =>
          obtain ⟨value, used₁, used₂, hmore, hnext⟩ := ih _ hchild
          exact ⟨value, used₁ + 1, used₂, .query _ _ _ _ hmore, hnext⟩

/-- Installed cap: every Halve receives its proved `2 T_p` allowance and the
final correction receives two more exact-jet queries. -/
noncomputable def baseTrialCap (data : VIPublicData E) (mu : ℝ) :
    (halvings : ℕ) → (r : ℝ) → ℕ
  | 0, _ => 2
  | halvings + 1, r =>
      2 * halvingIterationCount data.p data.Lp r mu +
        baseTrialCap data mu halvings (r / 2)

noncomputable def baseTrialCall (data : VIPublicData E) (mu delta : ℝ)
    (halvings : ℕ) (center : data.X) (R : ℝ) : CappedExactJetCall data where
  cap := baseTrialCap data mu halvings R
  program := baseTrialProgram data mu delta halvings center R

theorem baseTrialCall_finished_queries_le_cap
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) (halvings : ℕ) (center : data.X) (R : ℝ)
    {used : ℕ} {result : Option (EvaluatedNormalCertificate data)}
    (hrun : (baseTrialCall data mu delta halvings center R).execute
      data G oracle = .finished used result) :
    used ≤ baseTrialCap data mu halvings R := by
  exact CappedExactJetCall.finished_queries_le_cap data G oracle _ hrun

theorem baseTrialProgram_no_false_success
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) (halvings : ℕ) (center : data.X) (R : ℝ)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (heval : ExactJetProgram.Evaluates oracle.answer
      (baseTrialProgram data mu delta halvings center R) used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  induction halvings generalizing center R used with
  | zero =>
      exact correctionProgram_no_false_success data G oracle center delta heval
  | succ halvings ih =>
      simp only [baseTrialProgram] at heval
      obtain ⟨out, used₁, used₂, _, hnext⟩ :=
        ExactJetProgram.evaluates_bind_some_right oracle.answer
          (halvingProgram data center mu R) _ heval
      split at hnext
      · exact ih _ _ hnext
      · cases hnext

theorem baseTrialCall_no_false_success
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) (halvings : ℕ) (center : data.X) (R : ℝ)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (hrun : (baseTrialCall data mu delta halvings center R).execute
      data G oracle = .finished used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  exact baseTrialProgram_no_false_success data G oracle mu delta halvings center R
    (ExactJetProgram.evaluates_of_runWithFuel_finished hrun)

theorem exists_base_halving_threshold (data : VIPublicData E)
    (R delta : ℝ) (hR : 0 ≤ R) (hdelta : 0 < delta) :
    ∃ n : ℕ, correctionConstant data.p * data.Lp *
      (R / (2 : ℝ) ^ n) ^ data.p ≤ delta := by
  let c : ℝ := correctionConstant data.p * data.Lp * R ^ data.p
  let q : ℝ := (1 / 2 : ℝ) ^ data.p
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have hp0 : data.p ≠ 0 :=
      Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) data.p_ge_two)
    exact pow_lt_one₀ (by norm_num) (by norm_num) hp0
  have htq : Tendsto (fun n : ℕ ↦ q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have ht : Tendsto (fun n : ℕ ↦ c * q ^ n) atTop (nhds 0) := by
    simpa using htq.const_mul c
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht delta hdelta
  have hclose := hN N le_rfl
  have hnonneg : 0 ≤ c * q ^ N := by
    have hcc : 0 ≤ correctionConstant data.p := by
      unfold correctionConstant
      positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hcc data.Lp_pos.le)
      (pow_nonneg hR _)) (pow_nonneg hq0 _)
  have hle : c * q ^ N ≤ delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hclose
    exact hclose.le
  refine ⟨N, ?_⟩
  calc
    correctionConstant data.p * data.Lp * (R / (2 : ℝ) ^ N) ^ data.p =
        c * q ^ N := by
      simp only [c, q, div_pow, div_eq_mul_inv, one_pow, one_mul, mul_pow]
      rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm N data.p]
      ring
    _ ≤ delta := hle

/-- Least finite scheduled stage at which the source correction threshold is
met.  It depends only on public numerical inputs, not on the unknown operator
or its solution. -/
noncomputable def baseHalvingCount (data : VIPublicData E)
    (R delta : ℝ) : ℕ :=
  if hR : 0 ≤ R ∧ 0 < delta then
    Nat.find (exists_base_halving_threshold data R delta hR.1 hR.2)
  else 0

theorem baseHalvingCount_threshold (data : VIPublicData E)
    (R delta : ℝ) (hR : 0 ≤ R) (hdelta : 0 < delta) :
    correctionConstant data.p * data.Lp *
      (R / (2 : ℝ) ^ baseHalvingCount data R delta) ^ data.p ≤ delta := by
  rw [baseHalvingCount, dif_pos ⟨hR, hdelta⟩]
  exact Nat.find_spec (exists_base_halving_threshold data R delta hR hdelta)

/-- `BaseTrial` with its finite threshold-driven schedule installed. -/
noncomputable def scheduledBaseTrialCall (data : VIPublicData E)
    (mu delta : ℝ) (center : data.X) (R : ℝ) : CappedExactJetCall data :=
  baseTrialCall data mu delta (baseHalvingCount data R delta) center R

theorem scheduledBaseTrialCall_no_false_success
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) (center : data.X) (R : ℝ)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (hrun : (scheduledBaseTrialCall data mu delta center R).execute
      data G oracle = .finished used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  exact baseTrialCall_no_false_success data G oracle mu delta _ center R hrun

/-- The source scale `rho = (mu/Lp)^(1/(p-1))`. -/
noncomputable def baseStrongScale (data : VIPublicData E) (mu : ℝ) : ℝ :=
  (mu / data.Lp) ^ (1 / ((data.p - 1 : ℕ) : ℝ))

theorem baseStrongScale_pos (data : VIPublicData E) (mu : ℝ) (hmu : 0 < mu) :
    0 < baseStrongScale data mu := by
  unfold baseStrongScale
  exact Real.rpow_pos_of_pos (div_pos hmu data.Lp_pos) _

theorem exists_doubling_reaches_diameter (data : VIPublicData E)
    (mu : ℝ) (hmu : 0 < mu) :
    ∃ j : ℕ, data.D ≤ (2 : ℝ) ^ j * baseStrongScale data mu := by
  have hrho := baseStrongScale_pos data mu hmu
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    (data.D / baseStrongScale data mu) (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, ?_⟩
  have := mul_lt_mul_of_pos_right hj hrho
  rw [div_mul_cancel₀ data.D hrho.ne'] at this
  linarith

/-- Final index in the public geometric-radius list. -/
noncomputable def adaptiveGuessCount (data : VIPublicData E) (mu : ℝ) : ℕ :=
  if hmu : 0 < mu then Nat.find (exists_doubling_reaches_diameter data mu hmu)
  else 0

noncomputable def adaptiveGuessRadius (data : VIPublicData E) (mu : ℝ)
    (j : ℕ) : ℝ :=
  min data.D ((2 : ℝ) ^ j * baseStrongScale data mu)

/-- The last installed radius is exactly `D`, so the wrapper does not need an
unbounded search and does not append a second copy of `D`. -/
theorem adaptiveGuessRadius_last (data : VIPublicData E)
    (mu : ℝ) (hmu : 0 < mu) :
    adaptiveGuessRadius data mu (adaptiveGuessCount data mu) = data.D := by
  rw [adaptiveGuessCount, dif_pos hmu]
  unfold adaptiveGuessRadius
  rw [min_eq_left]
  exact Nat.find_spec (exists_doubling_reaches_diameter data mu hmu)

theorem adaptiveGuessRadius_before_last_lt (data : VIPublicData E)
    (mu : ℝ) (hmu : 0 < mu) (j : ℕ)
    (hj : j < adaptiveGuessCount data mu) :
    adaptiveGuessRadius data mu j < data.D := by
  have hnot : ¬ data.D ≤ (2 : ℝ) ^ j * baseStrongScale data mu := by
    rw [adaptiveGuessCount, dif_pos hmu] at hj
    exact Nat.find_min (exists_doubling_reaches_diameter data mu hmu) hj
  unfold adaptiveGuessRadius
  rw [min_eq_right (le_of_not_ge hnot)]
  exact lt_of_not_ge hnot

/-- Starting every trial from the original center, try the finite sequence of
public radius guesses. Each child BaseTrial is locally capped; only explicit
failure proceeds to the next guess. -/
noncomputable def adaptiveBaseProgramFrom (data : VIPublicData E)
    (mu delta : ℝ) (center : data.X) :
    (remaining j : ℕ) → ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data)
  | 0, j =>
      let call := scheduledBaseTrialCall data mu delta center
        (adaptiveGuessRadius data mu j)
      call.program.locallyCapped call.cap
  | remaining + 1, j =>
      let call := scheduledBaseTrialCall data mu delta center
        (adaptiveGuessRadius data mu j)
      ExactJetProgram.orElse (call.program.locallyCapped call.cap)
        (adaptiveBaseProgramFrom data mu delta center remaining (j + 1))

noncomputable def adaptiveBaseCapFrom (data : VIPublicData E)
    (mu delta : ℝ) (center : data.X) : (remaining j : ℕ) → ℕ
  | 0, j => (scheduledBaseTrialCall data mu delta center
      (adaptiveGuessRadius data mu j)).cap
  | remaining + 1, j =>
      (scheduledBaseTrialCall data mu delta center
        (adaptiveGuessRadius data mu j)).cap +
      adaptiveBaseCapFrom data mu delta center remaining (j + 1)

noncomputable def adaptiveBaseCall (data : VIPublicData E)
    (center : data.X) (mu delta : ℝ) : CappedExactJetCall data where
  cap := adaptiveBaseCapFrom data mu delta center (adaptiveGuessCount data mu) 0
  program := adaptiveBaseProgramFrom data mu delta center (adaptiveGuessCount data mu) 0

theorem ExactJetProgram.evaluation_of_locallyCapped_success'
    {X Answer Output : Type*} (oracle : X → Answer)
    (program : ExactJetProgram X Answer Output)
    (cap used : ℕ) (value : Output)
    (heval : ExactJetProgram.Evaluates oracle
      (program.locallyCapped cap) used (some value)) :
    ExactJetProgram.Evaluates oracle program used (some value) ∧ used ≤ cap := by
  induction cap generalizing program used with
  | zero =>
      cases program <;> simp only [ExactJetProgram.locallyCapped] at heval
      · cases heval
        exact ⟨.halt _, le_rfl⟩
      · cases heval
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
              obtain ⟨horig, hle⟩ := ih _ _ hchild
              exact ⟨.query point next childUsed (some value) horig,
                Nat.succ_le_succ hle⟩

theorem ExactJetProgram.property_of_orElse_success
    {X Answer Output : Type*} (oracle : X → Answer)
    (P : Output → Prop) (first fallback : ExactJetProgram X Answer Output)
    {used : ℕ} {value : Output}
    (hfirst : ∀ used value,
      ExactJetProgram.Evaluates oracle first used (some value) → P value)
    (hfallback : ∀ used value,
      ExactJetProgram.Evaluates oracle fallback used (some value) → P value)
    (heval : ExactJetProgram.Evaluates oracle (first.orElse fallback)
      used (some value)) : P value := by
  induction first generalizing used with
  | halt result =>
      cases result with
      | none => exact hfallback used value heval
      | some result =>
          cases heval
          exact hfirst _ _ (.halt _)
  | query point next ih =>
      cases heval with
      | query _ _ childUsed _ hchild =>
          exact ih (oracle point)
            (fun u v huv ↦ hfirst (u + 1) v (.query point next u _ huv))
            hchild

theorem adaptiveBaseProgramFrom_no_false_success
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu delta : ℝ) (center : data.X) (remaining j : ℕ)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (heval : ExactJetProgram.Evaluates oracle.answer
      (adaptiveBaseProgramFrom data mu delta center remaining j) used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  induction remaining generalizing j used cert with
  | zero =>
      exact scheduledBaseTrialCall_no_false_success data G oracle mu delta center _
        (let h := ExactJetProgram.evaluation_of_locallyCapped_success'
            oracle.answer _ _ _ _ heval
         h.1.runWithFuel_eq h.2)
  | succ remaining ih =>
      simp only [adaptiveBaseProgramFrom] at heval
      apply ExactJetProgram.property_of_orElse_success oracle.answer
        (fun cert ↦ cert.IsVerifiedFor data G delta) _ _ _ _ heval
      · intro used cert hlocal
        have horig := ExactJetProgram.evaluation_of_locallyCapped_success'
          oracle.answer _ _ used cert hlocal
        exact scheduledBaseTrialCall_no_false_success data G oracle mu delta center _
          (horig.1.runWithFuel_eq horig.2)
      · intro used cert htail
        exact ih (j + 1) (used := used) htail

/-- Concrete source algorithm underlying `prop:base-strong`. Its interface
success and sharp cost theorem are proved separately from this executable
definition. -/
noncomputable def baseStrongSolver (data : VIPublicData E) : StrongSolver data where
  leadingConstant := 1
  leadingConstant_pos := by norm_num
  solve := adaptiveBaseCall data

/-- Dimension- and instance-uniform executable family for each fixed order.
The leading constant will be enlarged, as a function of `p` alone, when the
sharp interface-cost estimate is attached. -/
noncomputable def baseStrongSolverFamily (p : ℕ) : StrongSolverFamily p where
  leadingConstant := 1
  leadingConstant_pos := by norm_num
  solve := fun _ _ _ _ data _ => (baseStrongSolver data).solve

theorem baseStrongSolver_no_false_success (data : VIPublicData E)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (center : data.X) (mu delta : ℝ) (used : ℕ)
    (cert : EvaluatedNormalCertificate data)
    (hrun : ((baseStrongSolver data).solve center mu delta).execute
      data G oracle = .finished used (some cert)) :
    cert.IsVerifiedFor data G delta := by
  exact adaptiveBaseProgramFrom_no_false_success data G oracle mu delta center _ 0
    (ExactJetProgram.evaluates_of_runWithFuel_finished hrun)

theorem halvingThreshold_nonneg (p : ℕ) (Lp r mu : ℝ)
    (hLp : 0 ≤ Lp) (hr : 0 ≤ r) (hmu : 0 ≤ mu) :
    0 ≤ halvingThreshold p Lp r mu := by
  unfold halvingThreshold
  apply Real.rpow_nonneg
  apply div_nonneg
  · have hbeta : 0 ≤ tensorBetaCoefficient p := by
      unfold tensorBetaCoefficient
      positivity
    positivity
  · exact hmu

/-- The ceiling in `T_p` costs less than one extra iteration; together with
the source's `max 1`, this is the explicit per-stage upper estimate. -/
theorem halvingIterationCount_cast_le (p : ℕ) (Lp r mu : ℝ)
    (hLp : 0 ≤ Lp) (hr : 0 ≤ r) (hmu : 0 ≤ mu) :
    (halvingIterationCount p Lp r mu : ℝ) ≤
      halvingThreshold p Lp r mu + 1 := by
  have hth := halvingThreshold_nonneg p Lp r mu hLp hr hmu
  rw [halvingIterationCount]
  norm_cast
  rw [Nat.cast_max]
  apply max_le
  · norm_num
    linarith
  · exact (Nat.ceil_lt_add_one hth).le

/-- Real-valued unfolding of the complete `BaseTrial` cap. -/
noncomputable def baseTrialRealCapBound (data : VIPublicData E) (mu : ℝ) :
    (halvings : ℕ) → (r : ℝ) → ℝ
  | 0, _ => 2
  | halvings + 1, r =>
      2 * (halvingThreshold data.p data.Lp r mu + 1) +
        baseTrialRealCapBound data mu halvings (r / 2)

theorem baseTrialCap_cast_le_realBound (data : VIPublicData E)
    (mu : ℝ) (hmu : 0 ≤ mu) (halvings : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (baseTrialCap data mu halvings r : ℝ) ≤
      baseTrialRealCapBound data mu halvings r := by
  induction halvings generalizing r with
  | zero => simp [baseTrialCap, baseTrialRealCapBound]
  | succ halvings ih =>
      simp only [baseTrialCap, baseTrialRealCapBound, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      gcongr
      · exact halvingIterationCount_cast_le data.p data.Lp r mu
          data.Lp_pos.le hr hmu
      · exact ih (r / 2) (by positivity)

end

end LeanArticleAudit.Pilot
