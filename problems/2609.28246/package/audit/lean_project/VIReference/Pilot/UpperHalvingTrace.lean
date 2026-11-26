import VIReference.Pilot.UpperBaseStrong

open Set
open scoped RealInnerProductSpace BigOperators

namespace VIReference.Pilot
noncomputable section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def halvingExecutionCenters (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) : ℕ → data.X
  | 0 => center
  | k + 1 =>
      let x := halvingExecutionCenters data oracle mu center k
      let yn := knownModelStep data x (oracle x)
      let lambda := 1 / ((tensorBetaCoefficient data.p * data.Lp) *
        ‖yn.1.1 - x.1‖ ^ (data.p - 1))
      let xp := compactConvexProjection data.X data.X_nonempty data.X_compact
        data.X_convex (x.1 - lambda • symmetricJetValue data (oracle yn.1))
      ⟨xp, compactConvexProjection_mem data.X data.X_nonempty data.X_compact
        data.X_convex _⟩

noncomputable def halvingExecutionY (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) (k : ℕ) : E :=
  (knownModelStep data (halvingExecutionCenters data oracle mu center k)
    (oracle (halvingExecutionCenters data oracle mu center k))).1.1

noncomputable def halvingExecutionLambda (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) (k : ℕ) : ℝ :=
  1 / ((tensorBetaCoefficient data.p * data.Lp) *
    ‖halvingExecutionY data oracle mu center k -
      (halvingExecutionCenters data oracle mu center k).1‖ ^ (data.p - 1))

noncomputable def halvingExecutionWeighted (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) (k : ℕ) : E :=
  ∑ i ∈ Finset.range k,
    halvingExecutionLambda data oracle mu center i •
      halvingExecutionY data oracle mu center i

noncomputable def halvingExecutionLambdaSum (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, halvingExecutionLambda data oracle mu center i

theorem halvingProgramAux_complete_evaluates (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) (remaining k : ℕ)
    (hnone : ∀ i, k ≤ i → i < k + remaining →
      halvingExecutionY data oracle mu center i ≠
        (halvingExecutionCenters data oracle mu center i).1) :
    ExactJetProgram.Evaluates oracle
      (halvingProgramAux data mu remaining
        (halvingExecutionCenters data oracle mu center k)
        (halvingExecutionWeighted data oracle mu center k)
        (halvingExecutionLambdaSum data oracle mu center k))
      (2 * remaining)
      (some {
        point := if halvingExecutionLambdaSum data oracle mu center (k + remaining) = 0
          then (halvingExecutionCenters data oracle mu center (k + remaining)).1
          else (1 / halvingExecutionLambdaSum data oracle mu center (k + remaining)) •
            halvingExecutionWeighted data oracle mu center (k + remaining)
        early := false
        normal := 0
        value := 0 }) := by
  induction remaining generalizing k with
  | zero =>
      simp [halvingProgramAux, halvingExecutionLambdaSum,
        halvingExecutionWeighted]
      exact .halt _
  | succ remaining ih =>
      simp only [halvingProgramAux]
      apply ExactJetProgram.Evaluates.query
      have hne :
          (knownModelStep data (halvingExecutionCenters data oracle mu center k)
            (oracle (halvingExecutionCenters data oracle mu center k))).1.1 ≠
              (halvingExecutionCenters data oracle mu center k).1 := by
        simpa [halvingExecutionY] using hnone k (le_refl _) (by omega)
      split
      · contradiction
      apply ExactJetProgram.Evaluates.query
      have hcenter : halvingExecutionCenters data oracle mu center (k + 1) =
          ⟨compactConvexProjection data.X data.X_nonempty data.X_compact data.X_convex
              ((halvingExecutionCenters data oracle mu center k).1 -
                halvingExecutionLambda data oracle mu center k •
                  symmetricJetValue data
                    (oracle (knownModelStep data
                      (halvingExecutionCenters data oracle mu center k)
                      (oracle (halvingExecutionCenters data oracle mu center k))).1)),
            compactConvexProjection_mem data.X data.X_nonempty data.X_compact
              data.X_convex _⟩ := by
        rfl
      have hweighted : halvingExecutionWeighted data oracle mu center k +
          halvingExecutionLambda data oracle mu center k •
            halvingExecutionY data oracle mu center k =
          halvingExecutionWeighted data oracle mu center (k + 1) := by
        rw [halvingExecutionWeighted, halvingExecutionWeighted,
          Finset.sum_range_succ]
      have hLambda : halvingExecutionLambdaSum data oracle mu center k +
          halvingExecutionLambda data oracle mu center k =
          halvingExecutionLambdaSum data oracle mu center (k + 1) := by
        rw [halvingExecutionLambdaSum, halvingExecutionLambdaSum,
          Finset.sum_range_succ]
      dsimp only [halvingExecutionY, halvingExecutionLambda] at hcenter hweighted hLambda ⊢
      rw [← hcenter, hweighted, hLambda]
      have htail := ih (k + 1) (fun i hki hilast ↦ hnone i (by omega) (by omega))
      convert htail using 1 <;> simp +arith

theorem halvingExecutionLambda_pos (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) (k : ℕ)
    (hne : halvingExecutionY data oracle mu center k ≠
      (halvingExecutionCenters data oracle mu center k).1) :
    0 < halvingExecutionLambda data oracle mu center k := by
  have hbeta : 0 < tensorBetaCoefficient data.p := by
    unfold tensorBetaCoefficient
    exact div_pos (mul_pos (by norm_num) (by exact_mod_cast
      (lt_of_lt_of_le (by omega : 0 < 2) data.p_ge_two))) (by positivity)
  unfold halvingExecutionLambda
  exact one_div_pos.mpr (mul_pos (mul_pos hbeta data.Lp_pos)
    (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) _))

theorem halvingExecutionLambdaSum_pos (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) (T : ℕ) (hT : 0 < T)
    (hnone : ∀ i < T, halvingExecutionY data oracle mu center i ≠
      (halvingExecutionCenters data oracle mu center i).1) :
    0 < halvingExecutionLambdaSum data oracle mu center T := by
  unfold halvingExecutionLambdaSum
  have hzero : 0 ∈ Finset.range T := Finset.mem_range.mpr hT
  have hterm := halvingExecutionLambda_pos data oracle mu center 0 (hnone 0 hT)
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (fun i hi ↦ (halvingExecutionLambda_pos data oracle mu center i
      (hnone i (Finset.mem_range.mp hi))).le) hzero)

theorem halvingExecutionCenters_succ_exact (data : VIPublicData E)
    (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
    (mu : ℝ) (center : data.X) (k : ℕ) :
    (halvingExecutionCenters data oracle.answer mu center (k + 1)).1 =
      compactConvexProjection data.X data.X_nonempty data.X_compact data.X_convex
        ((halvingExecutionCenters data oracle.answer mu center k).1 -
          halvingExecutionLambda data oracle.answer mu center k •
            G (halvingExecutionY data oracle.answer mu center k)) := by
  simp only [halvingExecutionCenters]
  rw [symmetricJetValue_feasible_exact data G oracle]
  rfl

theorem halvingProgram_complete_succeeds_and_halves
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu r : ℝ) (hmu : 0 < mu) (hr : 0 < r)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (hcenter : ‖center.1 - zStar‖ ≤ r)
    (hspec : ∀ i < halvingIterationCount data.p data.Lp r mu,
      IsKnownModelStep data
        (halvingExecutionCenters data oracle.answer mu center i)
        (oracle.answer (halvingExecutionCenters data oracle.answer mu center i))
        (knownModelStep data
          (halvingExecutionCenters data oracle.answer mu center i)
          (oracle.answer (halvingExecutionCenters data oracle.answer mu center i))))
    (hnone : ∀ i < halvingIterationCount data.p data.Lp r mu,
      halvingExecutionY data oracle.answer mu center i ≠
        (halvingExecutionCenters data oracle.answer mu center i).1) :
    let T := halvingIterationCount data.p data.Lp r mu
    let Lambda := halvingExecutionLambdaSum data oracle.answer mu center T
    let ybar := (1 / Lambda) • halvingExecutionWeighted data oracle.answer mu center T
    ExactJetProgram.Evaluates oracle.answer (halvingProgram data center mu r)
      (2 * T) (some { point := ybar, early := false, normal := 0, value := 0 }) ∧
    ybar ∈ data.X ∧ ‖ybar - zStar‖ ≤ r / 2 := by
  dsimp only
  let T := halvingIterationCount data.p data.Lp r mu
  have hT : 0 < T := halvingIterationCount_pos _ _ _ _
  have hLambda := halvingExecutionLambdaSum_pos data oracle.answer mu center T hT hnone
  have heval := halvingProgramAux_complete_evaluates data oracle.answer mu center T 0
    (fun i hi hilast ↦ hnone i (by simpa [T] using hilast))
  have heval' : ExactJetProgram.Evaluates oracle.answer (halvingProgram data center mu r)
      (2 * T) (some {
        point := (1 / halvingExecutionLambdaSum data oracle.answer mu center T) •
          halvingExecutionWeighted data oracle.answer mu center T
        early := false
        normal := 0
        value := 0 }) := by
    simp only [Nat.zero_add, halvingExecutionCenters, halvingExecutionWeighted,
      halvingExecutionLambdaSum, Finset.range_zero, Finset.sum_empty] at heval
    have hsumneq : (∑ i ∈ Finset.range T,
        halvingExecutionLambda data oracle.answer mu center i) ≠ 0 := by
      simpa [halvingExecutionLambdaSum] using hLambda.ne'
    rw [if_neg hsumneq] at heval
    simpa [halvingProgram, T, halvingExecutionLambdaSum,
      halvingExecutionWeighted] using heval
  refine ⟨heval', ?_⟩
  exact halving_full_schedule_halves data G oracle hG mu r hmu hr hstrong zStar hz
    (halvingExecutionCenters data oracle.answer mu center) hcenter hspec hnone
    (fun i hi ↦ halvingExecutionCenters_succ_exact data G oracle mu center i)


theorem knownModelStep_eq_center_verified_zero
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G) (x : data.X)
    (hspec : IsKnownModelStep data x (oracle.answer x)
      (knownModelStep data x (oracle.answer x)))
    (heq : (knownModelStep data x (oracle.answer x)).1.1 = x.1) :
    let yn := knownModelStep data x (oracle.answer x)
    ({ point := yn.1, normal := yn.2,
       value := symmetricJetValue data (oracle.answer x) } :
      EvaluatedNormalCertificate data).IsVerifiedFor data G 0 := by
  dsimp only
  let yn := knownModelStep data x (oracle.answer x)
  have hvalue := symmetricJetValue_feasible_exact data G oracle x
  have htaylor := taylorModelFromJet_feasible_exact data G oracle x x.1
  have htaylor_center : taylorModel data.p G x.1 x.1 = G x.1 := by
    rw [taylorModel]
    rw [Finset.sum_eq_single 0]
    · simp [iteratedFDeriv_zero_eq_comp]
    · intro j hj hj0
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      haveI : Nonempty (Fin j) := Fin.pos_iff_nonempty.mp hjpos
      have hzfun : (fun _ : Fin j ↦ x.1 - x.1) = (0 : Fin j → E) := by
        funext i
        simp
      rw [hzfun, ContinuousMultilinearMap.map_zero, smul_zero]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr
        (lt_of_lt_of_le (by omega : 0 < 2) data.p_ge_two))).elim
  have hzero : G x.1 + yn.2 = 0 := by
    have hm := hspec.2
    rw [heq] at hm
    simp only [sub_self, smul_zero, add_zero] at hm
    rw [htaylor, htaylor_center] at hm
    exact hm
  refine ⟨hspec.1, ?_, ?_⟩
  · dsimp only
    rw [heq]
    exact hvalue
  · dsimp only
    rw [hvalue, hzero, norm_zero]

theorem knownModelStep_eq_center_is_solution
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G) (x : data.X)
    (hspec : IsKnownModelStep data x (oracle.answer x)
      (knownModelStep data x (oracle.answer x)))
    (heq : (knownModelStep data x (oracle.answer x)).1.1 = x.1) :
    IsVISolution data G x.1 := by
  have hcert := knownModelStep_eq_center_verified_zero data G oracle x hspec heq
  refine ⟨x.2, ?_⟩
  intro z hz
  have hn := hcert.1 z hz
  have hnorm := hcert.2.2
  have hzero : G x.1 + (knownModelStep data x (oracle.answer x)).2 = 0 := by
    dsimp only at hnorm
    rw [symmetricJetValue_feasible_exact data G oracle x] at hnorm
    exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  have hnEq : (knownModelStep data x (oracle.answer x)).2 = -G x.1 := by
    exact eq_neg_of_add_eq_zero_right hzero
  dsimp only at hn
  rw [heq, hnEq, inner_neg_left] at hn
  linarith

theorem stronglyMonotone_solution_unique (data : VIPublicData E) (G : E → E)
    (mu : ℝ) (hmu : 0 < mu) (hstrong : StronglyMonotoneOn data G mu)
    {x z : E} (hx : IsVISolution data G x) (hz : IsVISolution data G z) : x = z := by
  have hm := hstrong x hx.1 z hz.1
  have hxz := hx.2 z hz.1
  have hzx := hz.2 x hx.1
  rw [inner_sub_left] at hm
  have hxneg : inner ℝ (G x) (x - z) ≤ 0 := by
    rw [show x - z = -(z - x) by abel, inner_neg_right]
    linarith
  have hprod : mu * ‖x - z‖ ^ 2 ≤ 0 := by linarith
  have hsquare : ‖x - z‖ ^ 2 = 0 := by
    nlinarith [mul_nonneg hmu.le (sq_nonneg ‖x - z‖)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsquare))




theorem halvingProgramAux_early_evaluates (data : VIPublicData E)
    (oracle : data.X → SymmetricExactJet E data.p) (mu : ℝ)
    (center : data.X) (n tail k : ℕ)
    (hnone : ∀ i, k ≤ i → i < k + n →
      halvingExecutionY data oracle mu center i ≠
        (halvingExecutionCenters data oracle mu center i).1)
    (heq : halvingExecutionY data oracle mu center (k + n) =
      (halvingExecutionCenters data oracle mu center (k + n)).1) :
    ExactJetProgram.Evaluates oracle
      (halvingProgramAux data mu (n + 1 + tail)
        (halvingExecutionCenters data oracle mu center k)
        (halvingExecutionWeighted data oracle mu center k)
        (halvingExecutionLambdaSum data oracle mu center k))
      (2 * n + 1)
      (some {
        point := halvingExecutionY data oracle mu center (k + n)
        early := true
        normal := (knownModelStep data
          (halvingExecutionCenters data oracle mu center (k + n))
          (oracle (halvingExecutionCenters data oracle mu center (k + n)))).2
        value := symmetricJetValue data
          (oracle (halvingExecutionCenters data oracle mu center (k + n))) }) := by
  induction n generalizing k with
  | zero =>
      rw [show 0 + 1 + tail = tail + 1 by omega, halvingProgramAux]
      apply ExactJetProgram.Evaluates.query
      dsimp only
      split
      · apply ExactJetProgram.Evaluates.halt
      · rename_i hne
        exact (hne (by simpa [halvingExecutionY] using heq)).elim
  | succ n ih =>
      rw [show (n + 1) + 1 + tail = (n + 1 + tail) + 1 by omega,
        halvingProgramAux]
      apply ExactJetProgram.Evaluates.query
      dsimp only
      have hne :
          (knownModelStep data (halvingExecutionCenters data oracle mu center k)
            (oracle (halvingExecutionCenters data oracle mu center k))).1.1 ≠
              (halvingExecutionCenters data oracle mu center k).1 := by
        simpa [halvingExecutionY] using hnone k (le_refl _) (by omega)
      split
      · contradiction
      apply ExactJetProgram.Evaluates.query
      have hcenter : halvingExecutionCenters data oracle mu center (k + 1) =
          ⟨compactConvexProjection data.X data.X_nonempty data.X_compact data.X_convex
              ((halvingExecutionCenters data oracle mu center k).1 -
                halvingExecutionLambda data oracle mu center k •
                  symmetricJetValue data
                    (oracle (knownModelStep data
                      (halvingExecutionCenters data oracle mu center k)
                      (oracle (halvingExecutionCenters data oracle mu center k))).1)),
            compactConvexProjection_mem data.X data.X_nonempty data.X_compact
              data.X_convex _⟩ := by rfl
      have hweighted : halvingExecutionWeighted data oracle mu center k +
          halvingExecutionLambda data oracle mu center k •
            halvingExecutionY data oracle mu center k =
          halvingExecutionWeighted data oracle mu center (k + 1) := by
        rw [halvingExecutionWeighted, halvingExecutionWeighted,
          Finset.sum_range_succ]
      have hLambda : halvingExecutionLambdaSum data oracle mu center k +
          halvingExecutionLambda data oracle mu center k =
          halvingExecutionLambdaSum data oracle mu center (k + 1) := by
        rw [halvingExecutionLambdaSum, halvingExecutionLambdaSum,
          Finset.sum_range_succ]
      dsimp only [halvingExecutionY, halvingExecutionLambda] at hcenter hweighted hLambda ⊢
      rw [← hcenter, hweighted, hLambda]
      have htail := ih (k + 1)
        (fun i hki hilast ↦ hnone i (by omega) (by omega))
        (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using heq)
      convert htail using 1
      all_goals simp [halvingExecutionY, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] <;> omega




/-- Executable `prop:halving` once the genuine model-step specification is
available at every queried center. -/
theorem halvingProgram_succeeds_and_halves_of_model_spec
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu r : ℝ) (hmu : 0 < mu) (hr : 0 < r)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (hcenter : ‖center.1 - zStar‖ ≤ r)
    (hspec : ∀ i < halvingIterationCount data.p data.Lp r mu,
      IsKnownModelStep data
        (halvingExecutionCenters data oracle.answer mu center i)
        (oracle.answer (halvingExecutionCenters data oracle.answer mu center i))
        (knownModelStep data
          (halvingExecutionCenters data oracle.answer mu center i)
          (oracle.answer (halvingExecutionCenters data oracle.answer mu center i)))) :
    ∃ used out,
      ExactJetProgram.Evaluates oracle.answer (halvingProgram data center mu r)
        used (some out) ∧
      used ≤ 2 * halvingIterationCount data.p data.Lp r mu ∧
      out.point ∈ data.X ∧ ‖out.point - zStar‖ ≤ r / 2 := by
  classical
  let T := halvingIterationCount data.p data.Lp r mu
  by_cases hnone : ∀ i < T,
      halvingExecutionY data oracle.answer mu center i ≠
        (halvingExecutionCenters data oracle.answer mu center i).1
  · have hfull := halvingProgram_complete_succeeds_and_halves data G oracle hG
      center mu r hmu hr hstrong zStar hz hcenter hspec hnone
    dsimp only at hfull
    let Lambda := halvingExecutionLambdaSum data oracle.answer mu center T
    let ybar := (1 / Lambda) • halvingExecutionWeighted data oracle.answer mu center T
    refine ⟨2 * T, { point := ybar, early := false, normal := 0, value := 0 },
      hfull.1, le_rfl, hfull.2⟩
  · push_neg at hnone
    obtain ⟨i, hiT, hieq⟩ := hnone
    let P : ℕ → Prop := fun j ↦ j < T ∧
      halvingExecutionY data oracle.answer mu center j =
        (halvingExecutionCenters data oracle.answer mu center j).1
    have hex : ∃ j, P j := ⟨i, hiT, hieq⟩
    let first := Nat.find hex
    have hfirst := Nat.find_spec hex
    let tail := T - (first + 1)
    have hdecomp : first + 1 + tail = T := by
      dsimp [tail]
      omega
    have hprior : ∀ j, 0 ≤ j → j < 0 + first →
        halvingExecutionY data oracle.answer mu center j ≠
          (halvingExecutionCenters data oracle.answer mu center j).1 := by
      intro j hj0 hj
      intro heq
      have hle : first ≤ j := by
        dsimp [first]
        exact Nat.find_min' hex ⟨by omega, heq⟩
      omega
    have heval := halvingProgramAux_early_evaluates data oracle.answer mu center
      first tail 0 hprior (by simpa using hfirst.2)
    have heval' : ExactJetProgram.Evaluates oracle.answer
        (halvingProgram data center mu r) (2 * first + 1)
        (some {
          point := halvingExecutionY data oracle.answer mu center first
          early := true
          normal := (knownModelStep data
            (halvingExecutionCenters data oracle.answer mu center first)
            (oracle.answer (halvingExecutionCenters data oracle.answer mu center first))).2
          value := symmetricJetValue data
            (oracle.answer (halvingExecutionCenters data oracle.answer mu center first)) }) := by
      rw [hdecomp] at heval
      simpa [halvingProgram, T, halvingExecutionCenters,
        halvingExecutionWeighted, halvingExecutionLambdaSum] using heval
    have hxsol := knownModelStep_eq_center_is_solution data G oracle
      (halvingExecutionCenters data oracle.answer mu center first)
      (hspec first hfirst.1) (by simpa [halvingExecutionY] using hfirst.2)
    have huniq := stronglyMonotone_solution_unique data G mu hmu hstrong hxsol hz
    have hyEq : halvingExecutionY data oracle.answer mu center first = zStar := by
      rw [hfirst.2, huniq]
    refine ⟨2 * first + 1, _, heval', ?_, ?_, ?_⟩
    · omega
    · rw [hfirst.2]
      exact (halvingExecutionCenters data oracle.answer mu center first).2
    · rw [hyEq, sub_self, norm_zero]
      positivity



end
end VIReference.Pilot
