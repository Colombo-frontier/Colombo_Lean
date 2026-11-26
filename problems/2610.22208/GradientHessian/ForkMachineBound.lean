import GradientHessian.ForkChronologicalProbability
import GradientHessian.ForkCappedPolicy
import GradientHessian.DisclosureStopping

/-!
# The fork bound for machines with arbitrary internal computation

Previous readouts are synthesized by the charged disclosure compiler.  A
finite snapshot retains the actual selected test vectors.  The retention
condition below speaks only about vectors in the machine's test register;
monotonicity of hit events is proved from it.
-/

namespace GradientHessian.ForkMachineBound

open Matrix MeasureTheory ProbabilityTheory LowRank OracleComposition
open GradientHessian.MatrixGoodSpectrum GradientHessian.ForkChronologicalProbability
open scoped InnerProductSpace ENNReal BigOperators
noncomputable section

abbrev Input (d n r : ℕ) (Seed Private : Type*) :=
  (Matrix (Fin d) (Fin n) ℝ × Seed) × (EuclideanSpace ℝ (Fin r) × Private)

def preBudget (J q₀ S : ℕ) : ℕ :=
  q₀+S*ReadoutFilter.degree (ReadoutFilter.matrixUpper J) ReadoutFilter.delta

def totalBudget (J q₀ S r q₁ : ℕ) : ℕ := preBudget J q₀ S+r*q₁

variable {d n r s : ℕ} {Seed PreState PostState Private : Type*}
  [MeasurableSpace Seed] [MeasurableSpace PreState] [MeasurableSpace PostState]
  [MeasurableSpace Private]

def sourceA (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (t : Input d n r Seed Private) : Matrix (Fin d) (Fin d) ℝ := sourceMatrix P J t.1.1

def earlierReadout (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ)
    (t : Input d n r Seed Private) : (Fin d → ℝ) → Fin d → ℝ :=
  ReadoutOracle.readout (ReadoutFilter.matrixUpper J) P (sourceA J P t) fallback

def saved (pre : DisclosureCompiler.Program d PreState) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ)
    (initial : MeasurableStateMap Seed PreState) (N : ℕ) (t : Input d n r Seed Private) :
    Bool × PreState := pre.eval (sourceA J P t) (earlierReadout J P fallback t) N (initial.1 t.1.2)

def snapshot (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (initial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ) (N : ℕ)
    (state : PreState) (t : Input d n r Seed Private) : Fin s → EuclideanSpace ℝ (Fin d) :=
  post.output ((post.step (fun v => sourceA J P t *ᵥv))^[N] (initial.1 (state,t.2)))

def postHit (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (initial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (γ : ℝ) (N : ℕ) (state : PreState)
    (t : Input d n r Seed Private) : Prop :=
  enabled.1 state = true ∧ ∃ j,
    γ < |⟪UnmarkedReadout.sourceOutput J P t.1.1 B fallback t.2.1,
      snapshot post initial J P N state t j⟫_ℝ|

/-- Nonzero entries of the selected-test register persist through every
internal or oracle step. Zero denotes an unused slot and may be replaced. -/
def RetainsTests (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d))) :
    Prop := ∀ A state i, post.output state i ≠ 0 → ∃ j,
      post.output (post.step (fun v => A*ᵥv) state) j = post.output state i

omit [MeasurableSpace Seed] in
theorem postHit_mono (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (initial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) {γ : ℝ} (hγ : 0 < γ) (hretain : RetainsTests post)
    (state : PreState) (t : Input d n r Seed Private) :
    Monotone (fun N => postHit post initial enabled J P B fallback γ N state t) := by
  intro N M hNM hN
  refine ⟨hN.1,?_⟩
  apply post.snapshot_property_mono (fun v => sourceA J P t*ᵥv)
    (fun u => ∃ j, γ < |⟪UnmarkedReadout.sourceOutput J P t.1.1 B fallback t.2.1,post.output u j⟫_ℝ|)
    _ (initial.1 (state,t.2)) hNM hN.2
  intro u hu
  obtain ⟨i,hi⟩ := hu
  have hn : post.output u i ≠ 0 := by
    intro hz
    rw [hz,inner_zero_right,abs_zero] at hi
    exact (not_lt_of_ge hγ.le) hi
  obtain ⟨j,hj⟩ := hretain (sourceA J P t) u i hn
  exact ⟨j,by rw [hj]; exact hi⟩

def cutoffHit (pre : DisclosureCompiler.Program d PreState)
    (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (γ : ℝ) (N : ℕ) : Set (Input d n r Seed Private) :=
  pre.cutoffHit (sourceA J P) (earlierReadout J P fallback) (fun t => preInitial.1 t.1.2)
    (postHit post postInitial enabled J P B fallback γ) N

def eventualHit (pre : DisclosureCompiler.Program d PreState)
    (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (γ : ℝ) : Set (Input d n r Seed Private) :=
  pre.eventualHit (sourceA J P) (earlierReadout J P fallback) (fun t => preInitial.1 t.1.2)
    (postHit post postInitial enabled J P B fallback γ)

def compiledPre (pre : DisclosureCompiler.Program d PreState) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ)
    (initial : MeasurableStateMap Seed PreState) (N q₀ S : ℕ) :
    Procedure d (preBudget J q₀ S) Seed (Bool × PreState) :=
  (pre.compile (DisclosureCompiler.readoutProcedure (ReadoutFilter.matrixUpper J) P fallback)
    N q₀ S).comap initial

/-- Legal execution caps are required only on source-good matrices and unit
fresh marks. The compiler supplies hard caps for all other reply histories. -/
structure Legal (pre : DisclosureCompiler.Program d PreState)
    (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ) (q₀ S q₁ : ℕ) : Prop where
  preprocessing : ∀ t : Input d n r Seed Private,
    t.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J → ∀ N,
    pre.ordinaryCalls (sourceA J P t) (earlierReadout J P fallback t) N (preInitial.1 t.1.2) ≤ q₀ ∧
    pre.disclosures (sourceA J P t) (earlierReadout J P fallback t) N (preInitial.1 t.1.2) ≤ S
  branch : ∀ t : Input d n r Seed Private,
    t.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J → ‖t.2.1‖ = 1 → ∀ N,
    (saved pre J P fallback preInitial N t).1 = true →
    enabled.1 (saved pre J P fallback preInitial N t).2 = true → ∀ M,
    post.calls (fun v => sourceA J P t*ᵥv) M
      (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2)) ≤ q₁ ∧
    ∀ j, ‖snapshot post postInitial J P M (saved pre J P fallback preInitial N t).2 t j‖ ≤ 1

/-- Exact event correspondence at a finite cutoff. The branch's actual saved
state, selected tests, and decisions using prior readouts are preserved. -/
theorem compiled_event_iff (pre : DisclosureCompiler.Program d PreState)
    (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) (q₀ S q₁ N : ℕ)
    (hlegal : Legal (n := n) pre post preInitial postInitial enabled J P fallback q₀ S q₁)
    {γ : ℝ} (hγ : 0 < γ) (t : Input d n r Seed Private)
    (hgood : t.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J) (hunit : ‖t.2.1‖ = 1) :
    t ∈ branchHit J P B fallback (compiledPre pre J P fallback preInitial N q₀ S)
      (ForkCappedPolicy.post post postInitial enabled q₁ N) γ ↔
    t ∈ cutoffHit pre post preInitial postInitial enabled J P B fallback γ N := by
  have hA : (sourceA J P t)ᵀ = sourceA J P t := sourceMatrix_symmetric t.1.1 hP J
  have hpre : (compiledPre pre J P fallback preInitial N q₀ S).run (sourceA J P t) t.1.2 =
      saved pre J P fallback preInitial N t := by
    rw [compiledPre,Procedure.run_comap]
    exact pre.literal_preprocessing_simulates (ReadoutFilter.matrixUpper J) P _ hA fallback N q₀ S
      (preInitial.1 t.1.2) (hlegal.preprocessing t hgood N).1 (hlegal.preprocessing t hgood N).2
  change (∃ j, γ < |⟪UnmarkedReadout.sourceOutput J P t.1.1 B fallback t.2.1,
      (ForkCappedPolicy.post post postInitial enabled q₁ N).run (sourceA J P t)
        ((compiledPre pre J P fallback preInitial N q₀ S).run (sourceA J P t) t.1.2,t.2) j⟫_ℝ|) ↔
    (saved pre J P fallback preInitial N t).1 = true ∧
      postHit post postInitial enabled J P B fallback γ N (saved pre J P fallback preInitial N t).2 t
  rw [hpre]
  by_cases hopen : (saved pre J P fallback preInitial N t).1 = true
  · by_cases hen : enabled.1 (saved pre J P fallback preInitial N t).2 = true
    · have hs : saved pre J P fallback preInitial N t =
          (true,(saved pre J P fallback preInitial N t).2) := Prod.ext hopen rfl
      have he : (ForkCappedPolicy.post post postInitial enabled q₁ N).run (sourceA J P t)
          (saved pre J P fallback preInitial N t,t.2) =
          snapshot post postInitial J P N (saved pre J P fallback preInitial N t).2 t := by
        rw [hs]
        exact ForkCappedPolicy.post_open post postInitial enabled q₁ N _ hA _ t.2 hen
          (hlegal.branch t hgood hunit N hopen hen N).1 (hlegal.branch t hgood hunit N hopen hen N).2
      rw [he]
      simp only [postHit,hopen,hen,true_and]
    · have he := ForkCappedPolicy.post_closed post postInitial enabled q₁ N (sourceA J P t)
        (saved pre J P fallback preInitial N t,t.2) (by simp [hen])
      rw [he]
      simp [postHit,hopen,hen,not_lt.mpr hγ.le]
  · have he := ForkCappedPolicy.post_closed post postInitial enabled q₁ N (sourceA J P t)
      (saved pre J P fallback preInitial N t,t.2) (by simp [hopen])
    rw [he]
    simp [hopen,not_lt.mpr hγ.le]

def experimentLaw (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) (seedLaw : Measure Seed)
    (privateLaw : Measure Private) : Measure (Input d n r Seed Private) :=
  (cond (matrixLaw.prod seedLaw) (commonGood P J)).prod
    ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod privateLaw)

theorem experimentLaw_probability (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) [IsProbabilityMeasure matrixLaw]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    (hp : 0 < matrixLaw.real (MatrixKernelConcentration.sourceGoodEvent P J)) :
    IsProbabilityMeasure (experimentLaw (r := r) J P matrixLaw seedLaw privateLaw) := by
  have he : (matrixLaw.prod seedLaw) (commonGood P J) ≠ 0 := by
    intro hz
    have hmass := commonGood_mass P J matrixLaw seedLaw
    rw [measureReal_def,hz,ENNReal.toReal_zero] at hmass
    linarith
  letI : IsProbabilityMeasure (cond (matrixLaw.prod seedLaw) (commonGood P J)) :=
    cond_isProbabilityMeasure he
  unfold experimentLaw
  infer_instance

theorem experimentLaw_good_unit (J : ℕ) (hr : 0 < r)
    (P : Matrix (Fin d) (Fin d) ℝ)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) [IsProbabilityMeasure matrixLaw]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw] :
    ∀ᵐ t ∂experimentLaw (r := r) J P matrixLaw seedLaw privateLaw,
      t.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J ∧ ‖t.2.1‖ = 1 := by
  letI : NeZero r := ⟨hr.ne'⟩
  have hg : ∀ᵐ t ∂experimentLaw (r := r) J P matrixLaw seedLaw privateLaw,
      t.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J :=
    Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (commonGood_measurable P J))
  have hu : ∀ᵐ z ∂(SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod privateLaw,
      ‖z.1‖ = 1 := Measure.quasiMeasurePreserving_fst.ae SphereGaussian.sphereLaw_unit
  have hu' : ∀ᵐ t ∂experimentLaw (r := r) J P matrixLaw seedLaw privateLaw,
      ‖t.2.1‖ = 1 := Measure.quasiMeasurePreserving_snd.ae hu
  exact hg.and hu'

theorem compiled_probability_eq (pre : DisclosureCompiler.Program d PreState)
    (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ) (hr : 0 < r)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) (q₀ S q₁ N : ℕ)
    (hlegal : Legal (n := n) pre post preInitial postInitial enabled J P fallback q₀ S q₁)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) [IsProbabilityMeasure matrixLaw]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    {γ : ℝ} (hγ : 0 < γ) :
    conditionedHitProbability J P B fallback (compiledPre pre J P fallback preInitial N q₀ S)
      (ForkCappedPolicy.post post postInitial enabled q₁ N) matrixLaw seedLaw privateLaw γ =
    (experimentLaw (r := r) J P matrixLaw seedLaw privateLaw).real
      (cutoffHit pre post preInitial postInitial enabled J P B fallback γ N) := by
  apply measureReal_congr
  filter_upwards [experimentLaw_good_unit J hr P matrixLaw seedLaw privateLaw] with t ht
  exact propext (compiled_event_iff pre post preInitial postInitial enabled J hP B fallback q₀ S q₁ N
    hlegal hγ t ht.1 ht.2)

/-- The manuscript expression, with residual dimension `a=D-Q` and kernel
nullity `a-b`. Every previous disclosure contributes its polynomial degree to
`preBudget`; the post-mark test cap is `q₁+2`. -/
def bound (J q₀ S q₁ r a b : ℕ) (γ pE : ℝ) : ℝ :=
  (512*((a:ℝ)-b)/(γ^2*(r:ℝ)*pE))*
    ((preBudget J q₀ S:ℝ)+2*(r:ℝ)*q₁+2*r)/a +
    Real.exp (-Real.log (3/2:ℝ)*(r:ℝ))/pE

theorem cutoff_fork_bound (a b J q₀ S q₁ r : ℕ) (hb : b ≤ a) (ha : 0 < a)
    (hJ : 4 ≤ J) (hr : 0 < r)
    {P : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin (a+totalBudget J q₀ S r q₁)) ℝ}
    (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (fallback : Fin (a+totalBudget J q₀ S r q₁) → ℝ)
    (pre : DisclosureCompiler.Program (a+totalBudget J q₀ S r q₁) PreState)
    (post : MachineCompiler.Program (a+totalBudget J q₀ S r q₁) PostState
      (Fin (q₁+2) → EuclideanSpace ℝ (Fin (a+totalBudget J q₀ S r q₁))))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool)
    (hlegal : Legal (n := b+totalBudget J q₀ S r q₁)
      pre post preInitial postInitial enabled J P fallback q₀ S q₁)
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    {v : NNReal} (hv : v ≠ 0) {γ : ℝ} (hγ : 0 < γ) (hδ : 5*ReadoutFilter.delta ≤ γ/4)
    (hp : 0 < (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v).real
      (MatrixKernelConcentration.sourceGoodEvent P J)) (N : ℕ) :
    (experimentLaw (r := r) J P
      (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v)
      seedLaw privateLaw).real
      (cutoffHit pre post preInitial postInitial enabled J P B fallback γ N) ≤
    bound J q₀ S q₁ r a b γ
      ((iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v).real
        (MatrixKernelConcentration.sourceGoodEvent P J)) := by
  rw [← compiled_probability_eq pre post preInitial postInitial enabled J hr hP B fallback q₀ S q₁ N
    hlegal _ seedLaw privateLaw hγ]
  have h := finite_fork_probability_bound a b hb ha hJ hr hP B hB hPB fallback
    (compiledPre pre J P fallback preInitial N q₀ S)
    (ForkCappedPolicy.post post postInitial enabled q₁ N)
    (fun A state fresh j => ForkCappedPolicy.post_norm post postInitial enabled q₁ N A (state,fresh) j)
    seedLaw privateLaw hv hγ hδ hp
  simpa only [source_numerator, bound] using h

/-- Arbitrary internal computation is allowed. The event is eventual opening
followed by an actual selected-test hit, including a hit before a subsequent
nonterminating computation. No eventual probability estimate is an input. -/
theorem eventual_fork_bound (a b J q₀ S q₁ r : ℕ) (hb : b ≤ a) (ha : 0 < a)
    (hJ : 4 ≤ J) (hr : 0 < r)
    {P : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin (a+totalBudget J q₀ S r q₁)) ℝ}
    (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (fallback : Fin (a+totalBudget J q₀ S r q₁) → ℝ)
    (pre : DisclosureCompiler.Program (a+totalBudget J q₀ S r q₁) PreState)
    (post : MachineCompiler.Program (a+totalBudget J q₀ S r q₁) PostState
      (Fin (q₁+2) → EuclideanSpace ℝ (Fin (a+totalBudget J q₀ S r q₁))))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool)
    (hlegal : Legal (n := b+totalBudget J q₀ S r q₁)
      pre post preInitial postInitial enabled J P fallback q₀ S q₁)
    (hretain : RetainsTests post)
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    {v : NNReal} (hv : v ≠ 0) {γ : ℝ} (hγ : 0 < γ) (hδ : 5*ReadoutFilter.delta ≤ γ/4)
    (hp : 0 < (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v).real
      (MatrixKernelConcentration.sourceGoodEvent P J)) :
    (experimentLaw (r := r) J P
      (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v)
      seedLaw privateLaw).real
      (eventualHit pre post preInitial postInitial enabled J P B fallback γ) ≤
    bound J q₀ S q₁ r a b γ
      ((iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v).real
        (MatrixKernelConcentration.sourceGoodEvent P J)) := by
  let μ := experimentLaw (r := r) J P
    (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v) seedLaw privateLaw
  letI : IsProbabilityMeasure μ := experimentLaw_probability J P _ seedLaw privateLaw hp
  apply pre.eventualHit_bound (sourceA J P) (earlierReadout J P fallback)
    (fun t => preInitial.1 t.1.2) (postHit post postInitial enabled J P B fallback γ)
    (fun state t => postHit_mono post postInitial enabled J P B fallback hγ hretain state t) μ
  intro N
  exact cutoff_fork_bound a b J q₀ S q₁ r hb ha hJ hr hP B hB hPB fallback pre post
    preInitial postInitial enabled hlegal seedLaw privateLaw hv hγ hδ hp N

theorem cutoffHit_nullMeasurable (pre : DisclosureCompiler.Program d PreState)
    (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ) (hr : 0 < r)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) (q₀ S q₁ : ℕ)
    (hlegal : Legal (n := n) pre post preInitial postInitial enabled J P fallback q₀ S q₁)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) [IsProbabilityMeasure matrixLaw]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    {γ : ℝ} (hγ : 0 < γ) (N : ℕ) :
    NullMeasurableSet (cutoffHit pre post preInitial postInitial enabled J P B fallback γ N)
      (experimentLaw J P matrixLaw seedLaw privateLaw) := by
  apply (branchHit_measurable J P B fallback (compiledPre pre J P fallback preInitial N q₀ S)
    (ForkCappedPolicy.post post postInitial enabled q₁ N) γ).nullMeasurableSet.congr
  filter_upwards [experimentLaw_good_unit J hr P matrixLaw seedLaw privateLaw] with t ht
  exact propext (compiled_event_iff pre post preInitial postInitial enabled J hP B fallback q₀ S q₁ N
    hlegal hγ t ht.1 ht.2)

theorem eventualHit_nullMeasurable (pre : DisclosureCompiler.Program d PreState)
    (post : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ) (hr : 0 < r)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin d) (Fin r) ℝ) (q₀ S q₁ : ℕ)
    (fallback : Fin d → ℝ) {γ : ℝ} (hγ : 0 < γ) (hretain : RetainsTests post) :
    ∀ (_hlegal : Legal (n := n) pre post preInitial postInitial enabled J P fallback q₀ S q₁)
      (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) [IsProbabilityMeasure matrixLaw]
      (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
      (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw],
    NullMeasurableSet (eventualHit pre post preInitial postInitial enabled J P B fallback γ)
      (experimentLaw J P matrixLaw seedLaw privateLaw) := by
  intro hlegal matrixLaw _ seedLaw _ privateLaw _
  unfold eventualHit
  rw [pre.eventualHit_eq_iUnion _ _ _ _
    (fun state t => postHit_mono post postInitial enabled J P B fallback hγ hretain state t)]
  exact NullMeasurableSet.iUnion
    (fun N => cutoffHit_nullMeasurable pre post preInitial postInitial enabled J hr hP B fallback q₀ S q₁
      hlegal matrixLaw seedLaw privateLaw hγ N)

end
end GradientHessian.ForkMachineBound
