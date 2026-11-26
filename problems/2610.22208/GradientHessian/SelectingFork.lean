import GradientHessian.MarkedLifetime
import GradientHessian.TestSelectionMachine

/-!
# Fork and lifetime bounds for arbitrary bounded test selection

The original machine has a separate, uncharged select step and may compute
forever. Its selections are recorded without changing its original state,
query vectors, replies, or product count. No retention assumption is imposed
on the original machine.
-/

namespace GradientHessian.SelectingFork

open Matrix MeasureTheory LowRank OracleComposition ForkMachineBound ForkChronologicalProbability
open scoped InnerProductSpace ENNReal
noncomputable section

variable {d n r s : ℕ} {Seed PreState PostState Private : Type*}
  [MeasurableSpace Seed] [MeasurableSpace PreState] [MeasurableSpace PostState]
  [MeasurableSpace Private]

def recordInitial (s : ℕ)
    (initial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState) :
    MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private))
      (PostState × TestRegister.Register s (EuclideanSpace ℝ (Fin d))) :=
  ⟨fun t => (initial.1 t,TestRegister.empty),initial.2.prodMk measurable_const⟩

structure LegalSelections (pre : DisclosureCompiler.Program d PreState)
    (post : TestSelectionMachine.Program d PostState)
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ) (q₀ S q₁ s : ℕ) : Prop where
  preprocessing : ∀ t : Input d n r Seed Private,
    t.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J → ∀ N,
    pre.ordinaryCalls (sourceA J P t) (earlierReadout J P fallback t) N (preInitial.1 t.1.2) ≤ q₀ ∧
    pre.disclosures (sourceA J P t) (earlierReadout J P fallback t) N (preInitial.1 t.1.2) ≤ S
  branch : ∀ t : Input d n r Seed Private,
    t.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J → ‖t.2.1‖ = 1 → ∀ N,
    (saved pre J P fallback preInitial N t).1 = true →
    enabled.1 (saved pre J P fallback preInitial N t).2 = true → ∀ M,
    post.queryCount (sourceA J P t) M
      (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2)) ≤ q₁ ∧
    post.selections (sourceA J P t) M
      (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2)) ≤ s ∧
    (post.mode (post.run (sourceA J P t) M
      (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2))) = 3 →
      ‖post.test (post.run (sourceA J P t) M
        (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2)))‖ ≤ 1)

theorem record_legal (pre : DisclosureCompiler.Program d PreState)
    (post : TestSelectionMachine.Program d PostState)
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ) (q₀ S q₁ s : ℕ)
    (hlegal : LegalSelections (n := n) pre post preInitial postInitial enabled J P fallback q₀ S q₁ s) :
    Legal (n := n) pre (post.record s) preInitial (recordInitial s postInitial)
      enabled J P fallback q₀ S q₁ := by
  refine ⟨hlegal.preprocessing,?_⟩
  intro t ht hu N hopen hen M
  constructor
  · change (post.record s).calls (fun v => sourceA J P t*ᵥv) M
      (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2),TestRegister.empty) ≤ q₁
    rw [post.record_calls]
    exact (hlegal.branch t ht hu N hopen hen M).1
  · intro j
    exact post.record_norm s (sourceA J P t) M
      (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2))
      (fun i _ hi => (hlegal.branch t ht hu N hopen hen i).2.2 hi) j

theorem record_retains (post : TestSelectionMachine.Program d PostState) (s : ℕ) :
    RetainsTests (post.record s) :=
  fun A state i hi => ⟨i,post.record_retains s A state i hi⟩

/-- A hit is defined by an actual select instruction in the original machine,
including an arbitrary unqueried selected vector. Hidden hit information is
absent from every machine transition. -/
def selectedHit (pre : DisclosureCompiler.Program d PreState)
    (post : TestSelectionMachine.Program d PostState)
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (γ : ℝ) : Set (Input d n r Seed Private) :=
  {t | ∃ N, (saved pre J P fallback preInitial N t).1 = true ∧
    enabled.1 (saved pre J P fallback preInitial N t).2 = true ∧
    ∃ M, post.mode (post.run (sourceA J P t) M
      (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2))) = 3 ∧
    γ < |⟪UnmarkedReadout.sourceOutput J P t.1.1 B fallback t.2.1,
      post.test (post.run (sourceA J P t) M
        (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2)))⟫_ℝ|}

theorem recorded_event_iff (pre : DisclosureCompiler.Program d PreState)
    (post : TestSelectionMachine.Program d PostState)
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (q₀ S q₁ s : ℕ)
    (hlegal : LegalSelections (n := n) pre post preInitial postInitial enabled J P fallback q₀ S q₁ s)
    {γ : ℝ} (hγ : 0 < γ) (t : Input d n r Seed Private)
    (hgood : t.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J) (hunit : ‖t.2.1‖ = 1) :
    t ∈ eventualHit pre (post.record s) preInitial (recordInitial s postInitial) enabled J P B fallback γ ↔
    t ∈ selectedHit pre post preInitial postInitial enabled J P B fallback γ := by
  let R := fun y : EuclideanSpace ℝ (Fin d) =>
    γ < |⟪UnmarkedReadout.sourceOutput J P t.1.1 B fallback t.2.1,y⟫_ℝ|
  have hz : ¬R 0 := by simpa only [R,inner_zero_right,abs_zero] using not_lt.mpr hγ.le
  have he N (hopen : (saved pre J P fallback preInitial N t).1=true)
      (hen : enabled.1 (saved pre J P fallback preInitial N t).2=true) :=
    post.recorded_ever_iff s (sourceA J P t)
      (postInitial.1 ((saved pre J P fallback preInitial N t).2,t.2))
      (fun M => (hlegal.branch t hgood hunit N hopen hen M).2.1) R hz
  constructor
  · rintro ⟨N,hopen,M,hen,j,hj⟩
    exact ⟨N,hopen,hen,(he N hopen hen).mp ⟨M,j,hj⟩⟩
  · rintro ⟨N,hopen,hen,M,hm,hhit⟩
    obtain ⟨M',j,hj⟩ := (he N hopen hen).mpr ⟨M,hm,hhit⟩
    exact ⟨N,hopen,M',hen,j,hj⟩

theorem recorded_probability_eq (pre : DisclosureCompiler.Program d PreState)
    (post : TestSelectionMachine.Program d PostState)
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool) (J : ℕ) (hr : 0 < r)
    (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (q₀ S q₁ s : ℕ)
    (hlegal : LegalSelections (n := n) pre post preInitial postInitial enabled J P fallback q₀ S q₁ s)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) [IsProbabilityMeasure matrixLaw]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    {γ : ℝ} (hγ : 0 < γ) :
    (experimentLaw J P matrixLaw seedLaw privateLaw).real
      (eventualHit pre (post.record s) preInitial (recordInitial s postInitial) enabled J P B fallback γ) =
    (experimentLaw J P matrixLaw seedLaw privateLaw).real
      (selectedHit pre post preInitial postInitial enabled J P B fallback γ) := by
  apply measureReal_congr
  filter_upwards [experimentLaw_good_unit J hr P matrixLaw seedLaw privateLaw] with t ht
  exact propext (recorded_event_iff pre post preInitial postInitial enabled J P B fallback q₀ S q₁ s
    hlegal hγ t ht.1 ht.2)

/-- The arbitrary-internal-time fork inequality for the original bounded
selection machine. Register persistence is derived by construction. -/
theorem arbitrary_selection_fork_bound (a b J q₀ S q₁ r : ℕ) (hb : b ≤ a) (ha : 0 < a)
    (hJ : 4 ≤ J) (hr : 0 < r)
    {P : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin (a+totalBudget J q₀ S r q₁)) ℝ}
    (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (fallback : Fin (a+totalBudget J q₀ S r q₁) → ℝ)
    (pre : DisclosureCompiler.Program (a+totalBudget J q₀ S r q₁) PreState)
    (post : TestSelectionMachine.Program (a+totalBudget J q₀ S r q₁) PostState)
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool)
    (hlegal : LegalSelections (n := b+totalBudget J q₀ S r q₁)
      pre post preInitial postInitial enabled J P fallback q₀ S q₁ (q₁+2))
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    {v : NNReal} (hv : v ≠ 0) {γ : ℝ} (hγ : 0 < γ) (hδ : 5*ReadoutFilter.delta ≤ γ/4)
    (hp : 0 < (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v).real
      (MatrixKernelConcentration.sourceGoodEvent P J)) :
    (experimentLaw (r := r) J P
      (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v)
      seedLaw privateLaw).real
      (selectedHit pre post preInitial postInitial enabled J P B fallback γ) ≤
    bound J q₀ S q₁ r a b γ
      ((iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁) v).real
        (MatrixKernelConcentration.sourceGoodEvent P J)) := by
  rw [← recorded_probability_eq pre post preInitial postInitial enabled J hr P B fallback
    q₀ S q₁ (q₁+2) hlegal _ seedLaw privateLaw hγ]
  exact eventual_fork_bound a b J q₀ S q₁ r hb ha hJ hr hP B hB hPB fallback
    pre (post.record (q₁+2)) preInitial (recordInitial (q₁+2) postInitial) enabled
    (record_legal pre post preInitial postInitial enabled J P fallback q₀ S q₁ (q₁+2) hlegal)
    (record_retains post (q₁+2)) seedLaw privateLaw hv hγ hδ hp

/-- Concrete source `cor:lifetime` for arbitrary measurable bounded test
selection, with actual prior-readout synthesis and unrestricted internal time.
The input premises contain only execution caps, test validity and source
parameters; no register-retention or success-probability premise is present. -/
theorem arbitrary_selection_lifetime (M r J κ q₀ S q₁ a b : ℕ)
    (hMsource : 1+4096*J^2 ≤ M) (hJ : ForkLifetime.depthThreshold ≤ J)
    (hr : ForkLifetime.rankRatio*(M:ℝ) ≤ r) (hκ : 18874368 ≤ κ)
    (hS : S ≤ M) (hq₀ : q₀ ≤ M*ForkLifetime.lifetime J+1)
    (hq₁ : q₁ ≤ ForkLifetime.lifetime J+1)
    (hab : κ*r+b=a) (hD : a+totalBudget J q₀ S r q₁=κ*r*J)
    {P : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin (a+totalBudget J q₀ S r q₁)) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank = r)
    (B : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (fallback : Fin (a+totalBudget J q₀ S r q₁) → ℝ)
    (pre : DisclosureCompiler.Program (a+totalBudget J q₀ S r q₁) PreState)
    (post : TestSelectionMachine.Program (a+totalBudget J q₀ S r q₁) PostState)
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool)
    (hlegal : LegalSelections (n := b+totalBudget J q₀ S r q₁)
      pre post preInitial postInitial enabled J P fallback q₀ S q₁ (q₁+2))
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw] :
    (experimentLaw (r := r) J P
      (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁)
        ((a+totalBudget J q₀ S r q₁:ℕ):NNReal)⁻¹) seedLaw privateLaw).real
      (selectedHit pre post preInitial postInitial enabled J P B fallback ForkLifetime.gamma) ≤ 1/256 ∧
    (ForkLifetime.lifetimeFraction/2)*(J:ℝ) ≤ ForkLifetime.lifetime J ∧
      1 ≤ (ForkLifetime.lifetimeFraction/2)*(J:ℝ) := by
  have h := MarkedLifetime.source_machine_lifetime M r J κ q₀ S q₁ a b hMsource hJ hr hκ
    hS hq₀ hq₁ hab hD hP hrank B hB hPB fallback pre (post.record (q₁+2))
    preInitial (recordInitial (q₁+2) postInitial) enabled
    (record_legal pre post preInitial postInitial enabled J P fallback q₀ S q₁ (q₁+2) hlegal)
    (record_retains post (q₁+2)) seedLaw privateLaw
  have hM : 1 ≤ M := by omega
  have hr0 : 0 < r := by
    have hMr := (ForkLifetime.source_parameters hM hJ hr).2.1
    omega
  rw [recorded_probability_eq pre post preInitial postInitial enabled J hr0 P B fallback
    q₀ S q₁ (q₁+2) hlegal _ seedLaw privateLaw ForkLifetime.gamma_pos] at h
  exact h

end
end GradientHessian.SelectingFork
