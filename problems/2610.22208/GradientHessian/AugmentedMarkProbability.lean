import GradientHessian.AugmentedHitContainment
import GradientHessian.RawFactorSeed
import GradientHessian.FactoredGeometricTests

/-! Future-mark repair bounds for the augmented disclosure policy. Both
initial and later public packets are replayed from the original external
factor, which retains the target matrix and all unrelated disclosed data. -/

noncomputable section
namespace GradientHessian.AugmentedMark
open Classical MeasureTheory HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState TaskSlots
  GeometricRepair ComparisonController ComparisonControllerReplay ControllerPolicyCoupling AugmentedPolicy AugmentedDisclosure
  Matrix LowRank
open DirectionPolicyReplay (Point)
open scoped InnerProductSpace

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
  (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t)
    (Ordinary d J E H t ell) (Rich d J E H t ell))

def query (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (w : RawMarkFactor.Rest d n r J E H t × Seed)
    (i : Fin (AugmentedVisibleQueries.cap (J := J) (ell := ell) t (leafNode leaf))) : EuclideanSpace ℝ (Fin d) :=
  BoundedNumericalTest.test (numericalProjection t (AugmentedVisibleQueries.query P B fallback t (blockMark leaf j)
    (markStop leaf j) (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j) 0 policy (leafNode leaf) K N fuel s₀ w i))

theorem query_measurable {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) (i) :
    Measurable (fun w => query (n := n) P B fallback t leaf j policy K N fuel s₀ w i) :=
  BoundedNumericalTest.test_contDiff.continuous.measurable.comp
    ((numericalProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) t).continuous.measurable.comp
      (AugmentedVisibleQueries.query_measurable P B fallback t (blockMark leaf j) (markStop leaf j)
        (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j) 0 policy (leafNode leaf) hK N fuel s₀ i))

theorem query_norm (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (w : RawMarkFactor.Rest d n r J E H t × Seed) (i) :
    ‖query P B fallback t leaf j policy K N fuel s₀ w i‖≤1 := BoundedNumericalTest.test_norm _

def arrayHit (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) (w : Raw d n r J E H t × Seed) : Prop :=
  ∃ i,1/3072 < |⟪UnmarkedReadout.sourceOutput J P (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).2.1 B fallback
      (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).1,
      query P B fallback t leaf j policy K N fuel s₀
        ((RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).2,w.2) i⟫_ℝ|

theorem hitBy_covered {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (hs : Ready s₀) (hell : 0<ell) (w : Raw d n r J E H t × Seed)
    (hhit : hitBy P B fallback t policy K (blockMark leaf j) (markStop leaf j) N fuel s₀ w) :
    arrayHit P B fallback t leaf j policy K N fuel s₀ w := by
  have hinit := hit_initial_open P B fallback t policy K (blockMark leaf j) (markStop leaf j) N fuel s₀ w hhit
  obtain ⟨i,hi,hh⟩ := hhit
  cases hq : trajectory P B fallback t policy K (blockMark leaf j) (markStop leaf j) N s₀ i w with
  | ready remaining a s => simp only [hq,BlockedHit] at hh
  | finished a s => simp only [hq,BlockedHit] at hh
  | pending remaining a output phase =>
    cases phase with
    | normal p s => simp only [hq,BlockedHit] at hh
    | delivered p before after => simp only [hq,BlockedHit] at hh
    | frozen p s => simp only [hq,BlockedHit] at hh
    | repairing p s =>
      rw [hq] at hh
      obtain ⟨_,act,hact,htrigger⟩ := hh
      have he : act=Action.futureMark leaf j := of_decide_eq_true hact
      subst act
      have hg : TaskState.current s=some leaf ∧ ¬GeometricDisclosure.MarkSupplied s leaf j ∧
          1/3072< |markReadout (assemble P B fallback t w.1) leaf j p.point| := of_decide_eq_true htrigger
      have hv : Visible (TaskState.retired s) (leafNode leaf) := ⟨leaf,hg.1,by intro k; rfl⟩
      have ht : shadowTrajectory P B fallback t policy (blockMark leaf j) (markStop leaf j)
          (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j) 0 K N s₀ i
          ((RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).2,w.2)=
            .pending remaining a output (.repairing p s) := by
        exact (mark_trajectory_eq P B fallback hK t leaf j w.1 _
          (by simp only [MeasurableEquiv.apply_symm_apply]) policy N s₀ hinit i w.2).symm.trans hq
      obtain ⟨q,hquery⟩ := AugmentedVisibleQueries.repairing_covered P B fallback t (blockMark leaf j) (markStop leaf j)
        (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j) 0 policy (leafNode leaf) K N fuel s₀ hs hell
        ((RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).2,w.2) i hi remaining a output p s ht hv
      refine ⟨q,?_⟩
      simp only [query,hquery]
      rw [← RawLeafFactor.leaf_a_mark_factor P B fallback t w.1 ((leafEquiv t).symm leaf) j]
      exact hg.2.2

variable [NeZero r] [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
  (σ : Measure Seed) [IsProbabilityMeasure σ]

theorem array_probability_bound (hJ : 4≤J) (hP : IsOrthogonalProjector P)
    (hB : Bᵀ*B=1) (hPB : P*B=B) {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (t+1) (4096*J^2+1) ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | arrayHit P B fallback t leaf j policy K N fuel s₀ w} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(1/8)*(1/3072:ℝ)^2*(r:ℝ))) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  letI := RawMarkFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  let e₀ := RawMarkFactor.factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t ((leafEquiv t).symm leaf) j
  have he := RawFactorSeed.factor_preserving e₀ (RawHierarchy.law P t)
    (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))) (RawMarkFactor.restLaw P t) σ
    (RawMarkFactor.factor_preserving P t ((leafEquiv t).symm leaf) j)
  have hX : ∀ᵐ w : RawMarkFactor.Rest d n r J E H t × Seed ∂(RawMarkFactor.restLaw P t).prod σ,
      w.1.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J :=
    Measure.quasiMeasurePreserving_fst.ae (RawMarkFactor.restLaw_matrix_good P t)
  have hb := FactoredTests.readout_list_bound hJ hP B hB hPB fallback (RawFactorSeed.factor e₀)
    ((RawHierarchy.law P t).prod σ) ((RawMarkFactor.restLaw P t).prod σ) he
    (fun w : RawMarkFactor.Rest d n r J E H t × Seed => w.1.1) (measurable_fst.comp measurable_fst) hX
    (AugmentedVisibleQueries.cap (J := J) (ell := ell) t (leafNode leaf))
    (query (n := n) P B fallback t leaf j policy K N fuel s₀)
    (query_measurable (n := n) P B fallback t leaf j policy hK N fuel s₀)
    (fun i => Filter.Eventually.of_forall (fun w => query_norm P B fallback t leaf j policy K N fuel s₀ w i))
    (by norm_num : (0:ℝ)<1/3072)
  simpa only [e₀,RawFactorSeed.factor_apply,arrayHit,AugmentedVisibleQueries.cap,leafNode,
    Nat.sub_self,pow_zero,one_mul] using hb

theorem shadow_probability (hJ : 4≤J) (hP : IsOrthogonalProjector P)
    (hB : Bᵀ*B=1) (hPB : P*B=B) {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (t+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | hitBy P B fallback t policy K (blockMark leaf j) (markStop leaf j) N fuel s₀ w} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(1/8)*(1/3072:ℝ)^2*(r:ℝ))) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  exact (measureReal_mono (fun w hw => hitBy_covered P B fallback t leaf j policy hK N fuel s₀ hs hell w hw)).trans
    (array_probability_bound P B fallback t leaf j policy σ hJ hP hB hPB hK N fuel s₀)

end GradientHessian.AugmentedMark
