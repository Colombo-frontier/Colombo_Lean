import Bilevel.PolishedTransportLocalSpaces
import Bilevel.TransportRoundNetworkObserver

/-! All source local/global energies on the same actual run event. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedTransportLocalSpaces
open EuclideanGaussian ProjectionGeometry TransportObserver TransportEdgePosterior
  OrthogonalAction TransportNetwork TransportRound TransportControllerMachine
set_option maxHeartbeats 1400000

def localRadius (n : ℕ) (e : ℝ) : ℝ := Real.sqrt (e/(34*batchFactor n))

theorem localRadius_pos (n : ℕ) {e : ℝ} (he : 0 < e) : 0 < localRadius n e := by
  have hF : 0 < batchFactor n := lt_of_lt_of_le zero_lt_one (batchFactor_ge_one n)
  exact Real.sqrt_pos.mpr (by positivity)

theorem localRadius_paid (n : ℕ) {e : ℝ} (he : 0 < e) :
    34*batchFactor n*energyTarget n (localRadius n e) ≤ e := by
  have hF : 0 < batchFactor n := lt_of_lt_of_le zero_lt_one (batchFactor_ge_one n)
  have h := mul_le_mul_of_nonneg_left (energyTarget_le_sq n (localRadius n e))
    (show 0 ≤ 34*batchFactor n by positivity)
  apply h.trans_eq
  rw [localRadius,Real.sq_sqrt (by positivity : 0 ≤ e/(34*batchFactor n))]
  field_simp

def MaximumGood {H : Type*} {n D p T : ℕ} (hT : T ≤ D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (M : ℕ) (e : ℝ) : Prop :=
  (∀ t ≤ M,runEnergy hT choose respond memory z t ≤ e) ∧
  ∀ t < M,
    let g := frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t
    let P := fun edge => runPairs hT choose respond (prefixNames n T) (memory,seed T hT z) z edge t
    TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) ≤ e ∧
    TransportRoundEnergy.total (known (execute g z)) (frame T hT z) (postFuture T t) ≤ e ∧
    ∀ edge : Edge n,
      let I := oldFuture T t (src edge)
      frameEnergy (sourceInitial hT t g z P edge) (frame T hT z (src edge)) I ≤ e ∧
      frameEnergy (destinationInitial hT t g z P edge) (frame T hT z (dst edge)) I ≤ e ∧
      frameEnergy (destinationForward hT t g z P edge) (frame T hT z (dst edge)) I ≤ e ∧
      frameEnergy (sourceReverse hT t g z P edge) (frame T hT z (src edge)) I ≤ e

theorem maximumGood_of_no_failure {H : Type*} {n D p T : ℕ}
    (hT : T ≤ D) (hn : 0 < n) (hpos : 0 < T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (M : ℕ) {e b : ℝ} (hb : 0 < b)
    (hpaid : 34*batchFactor n*energyTarget n b ≤ e)
    (hgood : ∀ t < M,¬runFailure hT (queryTolerance n p M b) choose respond memory z t) :
    MaximumGood hT choose respond memory z M e := by
  let target := energyTarget n b
  have htarget : 0 ≤ target := (energyTarget_pos n hb).le
  have hF := batchFactor_ge_one n
  have hstored : target ≤ e := by nlinarith
  have hfrozen : 2*target ≤ e := by nlinarith
  have hpost : 2*batchFactor n*target ≤ e := by nlinarith
  refine ⟨fun t ht => (run_energy_horizon hT hn hpos choose respond memory z M hb hgood t ht).trans hstored,?_⟩
  intro t ht
  dsimp only
  let g := frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t
  let P := fun edge => runPairs hT choose respond (prefixNames n T) (memory,seed T hT z) z edge t
  have hfr := frozen_energy_horizon hT hn hpos choose respond memory z M hb hgood t ht
  have hp := frozenAt_prefix hT hn choose respond memory z t
  have hpair := runPairs_frozen_included hT choose respond (prefixNames n T) (memory,seed T hT z) z
  have hPs (edge : Edge n) : domain (P edge) ≤ known g (src edge) := (hpair edge t).1
  have hPd (edge : Edge n) : range (P edge) ≤ known g (dst edge) := (hpair edge t).2
  have hP (edge : Edge n) : Supports (P edge) (z.2 edge) :=
    runPairs_supported hT choose respond (prefixNames n T) (memory,seed T hT z) z edge t
  have hbatchGood : ¬batchFailure hT t g z P := (not_or.mp (hgood t ht)).2
  have hbudget : batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) ≤ (1 : ℝ)/4096 := by
    apply (mul_le_mul_of_nonneg_left hfr (by linarith : 0 ≤ batchFactor n)).trans
    have h := energyTarget_budget n b
    convert h using 1
    dsimp only [roundFactor]
    ring
  have hZ : batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) ≤
      2*batchFactor n*target := by
    convert mul_le_mul_of_nonneg_left hfr (by linarith : 0 ≤ batchFactor n) using 1
    ring
  have h17Z : 17*(batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)) ≤ e := by
    have hh := mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℝ) ≤ 17)
    exact hh.trans (by convert hpaid using 1; ring)
  have hbatch := executed_batch_energy hT hn t g z P hP hPs hPd hp hbudget hbatchGood
  refine ⟨hfr.trans hfrozen,hbatch.trans (hZ.trans hpost),?_⟩
  intro edge
  have hl := executed_batch_local_energies hT hn t g z P hP hPs hPd hp hbudget hbatchGood edge
  exact ⟨hl.1.trans (hZ.trans hpost),hl.2.1.trans (hZ.trans hpost),
    hl.2.2.1.trans (hZ.trans hpost),hl.2.2.2.trans h17Z⟩

/-- Public finite dimension before the strategy, memory law or execution. -/
def maximumDimension (n p T M : ℕ) (e δ : ℝ) : ℕ :=
  geometryCap n p T M+residualRank n p T M (queryTolerance n p M (localRadius n e)) δ

theorem maximumDimension_ge_frame (n p T M : ℕ) (e δ : ℝ) : T ≤ maximumDimension n p T M e δ :=
  (geometryCap_ge_frame n p T M).trans (Nat.le_add_right _ _)

theorem actual_maximum_observer {n D T p k : ℕ} (H : Memory) (hT : T ≤ D)
    (hn : 0 < n) (hpos : 0 < T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (M : ℕ) {e : ℝ} (he : 0 < e)
    (hD : maximumDimension n p T M e (1/8) ≤ D) :
    ∃ G : Set (H × TransportNetworkAuxiliary.Sample n D k),MeasurableSet G ∧
      (7 : ℝ)/8 ≤ (ρ.prod (TransportNetworkAuxiliary.law n D k)).real G ∧
      ∀ s ∈ G,MaximumGood hT choose respond s.1 s.2.1 M e := by
  let b := localRadius n e
  let r := residualRank n p T M (queryTolerance n p M b) (1/8)
  let a := queryTolerance n p M b
  let μ := ρ.prod (TransportNetworkAuxiliary.law n D k)
  have hb : 0 < b := localRadius_pos n he
  have ha : 0 < a := queryTolerance_pos n p M hb
  have hdim : geometryCap n p T M+r ≤ D := hD
  have hp := actual_run_failure_probability (k := k) H hT hpos choose hc respond hr ρ M r
    (residualRank_pos _ _ _ _ _ _) a ha (geometryCap_query hdim) (geometryCap_edge hdim)
  have hbad : μ {s | (s.1,s.2.1) ∈ runFailureEvent hT a choose respond M} ≤ ENNReal.ofReal (1/8) :=
    hp.trans (calibrated_runBudget n p T M ha (by norm_num : (0 : ℝ) < 1/8))
  let B : Set (H × TransportNetworkAuxiliary.Sample n D k) :=
    {s | (s.1,s.2.1) ∈ runFailureEvent hT a choose respond M}
  have hB : MeasurableSet B := (runFailureEvent_measurable hT a choose hc respond hr M).preimage
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hreal : μ.real B ≤ 1/8 := by
    have hh := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1/8 : ℝ) ≠ ⊤) hbad
    simpa only [measureReal_def,ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/8)] using hh
  refine ⟨Bᶜ,hB.compl,?_,?_⟩
  · rw [measureReal_compl hB,measureReal_univ_eq_one]
    linarith
  · intro s hs
    apply maximumGood_of_no_failure hT hn hpos choose respond s.1 s.2.1 M hb (localRadius_paid n he)
    intro t ht hfail
    exact hs ⟨t,ht,hfail⟩

end Bilevel.PolishedTransportLocalSpaces
