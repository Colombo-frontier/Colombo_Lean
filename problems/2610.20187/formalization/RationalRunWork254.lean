import RationalInitialEncoding254
import RationalPredictionHeight254
import HistoryBitCertificate254

noncomputable section
namespace Paper254

/-- All fields describe initial inputs, numerical parameters or the two
oracle interfaces. No bound on an evolved state is assumed. -/
structure RationalRunEncodingSetup {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
    (C : RationalSparseConstruction d T K D G eta W) where
  L0 : ℕ
  c : ℕ
  degree : ℕ
  v : ℕ
  storage : ℕ
  projection : ℕ
  initialBits : ℕ
  liveLog : ℕ
  parameterBits : ℕ
  responseHorizon : ℕ
  projection_encoding : ProjectionEncodingSpec C.oracle L0 c degree
  storage_bound : ∀ j,(C.cfg j).storagePrecision≤storage
  projection_bound : ∀ j,(C.cfg j).projectionPrecision≤projection
  initial_magnitude : ∀ i,|(C.initial_mean i:ℝ)|≤(2:ℝ)^v
  dimension_bound : (d:ℝ)≤(2:ℝ)^v
  diameter_bound : D≤(2:ℝ)^v
  hi_bound : (C.hi:ℝ)≤(2:ℝ)^v
  lo_inverse_bound : ∀ j,(C.lo j:ℝ)⁻¹≤(2:ℝ)^v
  gradient_magnitude : G≤(2:ℝ)^v
  rate_magnitude : (C.lam:ℝ)≤(2:ℝ)^v
  initial_mean_bits : RationalVectorBits C.initial_mean initialBits
  initial_covariance_height : RationalHeight C.hi initialBits
  live_bound : (standardLiveCap T K:ℤ)≤(2:ℤ)^liveLog
  gradient_encoding : ∀ t<responseHorizon,RationalVectorBits (C.gradient t) L0
  rate_height : RationalHeight C.lam parameterBits
  smoothing_height : ∀ j,RationalHeight (C.cfg j).smoothing parameterBits
  lower_height : ∀ j,RationalHeight (C.cfg j).lowerThreshold parameterBits
  upper_height : ∀ j,RationalHeight (C.cfg j).upperThreshold parameterBits

namespace RationalRunEncodingSetup
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable {C : RationalSparseConstruction d T K D G eta W} (E : RationalRunEncodingSetup C)

def covarianceBits := max (E.initialBits+1) (3*E.v+E.storage+1)
def meanBits := max (E.initialBits+1) (E.c*(d+E.L0+6*E.v+E.storage+E.projection+6)^E.degree)
def weightBits := E.liveLog+C.master_precision+4
def predictionBits := standardLiveCap T K*(2*E.weightBits+2*E.meanBits+2)+1
def inputHeight := (d*d+1)*E.covarianceBits+(d+1)*E.meanBits+
  (d+1)*E.L0+(d+1)*E.predictionBits+E.parameterBits

theorem history_bits (t : ℕ) (e : Fin ((T+1)*(K+1))) :
    RationalMatrixBits ((C.run t).histories e).covariance E.covarianceBits ∧
      RationalVectorBits ((C.run t).histories e).mean E.meanBits := by
  exact C.run_history_bits E.L0 E.c E.degree E.v E.storage E.projection (E.initialBits+1)
    E.projection_encoding E.storage_bound E.projection_bound E.initial_magnitude E.dimension_bound
    E.diameter_bound E.hi_bound E.lo_inverse_bound E.gradient_magnitude E.rate_magnitude
    (rationalHistoryInitial_height C.initial_mean C.hi E.initialBits E.initial_covariance_height).reduced_bits
    (E.initial_mean_bits.mono (by omega)) t e

theorem weight_bits (t : ℕ) (e : Fin ((T+1)*(K+1))) :
    ((C.run t).weights e).num.natAbs.size≤E.weightBits ∧
      ((C.run t).weights e).den.size≤E.weightBits := by
  cases t with
  | succ t => exact C.run_weight_bits E.liveLog E.live_bound t e
  | zero =>
    have hK : (K+1:ℤ)≤(2:ℤ)^E.liveLog := by
      have hc : K+1≤standardLiveCap T K := by
        unfold standardLiveCap
        nlinarith
      have hci : (K+1:ℤ)≤(standardLiveCap T K:ℤ) := by exact_mod_cast hc
      exact hci.trans E.live_bound
    have hh := (numberedBirthPrior_height T K E.liveLog ⟨0,by omega⟩ hK).reduced_bits e 0
    change (numberedBirthPrior T K ⟨0,by omega⟩ e).num.natAbs.size≤_ ∧
      (numberedBirthPrior T K ⟨0,by omega⟩ e).den.size≤_
    exact ⟨hh.1.trans (by dsimp [weightBits]; omega),hh.2.trans (by dsimp [weightBits]; omega)⟩

theorem prediction_bits (t : ℕ) : RationalVectorBits (C.prediction t) E.predictionBits := by
  intro j
  have hw (e : Fin ((T+1)*(K+1))) : RationalHeight ((C.run t).weights e) (2*E.weightBits) := by
    have hh := canonical_matrix_height (fun _ _ : Fin 1=>(C.run t).weights e)
      (fun _ _=>E.weight_bits t e)
    simpa only [Nat.one_mul,Nat.reduceAdd] using hh
  have hm (e : Fin ((T+1)*(K+1))) (j : Fin d) :
      RationalHeight (((C.run t).histories e).mean j) (2*E.meanBits) := by
    have hh := canonical_matrix_height (fun _ _ : Fin 1=>((C.run t).histories e).mean j)
      (fun _ _=>(E.history_bits t e).2 j)
    simpa only [Nat.one_mul,Nat.reduceAdd] using hh
  have hh := rationalSparsePrediction_bits (C.run t) ((standardRationalSchedule T K).live t)
    (2*E.weightBits) (2*E.meanBits) (C.invariant t).support (fun e _=>hw e) (fun e _ j=>hm e j) j
  have hb := Nat.mul_le_mul_right (2*E.weightBits+2*E.meanBits+2)
    (standardRationalSchedule_uniform_card T K t)
  exact ⟨hh.1.trans (Nat.add_le_add_right hb 1),hh.2.trans (Nat.add_le_add_right hb 1)⟩

theorem history_input_height (t : ℕ) (hresponse : t<E.responseHorizon) (e : Fin ((T+1)*(K+1))) :
    HistoryInputHeight (C.allCfg e) ((C.run t).histories e) C.lam (C.gradient t) (C.prediction t)
      E.inputHeight := by
  let j := ((numberedExpertEquiv T K).symm e).2
  have hC := canonical_matrix_height _ (E.history_bits t e).1
  have hm := canonical_matrix_height (rationalColumn ((C.run t).histories e).mean)
    (fun i _=>(E.history_bits t e).2 i)
  have hg := canonical_matrix_height (rationalColumn (C.gradient t))
    (fun i _=>E.gradient_encoding t hresponse i)
  have hw := canonical_matrix_height (rationalColumn (C.prediction t)) (fun i _=>E.prediction_bits t i)
  simp only [Nat.mul_one] at hm hg hw
  refine ⟨hC.mono ?_,hm.mono ?_,E.rate_height.mono ?_,hg.mono ?_,hw.mono ?_,
    (E.smoothing_height j).mono ?_,(E.lower_height j).mono ?_,(E.upper_height j).mono ?_⟩
  all_goals dsimp [inputHeight]; omega

theorem history_work_heights (t : ℕ) (hresponse : t<E.responseHorizon) (e : Fin ((T+1)*(K+1))) :
    HistoryWorkHeights C.oracle (C.allCfg e) ((C.run t).histories e) C.lam
      (C.gradient t) (C.prediction t)
      (historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree (C.allCfg e)) := by
  let j := ((numberedExpertEquiv T K).symm e).2
  have hs := (C.invariant t).histories e
  have hg : ∀ i,|(C.gradient t i:ℝ)|≤G := by
    intro i
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun j=>(C.gradient t j:ℝ))) i).trans (C.gradient_bound t)
  have hsmall : |2*(C.lam:ℝ)*((fun i=>(C.gradient t i:ℝ)) ⬝ᵥ
      ((fun i=>(((C.run t).histories e).mean i:ℝ))-(fun i=>(C.prediction t i:ℝ))))|≤1/4 := by
    rw [C.lam_eq]
    exact coordinate_curvature_bound W C.diameter_pos C.gradient_pos C.curvature_pos _
      (C.gradient_bound t) ⟨_,hs.feasible⟩ ⟨_,C.prediction_feasible t⟩
  exact actual_history_work_heights C.dimension_pos W C.oracle C.oracle_spec E.L0 E.c E.degree
    E.projection_encoding (C.allCfg e) (C.allLo e) (C.hi:ℝ) G (C.lo_pos j) C.hi_pos
    C.gradient_pos.le (C.guards j) ((C.run t).histories e) hs C.lam C.lam_pos.le _ _
    (E.history_input_height t hresponse e) hg hsmall ⟨_,C.initial_feasible⟩ E.v E.initial_magnitude E.dimension_bound
    E.diameter_bound E.hi_bound (E.lo_inverse_bound j) E.gradient_magnitude E.rate_magnitude

end RationalRunEncodingSetup
end Paper254
#print axioms Paper254.RationalRunEncodingSetup.history_work_heights
