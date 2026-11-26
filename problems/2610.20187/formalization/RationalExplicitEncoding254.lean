import RationalExplicitOnline254
import RationalRunWork254
import RationalParameterEncoding254
import MasterBitCertificate254

noncomputable section
namespace Paper254
namespace ExplicitRationalSparseInput
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (I : ExplicitRationalSparseInput d T D G eta W)

/-- Initial encodings and the two oracle interfaces suffice for the same
deterministically tuned learner; no evolved-state height is an input. -/
def encodingSetup (b L0 c degree responseHorizon : ℕ) (hbv : b≤I.v)
    (hmean : RationalVectorBits I.initial_mean b)
    (hhi : RationalHeight I.hi b) (hlam : RationalHeight I.lam b)
    (hproj : ProjectionEncodingSpec I.oracle L0 c degree)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : ℕ → Loss d)
    (hgrad : ∀ t<responseHorizon, RationalVectorBits ((I.construction.forLosses oracle hspec f).gradient t) L0) :
    RationalRunEncodingSetup (I.construction.forLosses oracle hspec f) := by
  let r := explicitSparseHistoryPrecision d I.s I.v
  let B := b+2*(scaleCount T+1)+1
  have hlo (j : Fin (scaleCount T+1)) : RationalHeight (I.lo j) B :=
    rationalCappedVariance_height I.hi b (scaleCount T) j.val hhi (by omega)
  have hhiB : RationalHeight I.hi B := hhi.mono (by dsimp [B]; omega)
  have hc (j : Fin (scaleCount T+1)) :=
    uniformHistoryParameters_height I.v I.v r r B (I.lo j) I.hi (hlo j) hhiB
  refine {
    L0 := L0
    c := c
    degree := degree
    v := I.v
    storage := 3*I.v+I.v+r+6
    projection := r
    initialBits := b
    liveLog := I.v
    parameterBits := B+3*I.v+I.v+2*r+10
    responseHorizon := responseHorizon
    projection_encoding := hproj
    storage_bound := fun j => le_rfl
    projection_bound := fun j => le_rfl
    initial_magnitude := ?_
    dimension_bound := I.dimension_bound
    diameter_bound := I.diameter_bound
    hi_bound := I.hi_bound
    lo_inverse_bound := I.scale_inverse_bound
    gradient_magnitude := I.gradient_bound
    rate_magnitude := I.lam_bound
    initial_mean_bits := hmean
    initial_covariance_height := hhi
    live_bound := ?_
    gradient_encoding := hgrad
    rate_height := hlam.mono (by dsimp [B]; omega)
    smoothing_height := fun j => (hc j).1
    lower_height := fun j => (hc j).2.1
    upper_height := fun j => (hc j).2.2 }
  · intro j
    have hh := RationalHeight.of_bits (I.initial_mean j) b (hmean j).1 (hmean j).2
    exact hh.real_abs.trans (pow_le_pow_right₀ (by norm_num) hbv)
  · exact_mod_cast I.live_bound

theorem encoded_history_work (b L0 c degree responseHorizon : ℕ) (hbv : b≤I.v)
    (hmean : RationalVectorBits I.initial_mean b)
    (hhi : RationalHeight I.hi b) (hlam : RationalHeight I.lam b)
    (hproj : ProjectionEncodingSpec I.oracle L0 c degree)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : ℕ → Loss d)
    (hgrad : ∀ t<responseHorizon, RationalVectorBits ((I.construction.forLosses oracle hspec f).gradient t) L0)
    (t : ℕ) (ht : t<responseHorizon) (e : Fin ((T+1)*(scaleCount T+1))) :
    let C := I.construction.forLosses oracle hspec f
    let E := I.encodingSetup b L0 c degree responseHorizon hbv hmean hhi hlam hproj oracle hspec f hgrad
    HistoryWorkHeights C.oracle (C.allCfg e) ((C.run t).histories e) C.lam
      (C.gradient t) (C.prediction t)
      (historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree (C.allCfg e)) :=
  (I.encodingSetup b L0 c degree responseHorizon hbv hmean hhi hlam hproj oracle hspec f hgrad).history_work_heights t ht e

end ExplicitRationalSparseInput
end Paper254
#print axioms Paper254.ExplicitRationalSparseInput.encoded_history_work
