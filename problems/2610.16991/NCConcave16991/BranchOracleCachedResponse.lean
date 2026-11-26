import NCConcave16991.BranchOracleResponse
import NCConcave16991.BranchOracleMeasurable

/-! # Measurable complete replies from the actual public reply cache -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable {D : ℝ} (K : KnownDualDomain (dualDimension V) D)

abbrev CachedReplyInput := (SourceParameters V × OracleQuery n (primalDimension V) K) × GlobalActionCoordinates V

def renderCachedAnswer (d c μ : ℝ) (a : CachedReplyInput (n := n) V K) :
    OracleAnswer (primalDimension V) (dualDimension V) :=
  renderOracleAnswer V K a.1.1.1 a.1.1.2 d c μ a.1.2 (coordinateArray V a.2)

theorem queryGlobal_continuous : Continuous (queryGlobal (n := n) V K) :=
  (jointCoordinates V).symm.continuous.comp
    ((WithLp.prod_continuous_toLp 2 _ _).comp
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))

variable [MeasurableSpace (SourceParameters V)] [OpensMeasurableSpace (SourceParameters V)]
  [MeasurableSpace (GlobalHard.Joint V)] [BorelSpace (GlobalHard.Joint V)]
  [MeasurableSpace (GlobalActionCoordinates V)] [OpensMeasurableSpace (GlobalActionCoordinates V)]

theorem renderCachedAnswer_measurable (d c μ : ℝ) : Measurable (renderCachedAnswer (n := n) V K d c μ) := by
  let input : CachedReplyInput (n := n) V K → RendererInput V :=
    fun a ↦ ((a.1.1, queryGlobal V K a.1.2), a.2)
  have hi : Measurable input :=
    ((measurable_fst.comp measurable_fst).prodMk
      ((queryGlobal_continuous V K).measurable.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  have hj := (renderEncodedFirstJet_measurable (ι := Fin n) V d c μ).comp hi
  let post : ℝ × GlobalHard.Joint V → OracleAnswer (primalDimension V) (dualDimension V) :=
    fun a ↦ (a.1, ((jointCoordinates V a.2).fst, (jointCoordinates V a.2).snd))
  have hg : Continuous (fun a : ℝ × GlobalHard.Joint V ↦ jointCoordinates V a.2) :=
    (jointCoordinates V).continuous.comp continuous_snd
  have hp : Continuous post := continuous_fst.prodMk
    (((WithLp.fstL 2 ℝ _ _).continuous.comp hg).prodMk ((WithLp.sndL 2 ℝ _ _).continuous.comp hg))
  convert hp.measurable.comp hj using 1
  funext a
  rfl

end
end NCConcave16991.BranchOracle
