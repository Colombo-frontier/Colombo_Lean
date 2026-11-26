import MatchingBounds1005.AlgorithmQueryTrace
import MatchingBounds1005.AnalyticReferenceParameters
import MatchingBounds1005.AnalyticTraceEvent
import MatchingBounds1005.FinalScalarCalibration

/-! The measurable compact geometry event forces every hidden query to stay
inside the polynomial core and the unqueried candidate to remain nonstationary. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
open scoped InnerProductSpace

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry

def disclosedSet (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K j : ℕ) : Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1)) :=
  Finset.univ.filter (fun i => (referenceParameters p t ht hs K).disclosure i ≤ j + 1)

def stoppedReadout (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K T : ℕ) (i : Fin (phaseCount (amplitudeConstant p) t - 1 + 1)) : ℕ :=
  min (T + 1) ((referenceParameters p t ht hs K).disclosure i - 1)

def queryGeometryEvent {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K T : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed) :=
  Model.geometryEvent (t ^ 3)⁻¹ A T (referenceParameters p t ht hs K).b
    (stoppedReadout p t ht hs K T) (2 * sourceAngle p t)

theorem queryGeometryEvent_measurable {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K T : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed) :
    MeasurableSet (queryGeometryEvent p t ht hs K T A) :=
  Model.geometryEvent_measurable _ _ _ _ _ _

theorem sourceReadouts_last (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d) :
    sourceReadouts p t ht hs K I (Fin.last (phaseCount (amplitudeConstant p) t - 1)) =
      tail p t ht hs K I := rfl

theorem last_disclosure (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ) :
    (referenceParameters p t ht hs K).disclosure (Fin.last (phaseCount (amplitudeConstant p) t - 1)) =
      calendarHorizon p t := by
  change (phaseCount (amplitudeConstant p) t - 1 + 1) * _ = _
  rw [Nat.sub_add_cancel (phase_pos p ht hs)]
  rfl

theorem geometryEvent_no_exit {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (hgeom : t ≤ geometryThreshold p) (K T : ℕ) (hT : T + 1 < calendarHorizon p t)
    (A : Model.Algorithm (dimension p t K) Seed)
    (z : (Rotation (Vec (dimension p t K)) × Seed) × (Fin T → Model.Response (dimension p t K)))
    (hz : z ∈ queryGeometryEvent p t ht hs K T A) :
    z ∉ traceExitEvent p t ht hs K A (disclosedSet p t ht hs K) T := by
  classical
  have hθ : 0 ≤ 2 * sourceAngle p t :=
    mul_nonneg (by norm_num) (geometricAngle_nonneg _ _ _)
  have hb := referenceParameters_readouts_orthonormal p t ht hs K
  have hbound (s : Fin (phaseCount (amplitudeConstant p) t - 1 + 1)) (i : Fin (T + 1))
      (hi : i.val < stoppedReadout p t ht hs K T s) :
      |⟪sourceReadouts p t ht hs K (rotationIso p t K z.1.1) s,
        Model.queryTrace (t ^ 3)⁻¹ A T (z.1.2, z.2) i⟫_ℝ| ≤ 2 * sourceAngle p t / t ^ 3 := by
    have h := Model.geometryEvent_physical_readout (by positivity : 0 < (t ^ 3)⁻¹) hθ
      A T (referenceParameters p t ht hs K).b (stoppedReadout p t ht hs K T) z hz s i hi
    rw [hb.norm_eq_one s, mul_one] at h
    simpa only [div_eq_mul_inv] using h
  have hq (j : Fin T) : rotationQuerySafe p t ht hs K A (disclosedSet p t ht hs K) j.val z.1
      (fun i => z.2 ⟨i.val, i.isLt.trans j.isLt⟩) := by
    intro s hhidden
    have hdis : ¬ (referenceParameters p t ht hs K).disclosure s ≤ j.val + 1 := by
      simpa only [disclosedSet, Finset.mem_filter, Finset.mem_univ, true_and] using hhidden
    have hi : j.castSucc.val < stoppedReadout p t ht hs K T s := by
      change j.val < min (T + 1) ((referenceParameters p t ht hs K).disclosure s - 1)
      apply lt_min <;> omega
    have h := (hbound s j.castSucc hi).trans (sourceAngle_readout_thresholds p t ht hgeom).1
    simpa only [Model.queryTrace_query] using h
  have ho : rotationOutputSafe p t ht hs K A T z.1 z.2 := by
    let s := Fin.last (phaseCount (amplitudeConstant p) t - 1)
    have hi : (Fin.last T).val < stoppedReadout p t ht hs K T s := by
      unfold stoppedReadout
      rw [last_disclosure]
      apply lt_min <;> simp only [Fin.val_last] <;> omega
    have h := (hbound s (Fin.last T) hi).trans (sourceAngle_readout_thresholds p t ht hgeom).2
    simpa only [s, sourceReadouts_last, Model.queryTrace_output] using h
  rintro (⟨j, hj⟩ | ho')
  · exact hj (hq j)
  · exact ho' ho

end MatchingBounds1005.AnalyticFamily
