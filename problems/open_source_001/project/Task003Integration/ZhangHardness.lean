import Task003Integration.ZhangPolicy
import Task003Integration.ZhangScale
import Task003Integration.ZhangMeasure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Task003Integration
open MeasureTheory Set Task003.OracleSimulation Task003.OracleReduction Task003.ZhangInterface
open Task003.StrictSourcePrior Task003.RegionalSourceBridge PaperGeometry

def zhangAdaptiveInput (d : ℕ) [NeZero d] (cp : ℝ) : Prop :=
  ∀ (k : ℕ) (hk : 0 < k),
    letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
    256 ≤ Module.finrank ℝ (ZhangPoint d) →
    (k:ℝ) ≤ (Module.finrank ℝ (ZhangPoint d):ℝ)/512 →
    ∀ T : ℕ, (T:ℝ) ≤ cp * Module.finrank ℝ (ZhangPoint d) * k / Real.log (Real.exp 1*k) →
    ∀ (S : Type) (mS : MeasurableSpace S), letI := mS
      ∀ q : Nonsmooth.Policy Unit S (ZhangBall d), q.IsMeasurable →
        3/4 ≤ (Nonsmooth.gaussianSupportPrior (ZhangPoint d) k).real
          {a : Nonsmooth.BoundedSupportRows (ZhangPoint d) (Fin k) |
            7*((1/4:ℝ)/Real.sqrt k)/16 <
              Nonsmooth.boundedFiniteSupport a
                (q.result (fun x => Nonsmooth.boundedFiniteSupport a x.val) () T).val -
                Nonsmooth.minimumValue 1 (Nonsmooth.boundedFiniteSupport a)}

theorem zhang_fixed_prior_hardness_of_adaptive
    (hHard : ∀ (d : ℕ) [NeZero d], zhangAdaptiveInput d (1/(65536*513))) :
    ZhangPrinciple 256 (1/512) (7/512) (1/(65536*513)) := by
  intro d hd k hk hkbound
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  intro N hN hbudget b _hcost
  let p := zhangStatePolicy b N
  have hp : p.IsMeasurable := zhangStatePolicy_measurable b N
  have hkd : (k:ℝ) ≤ (d:ℝ)/512 := by
    have hcast := (Nat.cast_le.mpr hkbound).trans (Nat.floor_le (by positivity : (0:ℝ)≤(1/512)*(d:ℝ)))
    linarith
  have hhard := (hHard d) k hk
    (by simpa only [finrank_euclideanSpace_fin] using hd)
    (by simpa only [finrank_euclideanSpace_fin] using hkd) N
    (by simpa only [finrank_euclideanSpace_fin] using hbudget.le)
    (Nonsmooth.HistoryStore (ZhangBall d)) inferInstance p hp
  let μ := Nonsmooth.gaussianSupportPrior (ZhangPoint d) k
  let S : Set (Fin k → Fin d → ℝ) := {rows | () ∈ strictSourceSuccessEvent b (sourceSupport rows) N
    (sourceAccuracy 1 (7/512) k)}
  have hS : MeasurableSet S :=
    (strictPriorSuccess_measurable b N (sourceAccuracy 1 (7/512) k)).preimage
      (measurable_id.prodMk measurable_const)
  let A : Set (Nonsmooth.BoundedSupportRows (ZhangPoint d) (Fin k)) :=
    {a | 7 * ((1/4:ℝ)/Real.sqrt (k:ℝ))/16 <
      Nonsmooth.boundedFiniteSupport a (p.result (fun x => Nonsmooth.boundedFiniteSupport a x.val) () N).val -
        Nonsmooth.minimumValue 1 (Nonsmooth.boundedFiniteSupport a)}
  have hA : (3/4:ℝ) ≤ μ.real A := hhard
  have hsub : A ⊆ (halfRows ⁻¹' S)ᶜ := by
    intro a ha hsucc
    have hf : (fun x => Nonsmooth.boundedFiniteSupport a x / 2) = sourceSupport (halfRows a) := by
      funext x
      exact (zhangHalfSupport a x).symm
    have hresult : (p.result (fun x => Nonsmooth.boundedFiniteSupport a x.val) () N).val =
        b.run (sourceSupport (halfRows a)) N () := by
      change ((zhangStatePolicy b N).result _ () N).val = _
      rw [zhangStatePolicy_result,hf]
    have hgap : sourceSupport (halfRows a) (b.run (sourceSupport (halfRows a)) N ()) -
        sourceOptimum (sourceSupport (halfRows a)) =
        (Nonsmooth.boundedFiniteSupport a (p.result
          (fun x => Nonsmooth.boundedFiniteSupport a x.val) () N).val -
          Nonsmooth.minimumValue 1 (Nonsmooth.boundedFiniteSupport a)) / 2 := by
      change sourceSupport (zhangHalfRows a) _ - sourceOptimum (sourceSupport (zhangHalfRows a)) = _
      rw [zhangHalfSupport,zhangHalfOptimum,hresult]
      ring
    change sourceSupport (halfRows a) (b.run (sourceSupport (halfRows a)) N ()) -
      sourceOptimum (sourceSupport (halfRows a)) < sourceAccuracy 1 (7/512) k at hsucc
    rw [hgap] at hsucc
    change 7 * ((1/4:ℝ)/Real.sqrt (k:ℝ))/16 < _ at ha
    dsimp [sourceAccuracy] at hsucc
    have hscale : 4*1*(7/512:ℝ)/Real.sqrt (k:ℝ) =
        (7*((1/4:ℝ)/Real.sqrt (k:ℝ))/16)/2 := by ring
    rw [hscale] at hsucc
    exact (not_lt_of_ge (div_le_div_of_nonneg_right ha.le (by norm_num))) hsucc
  have hcomp : (3/4:ℝ) ≤ μ.real (halfRows ⁻¹' S)ᶜ :=
    hA.trans (measureReal_mono hsub (measure_ne_top _ _))
  have hsum := measureReal_add_measureReal_compl (μ := μ) ((halfRows_measurable d k) hS)
  rw [probReal_univ] at hsum
  have hb : μ.real (halfRows ⁻¹' S) ≤ (1/4:ℝ) := by linarith
  change (PaperTruncatedGaussianRows.rowsLaw d k).real S ≤ _
  rw [← halfRows_map_law d k]
  unfold Measure.real
  rw [Measure.map_apply (halfRows_measurable d k) hS]
  exact hb

end Task003Integration
