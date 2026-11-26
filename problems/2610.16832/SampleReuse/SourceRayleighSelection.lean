import SampleReuse.Descent
import SecondOrder.CurvatureMeasurability

/-! A Borel Rayleigh-witness implementation of the curvature test, retaining
the manuscript's exact certificate/witness threshold. The manuscript chooses
a minimum eigenvector; the convergence proof needs only this Rayleigh bound.
We do not identify the dense witness with a minimum eigenvector. -/

open MeasureTheory SecondOrder
open scoped InnerProductSpace Classical

namespace SampleReuse
noncomputable section

def sourceRayleighPred {d : ℕ} (a : ℝ) (H : Point d →L[ℝ] Point d) (n : ℕ) : Prop :=
  if n = 0 then RayleighCertificate a H else strictRayleigh (2 * a) H (denseProbe d (n - 1))

theorem exists_sourceRayleighPred {d : ℕ} (a : ℝ) (H : Point d →L[ℝ] Point d) :
    ∃ n, sourceRayleighPred a H n := by
  by_cases hc : RayleighCertificate a H
  · exact ⟨0, by simpa only [sourceRayleighPred, if_true] using hc⟩
  · have hv : ∃ v : Point d, ⟪H v, v⟫_ℝ < -a * ‖v‖^2 := by
      simpa only [RayleighCertificate, not_forall, not_le] using hc
    have ho : IsOpen {v : Point d | strictRayleigh (2 * a) H v} := by
      apply isOpen_lt <;> fun_prop
    obtain ⟨v, hv⟩ := hv
    have hm : strictRayleigh (2 * a) H v := by
      unfold strictRayleigh
      nlinarith
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (Point d)).exists_mem_open ho ⟨v, hm⟩
    exact ⟨n + 1, by simpa [sourceRayleighPred] using hn⟩

def sourceRayleighIndex {d : ℕ} (a : ℝ) (H : Point d →L[ℝ] Point d) : ℕ :=
  Nat.find (exists_sourceRayleighPred a H)

theorem sourceRayleighIndex_measurable {d : ℕ} (a : ℝ) :
    Measurable (sourceRayleighIndex (d := d) a) := by
  apply measurable_find
  intro n
  by_cases hn : n = 0
  · simpa only [sourceRayleighPred, if_pos hn] using (rayleighCertificate_closed (d := d) a).measurableSet
  · simpa only [sourceRayleighPred, if_neg hn] using
      strictRayleigh_measurableSet (2 * a) (denseProbe d (n - 1))

def sourceCurvatureSelector {d : ℕ} (a : ℝ) (H : Point d →L[ℝ] Point d) : CurvatureReply d :=
  if sourceRayleighIndex a H = 0 then .certificate
  else .negative (normalizeProbe (denseProbe d (sourceRayleighIndex a H - 1)))

def SourceCurvatureValid {d : ℕ} (a : ℝ) (H : Point d →L[ℝ] Point d) : CurvatureReply d → Prop
  | .certificate => RayleighCertificate a H
  | .negative v => ‖v‖ = 1 ∧ ⟪H v, v⟫_ℝ ≤ -a

theorem sourceCurvatureSelector_measurable {d : ℕ} (a : ℝ) :
    Measurable (sourceCurvatureSelector (d := d) a) :=
  (measurable_of_countable (fun n : ℕ => if n = 0 then CurvatureReply.certificate
    else .negative (normalizeProbe (denseProbe d (n - 1))))).comp (sourceRayleighIndex_measurable a)

theorem sourceCurvatureSelector_valid {d : ℕ} (a : ℝ) (H : Point d →L[ℝ] Point d) :
    SourceCurvatureValid a H (sourceCurvatureSelector a H) := by
  have hs : sourceRayleighPred a H (sourceRayleighIndex a H) := Nat.find_spec (exists_sourceRayleighPred a H)
  by_cases hn : sourceRayleighIndex a H = 0
  · simpa only [sourceCurvatureSelector, if_pos hn, SourceCurvatureValid,
      sourceRayleighPred, if_pos hn] using hs
  · have hv : strictRayleigh (2 * a) H (denseProbe d (sourceRayleighIndex a H - 1)) := by
      simpa only [sourceRayleighPred, if_neg hn] using hs
    have hnorm := strictRayleigh_normalize hv
    have he : -(2 * a) / 2 = -a := by ring
    simpa only [sourceCurvatureSelector, if_neg hn, SourceCurvatureValid, he] using hnorm

theorem sourceCurvatureSelector_certificate_iff {d : ℕ} (a : ℝ) (H : Point d →L[ℝ] Point d) :
    sourceCurvatureSelector a H = .certificate ↔ RayleighCertificate a H := by
  have hn : sourceRayleighIndex a H = 0 ↔ RayleighCertificate a H := by
    simp [sourceRayleighIndex, sourceRayleighPred]
  by_cases hc : RayleighCertificate a H
  · simp [sourceCurvatureSelector, hn.mpr hc, hc]
  · simp [sourceCurvatureSelector, mt hn.mp hc, hc]

theorem accurate_source_curvature {d : ℕ} {H Htrue : Point d →L[ℝ] Point d} {v : Point d} {γ : ℝ}
    (he : ‖H-Htrue‖ ≤ γ/4) (hv : ‖v‖ = 1) (hc : ⟪H v, v⟫_ℝ ≤ -(3*γ/4)) :
    ⟪Htrue v, v⟫_ℝ ≤ -γ/2 := by
  have herr : |⟪(H-Htrue) v, v⟫_ℝ| ≤ γ/4 := by
    calc
      _ ≤ ‖(H-Htrue) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H-Htrue‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right ((H-Htrue).le_opNorm v) (norm_nonneg v)
      _ ≤ γ/4 := by simpa only [hv, mul_one] using he
  have hl := (abs_le.mp herr).1
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left] at hl
  linarith

theorem source_selector_negative_population {d : ℕ} {f : Point d → ℝ} {x v : Point d}
    {H : Point d →L[ℝ] Point d} {γ : ℝ}
    (he : ‖H-hessian f x‖ ≤ γ/4)
    (hsel : sourceCurvatureSelector (3*γ/4) H = .negative v) :
    ‖v‖ = 1 ∧ ⟪hessian f x v, v⟫_ℝ ≤ -γ/2 := by
  have hv := sourceCurvatureSelector_valid (3*γ/4) H
  rw [hsel] at hv
  exact ⟨hv.1, accurate_source_curvature he hv.1 hv.2⟩

end
end SampleReuse
