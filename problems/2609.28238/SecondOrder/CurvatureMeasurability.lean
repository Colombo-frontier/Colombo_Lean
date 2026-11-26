import SecondOrder.RayleighProbe

open MeasureTheory
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def curvatureTag {d : ℕ} : CurvatureReply d → Bool
  | .certificate => false
  | .negative _ => true

def curvatureVector {d : ℕ} : CurvatureReply d → Point d
  | .certificate => 0
  | .negative u => u

def curvatureEncode {d : ℕ} (r : CurvatureReply d) : Bool × Point d :=
  (curvatureTag r,curvatureVector r)

theorem curvatureEncode_injective {d : ℕ} : Function.Injective (@curvatureEncode d) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [curvatureEncode, curvatureTag, curvatureVector]

instance curvatureReplyMeasurableSpace (d : ℕ) : MeasurableSpace (CurvatureReply d) :=
  MeasurableSpace.comap curvatureEncode inferInstance

theorem curvatureEncode_measurable {d : ℕ} : Measurable (@curvatureEncode d) :=
  comap_measurable _

theorem curvatureTag_measurable {d : ℕ} : Measurable (@curvatureTag d) :=
  measurable_fst.comp curvatureEncode_measurable

theorem curvatureVector_measurable {d : ℕ} : Measurable (@curvatureVector d) :=
  measurable_snd.comp curvatureEncode_measurable

theorem curvature_measurable_iff {X : Type*} [MeasurableSpace X] {d : ℕ}
    {r : X → CurvatureReply d} : Measurable r ↔ Measurable (fun x => curvatureEncode (r x)) := by
  constructor
  · intro hr
    exact curvatureEncode_measurable.comp hr
  · intro hr s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hr ht

theorem curvatureNegative_measurable {d : ℕ} : Measurable (@CurvatureReply.negative d) := by
  rw [curvature_measurable_iff]
  exact measurable_const.prodMk measurable_id

def RayleighReplyValid {d : ℕ} (γ : ℝ) (H : Point d →L[ℝ] Point d) : CurvatureReply d → Prop
  | .certificate => RayleighCertificate γ H
  | .negative u => ‖u‖ = 1 ∧ ⟪H u,u⟫_ℝ ≤ -γ/2

theorem rayleighReplyValid_iff {d : ℕ} (γ : ℝ) (H : Point d →L[ℝ] Point d) (r : CurvatureReply d) :
    RayleighReplyValid γ H r ↔
      (curvatureTag r = false ∧ RayleighCertificate γ H) ∨
      (curvatureTag r = true ∧ ‖curvatureVector r‖ = 1 ∧
        ⟪H (curvatureVector r),curvatureVector r⟫_ℝ ≤ -γ/2) := by
  cases r <;> simp [RayleighReplyValid, curvatureTag, curvatureVector]

theorem rayleighReplyValid_measurableSet {X : Type*} [MeasurableSpace X] {d : ℕ}
    (γ : ℝ) {H : X → Point d →L[ℝ] Point d} {r : X → CurvatureReply d}
    (hH : Measurable H) (hr : Measurable r) : MeasurableSet {x | RayleighReplyValid γ (H x) (r x)} := by
  simp only [rayleighReplyValid_iff, Set.setOf_or, Set.setOf_and]
  have ht := curvatureTag_measurable.comp hr
  have hu := curvatureVector_measurable.comp hr
  have hHu : Measurable (fun x => H x (curvatureVector (r x))) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp (hH.prodMk hu)
  have hq : Measurable (fun x => ⟪H x (curvatureVector (r x)),curvatureVector (r x)⟫_ℝ) :=
    (continuous_fst.inner continuous_snd).measurable.comp (hHu.prodMk hu)
  exact ((ht (measurableSet_singleton false)).inter ((rayleighCertificate_closed γ).measurableSet.preimage hH)).union
    ((ht (measurableSet_singleton true)).inter
      ((measurableSet_eq_fun hu.norm measurable_const).inter
        (measurableSet_le hq measurable_const)))

/-- A fixed countable-valued Borel selector. If the certificate holds it is
returned; otherwise a strict dense probe is normalized. This is analysis-only. -/
def measurableCurvature {d : ℕ} {γ : ℝ} (hγ : 0 < γ) (H : Point d →L[ℝ] Point d) : CurvatureReply d :=
  if rayleighIndex hγ H = 0 then .certificate
    else .negative (normalizeProbe (denseProbe d (rayleighIndex hγ H-1)))

theorem measurableCurvature_measurable {d : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    Measurable (measurableCurvature (d := d) hγ) :=
  (measurable_of_countable (fun n : ℕ => if n = 0 then CurvatureReply.certificate
    else .negative (normalizeProbe (denseProbe d (n-1))))).comp (rayleighIndex_measurable hγ)

theorem measurableCurvature_valid {d : ℕ} {γ : ℝ} (hγ : 0 < γ) (H : Point d →L[ℝ] Point d) :
    RayleighReplyValid γ H (measurableCurvature hγ H) := by
  have hs := rayleighIndex_spec hγ H
  by_cases hn : rayleighIndex hγ H = 0
  · simpa [measurableCurvature, hn, rayleighProbePred, RayleighReplyValid] using hs
  · have hv : strictRayleigh γ H (denseProbe d (rayleighIndex hγ H-1)) := by
      simpa [rayleighProbePred, hn] using hs
    simpa [measurableCurvature, hn, RayleighReplyValid] using strictRayleigh_normalize hv

theorem measurableCurvature_certificate_iff {d : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (H : Point d →L[ℝ] Point d) :
    measurableCurvature hγ H = .certificate ↔ RayleighCertificate γ H := by
  have hn : rayleighIndex hγ H = 0 ↔ RayleighCertificate γ H := by
    simp [rayleighIndex, rayleighProbePred]
  by_cases hc : RayleighCertificate γ H
  · simp [measurableCurvature, hn.mpr hc, hc]
  · simp [measurableCurvature, mt hn.mp hc, hc]

def measurableCorrectCurvature {d : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (H : Point d →L[ℝ] Point d) (r : CurvatureReply d) : CurvatureReply d :=
  if RayleighReplyValid γ H r then r else measurableCurvature hγ H

theorem measurableCorrectCurvature_valid {d : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (H : Point d →L[ℝ] Point d) (r : CurvatureReply d) :
    RayleighReplyValid γ H (measurableCorrectCurvature hγ H r) := by
  unfold measurableCorrectCurvature
  split
  · assumption
  · exact measurableCurvature_valid hγ H

theorem measurableCorrectCurvature_unchanged {d : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (H : Point d →L[ℝ] Point d) (r : CurvatureReply d) (hr : RayleighReplyValid γ H r) :
    measurableCorrectCurvature hγ H r = r := if_pos hr

theorem measurableCorrectCurvature_measurable {X : Type*} [MeasurableSpace X] {d : ℕ}
    {γ : ℝ} (hγ : 0 < γ) {H : X → Point d →L[ℝ] Point d} {r : X → CurvatureReply d}
    (hH : Measurable H) (hr : Measurable r) :
    Measurable (fun x => measurableCorrectCurvature hγ (H x) (r x)) :=
  Measurable.ite (rayleighReplyValid_measurableSet γ hH hr) hr
    ((measurableCurvature_measurable hγ).comp hH)

theorem population_measurableCurvature {d : ℕ} {F : Point d → ℝ} (hF : ContDiff ℝ 2 F)
    {γ : ℝ} (hγ : 0 < γ) : Measurable (fun x => measurableCurvature hγ (hessian F x)) :=
  (measurableCurvature_measurable hγ).comp (continuous_hessian hF).measurable

end
end SecondOrder
