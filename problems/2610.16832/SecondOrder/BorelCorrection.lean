import SecondOrder.ExecutionMeasurability
import SecondOrder.PhysicalCapping

open MeasureTheory
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

theorem correctVector_measurable {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ρ : X → ℝ} {target estimate : X → E} (hρ : Measurable ρ)
    (ht : Measurable target) (he : Measurable estimate) :
    Measurable (fun x => correctVector (ρ x) (target x) (estimate x)) :=
  Measurable.ite (measurableSet_le (he.sub ht).norm hρ) he ht

theorem validIdealMove_iff {d : ℕ} (F : Point d → ℝ) (τ γ : ℝ) (x : Point d) (a : IdealMove d) :
    ValidIdealMove F τ γ x a ↔
      (moveTag a = 0 ∧ ‖gradient F x‖ ≤ 10*τ ∧ RayleighCertificate γ (hessian F x)) ∨
      (moveTag a = 1 ∧ ‖moveVector a-gradient F x‖ ≤ τ ∧ 4*τ ≤ ‖moveVector a‖) ∨
      (moveTag a = 2 ∧ ‖moveVector a‖ = 1 ∧ ⟪hessian F x (moveVector a),moveVector a⟫_ℝ ≤ -γ/2) := by
  cases a <;> simp [ValidIdealMove, IsSOSP, moveTag, moveVector, RayleighCertificate]

theorem validIdealMove_measurableSet {X : Type*} [MeasurableSpace X] {d : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (τ γ : ℝ)
    {x : X → Point d} {a : X → IdealMove d} (hx : Measurable x) (ha : Measurable a) :
    MeasurableSet {w | ValidIdealMove F τ γ (x w) (a w)} := by
  have ht := moveTag_measurable.comp ha
  have hu := moveVector_measurable.comp ha
  have hg := (contDiff_gradient_one hF).continuous.measurable.comp hx
  have hH := (continuous_hessian hF).measurable.comp hx
  have hHu : Measurable (fun w => hessian F (x w) (moveVector (a w))) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp (hH.prodMk hu)
  have hq : Measurable (fun w => ⟪hessian F (x w) (moveVector (a w)),moveVector (a w)⟫_ℝ) :=
    (continuous_fst.inner continuous_snd).measurable.comp (hHu.prodMk hu)
  simp only [validIdealMove_iff, Set.setOf_or, Set.setOf_and]
  exact ((ht (measurableSet_singleton 0)).inter
    ((measurableSet_le hg.norm measurable_const).inter
      ((rayleighCertificate_closed γ).measurableSet.preimage hH))).union
    (((ht (measurableSet_singleton 1)).inter
      ((measurableSet_le (hu.sub hg).norm measurable_const).inter
        (measurableSet_le measurable_const hu.norm))).union
      ((ht (measurableSet_singleton 2)).inter
        ((measurableSet_eq_fun hu.norm measurable_const).inter (measurableSet_le hq measurable_const))))

def borelExactMove {d : ℕ} (F : Point d → ℝ) (τ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (x : Point d) : IdealMove d :=
  decideMove τ (gradient F x) (measurableCurvature hγ (hessian F x))

theorem borelExactMove_valid {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (x : Point d) :
    ValidIdealMove F τ γ x (borelExactMove F τ hγ x) := by
  apply decideMove_valid hτ
  · simp only [sub_self, norm_zero]
    linarith
  · intro hs
    have hc := measurableCurvature_valid hγ (hessian F x)
    cases he : measurableCurvature hγ (hessian F x) <;> rw [he] at hc <;> exact hc

theorem borelExactMove_measurable {d : ℕ} {F : Point d → ℝ} (hF : ContDiff ℝ 2 F)
    (τ : ℝ) {γ : ℝ} (hγ : 0 < γ) : Measurable (borelExactMove F τ hγ) :=
  decideMove_measurable τ (contDiff_gradient_one hF).continuous.measurable (population_measurableCurvature hF hγ)

/-- A measurable replacement of the earlier unrestricted exact-choice
correction. Only invalid physical proposals are changed. -/
def borelCorrectedPolicy {d : ℕ} (F : Point d → ℝ) (τ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (policy : IdealPolicy d) : IdealPolicy d :=
  fun t w z => if ValidIdealMove F τ γ z.point (policy t w z)
    then policy t w z else borelExactMove F τ hγ z.point

theorem borelCorrectedPolicy_valid {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (L s : ℝ) (policy : IdealPolicy d) :
    ValidIdealPolicy F L s τ γ (borelCorrectedPolicy F τ hγ policy) := by
  intro t w hr
  unfold borelCorrectedPolicy
  split
  · assumption
  · exact borelExactMove_valid F hτ hγ _

theorem borelCorrectedPolicy_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (τ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) :
    MeasurableIdealPolicy (fun ξ => borelCorrectedPolicy F τ hγ (policy ξ)) := by
  intro t
  have hp : Measurable (fun w : (Ξ × (Fin t → Bool)) × IdealState d => w.2.point) :=
    (state_measurable_fields.mp measurable_snd).1
  exact Measurable.ite (validIdealMove_measurableSet hF τ γ hp (hm t)) (hm t)
    ((borelExactMove_measurable hF τ hγ).comp hp)

theorem idealRun_borelCorrected_agrees {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hγ : 0 < γ) (L s : ℝ) (policy : IdealPolicy d) (t : ℕ) (w : Fin t → Bool)
    (hv : validHistory F L s τ γ policy t w) :
    idealRun L s (borelCorrectedPolicy F τ hγ policy) t w = idealRun L s policy t w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (Fin.init w) hv.1
    simp only [idealRun, hh]
    cases hr : (idealRun L s policy t (Fin.init w)).running
    · simp [idealStep, hr]
    · have ha := hv.2 hr
      simp only [borelCorrectedPolicy, if_pos ha]

theorem validHistory_measurableSet {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (L s τ γ : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (t : ℕ) :
    MeasurableSet {w : Ξ × (Fin t → Bool) | validHistory F L s τ γ (policy w.1) t w.2} := by
  induction t with
  | zero => exact MeasurableSet.univ
  | succ t ih =>
    have hp : Measurable (fun w : Ξ × (Fin (t+1) → Bool) => (w.1,Fin.init w.2)) :=
      measurable_fst.prodMk ((measurable_of_countable (fun w : Fin (t+1) → Bool => Fin.init w)).comp measurable_snd)
    have hz := (idealRun_measurable L s hm t).comp hp
    have hr := (state_measurable_fields.mp hz).2.1
    have hpos := (state_measurable_fields.mp hz).1
    have ha := (hm t).comp (hp.prodMk hz)
    have hv := validIdealMove_measurableSet hF τ γ hpos ha
    change MeasurableSet {w : Ξ × (Fin (t+1) → Bool) | validHistory F L s τ γ (policy w.1) t (Fin.init w.2) ∧
      ((idealRun L s (policy w.1) t (Fin.init w.2)).running = true →
        ValidIdealMove F τ γ (idealRun L s (policy w.1) t (Fin.init w.2)).point
          (policy w.1 t (Fin.init w.2) (idealRun L s (policy w.1) t (Fin.init w.2))))}
    simp only [imp_iff_not_or, Set.setOf_and, Set.setOf_or, ← Set.compl_setOf]
    exact (ih.preimage hp).inter ((hr (measurableSet_singleton true)).compl.union hv)

end
end SecondOrder
