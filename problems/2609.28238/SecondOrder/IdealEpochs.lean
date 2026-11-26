import SecondOrder.EpochPartition
import SecondOrder.MeasurableCapping

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def idealPath {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (t : ℕ) : IdealState d :=
  idealRun L s policy t (fun i => w i.val)

theorem idealPath_succ {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (t : ℕ) :
    idealPath L s policy w (t+1) =
      idealStep L s (idealPath L s policy w t) (policy t (fun i => w i.val) (idealPath L s policy w t)) (w t) := rfl

def isGradientMove {d : ℕ} (z : IdealState d) (a : IdealMove d) : Bool :=
  if z.running then
    match a with
    | .gradient _ => true
    | _ => false
  else false

def idealGradientFlag {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (t : ℕ) : Bool :=
  let z := idealPath L s policy w t
  isGradientMove z (policy t (fun i => w i.val) z)

theorem idealStep_gradientMoves {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool) :
    (idealStep L s z a b).gradientMoves = z.gradientMoves+if isGradientMove z a then 1 else 0 := by
  cases hz : z.running <;> cases a <;> simp [idealStep,isGradientMove,hz]

theorem idealGradientFlag_count {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (t : ℕ) :
    gradientCount (idealGradientFlag L s policy w) t = (idealPath L s policy w t).gradientMoves := by
  induction t with
  | zero => rfl
  | succ t ih => rw [gradientCount,idealPath_succ,idealStep_gradientMoves,ih]; rfl

/-- Extend finite signs only to express one consistent sequence of past
move types. The first M execution steps never inspect the padded signs. -/
def extendSigns {M : ℕ} (w : Fin M → Bool) (t : ℕ) : Bool := if ht : t < M then w ⟨t,ht⟩ else false

theorem idealPath_extendSigns {d M : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : Fin M → Bool) :
    idealPath L s policy (extendSigns w) M = idealRun L s policy M w := by
  unfold idealPath
  congr 1
  funext i
  simp [extendSigns,i.isLt]

def idealAnchorCount {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d) (w : Fin M → Bool) : ℕ :=
  epochAnchorCount q (idealGradientFlag L s policy (extendSigns w)) M

theorem idealAnchorCount_eq {d M q : ℕ} (hq : 0 < q) (L s : ℝ) (policy : IdealPolicy d) (w : Fin M → Bool) :
    idealAnchorCount q L s policy w = 1+(idealRun L s policy M w).gradientMoves/q := by
  rw [idealAnchorCount,epochAnchorCount_eq hq,idealGradientFlag_count,idealPath_extendSigns]

theorem idealAnchorCount_bound {d M q : ℕ} (hq : 0 < q) (L s : ℝ) (policy : IdealPolicy d) (w : Fin M → Bool) :
    (idealAnchorCount q L s policy w : ℝ) ≤ 1+((idealRun L s policy M w).gradientMoves : ℝ)/(q : ℝ) := by
  have hh := epochAnchorCount_bound hq (idealGradientFlag L s policy (extendSigns w)) M
  simpa only [idealGradientFlag_count,idealPath_extendSigns] using hh

theorem idealAnchorCount_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d q : ℕ}
    (hq : 0 < q) (L s : ℝ) {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M : ℕ) :
    Measurable (fun w : Ξ × (Fin M → Bool) => idealAnchorCount q L s (policy w.1) w.2) := by
  simp_rw [idealAnchorCount_eq hq]
  have hz := state_measurable_fields.mp (idealRun_measurable L s hm M)
  exact (measurable_of_countable (fun n : ℕ => 1+n/q)).comp hz.2.2.1

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.measurableIdealRun_gradient_count (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) :
    let count := fun w : Ξ × (Fin M → Bool) =>
      ((idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).gradientMoves : ℝ)
    Integrable count (η.prod (signLaw M)) ∧
      (∫ w, count w ∂η.prod (signLaw M)) ≤ P.gap*P.gradientLip/τ^2 := by
  have hz := state_measurable_fields.mp
    (idealRun_measurable P.gradientLip (curvatureRadius P.hessianHolder ν γ) hm M)
  exact mixed_sign_mean_bound
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hz.2.2.1)
    (fun _ => Nat.cast_nonneg _) (fun ξ => (h.idealRun_statistics hτ hγ (policy ξ) (hv ξ) M).1)

/-- The expected number of actual initial/refresh anchors is controlled
by gradient moves alone; curvature moves cannot trigger extra resets. -/
theorem CommonLoss.idealAnchorCount_integral (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) :
    let count := fun w : Ξ × (Fin M → Bool) =>
      (idealAnchorCount q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 : ℝ)
    Integrable count (η.prod (signLaw M)) ∧
      (∫ w, count w ∂η.prod (signLaw M)) ≤ 1+(P.gap*P.gradientLip/τ^2)/(q : ℝ) := by
  dsimp only
  have hg := h.measurableIdealRun_gradient_count (η := η) hτ hγ hm hv M
  have hm' := (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (idealAnchorCount_measurable hq P.gradientLip (curvatureRadius P.hessianHolder ν γ) hm M)
  have he := (integrable_const (1 : ℝ)).add (hg.1.div_const (q : ℝ))
  have hi : Integrable (fun w : Ξ × (Fin M → Bool) =>
      (idealAnchorCount q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 : ℝ))
      (η.prod (signLaw M)) := by
    apply he.mono' hm'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    change ‖(idealAnchorCount q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 : ℝ)‖ ≤ _
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact idealAnchorCount_bound hq _ _ _ _
  refine ⟨hi, ?_⟩
  have hb := integral_mono hi he (fun w => idealAnchorCount_bound hq P.gradientLip
    (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2)
  refine hb.trans ?_
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) (hg.1.div_const _),integral_div]
  simp only [integral_const,measureReal_univ_eq_one,one_smul]
  exact add_le_add_left (div_le_div_of_nonneg_right hg.2 (Nat.cast_nonneg q)) 1

end
end SecondOrder
