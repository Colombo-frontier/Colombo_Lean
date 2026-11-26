import SecondOrder.LocalEstimators

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

section JointBatches
variable {A Ω E : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {X : A × Ω → E}

theorem drawsSum_joint_measurable (hX : Measurable X) (n : ℕ) :
    Measurable (fun w : A × Draws Ω n => drawsSum (fun z => X (w.1,z)) n w.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).add
      (hX.comp (measurable_fst.prodMk measurable_snd.snd))

theorem drawsMean_joint_measurable (hX : Measurable X) (n : ℕ) :
    Measurable (fun w : A × Draws Ω n => drawsMean (fun z => X (w.1,z)) n w.2) :=
  (drawsSum_joint_measurable hX n).const_smul _

theorem drawsVector_joint_measurable (hX : Measurable X) (n : ℕ) :
    Measurable (fun w : A × Draws Ω n => drawsVector (fun z => X (w.1,z)) n w.2) := by
  induction n with
  | zero => exact measurable_pi_lambda _ (fun i => Fin.elim0 i)
  | succ n ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [drawsVector, Fin.snoc_last] using
        hX.comp (measurable_fst.prodMk measurable_snd.snd)
    · simpa only [drawsVector, Fin.snoc_castSucc] using
        ((measurable_pi_apply j).comp ih).comp (measurable_fst.prodMk measurable_snd.fst)

theorem robustBatch_joint_measurable (hX : Measurable X) (m : ℕ) {R : ℕ} (hR : 0 < R) (ρ : ℝ) :
    Measurable (fun w : A × Draws (Draws Ω m) R => robustBatch (fun z => X (w.1,z)) m hR ρ w.2) :=
  (robustCenter_measurable hR (ρ/3)).comp
    (drawsVector_joint_measurable (drawsMean_joint_measurable hX m) R)

theorem freshEstimate_joint_measurable (hX : Measurable X) (V ρ δ : ℝ) :
    Measurable (fun w : A × LocalDraws Ω V ρ δ => freshEstimate (fun z => X (w.1,z)) V ρ δ w.2) :=
  robustBatch_joint_measurable hX (localBatchSize V ρ) (confidenceRepeats_pos δ) ρ

end JointBatches

/-- Uniform fresh-sample slice bounds remain valid on every measurable
event determined by the past. This is stronger than an unconditional bound. -/
theorem fresh_event_past_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {η : Measure A} {μ : Measure B} [SFinite μ] {event : Set (A × B)}
    (he : MeasurableSet event) {δ : ℝ≥0∞}
    (hb : ∀ x, μ {y | (x,y) ∈ event} ≤ δ) {past : Set A} (hp : MeasurableSet past) :
    (η.prod μ) {w | w.1 ∈ past ∧ w ∈ event} ≤ δ*η past := by
  change (η.prod μ) ((Prod.fst ⁻¹' past) ∩ event) ≤ δ*η past
  rw [Measure.prod_apply ((hp.preimage measurable_fst).inter he)]
  calc
    _ ≤ ∫⁻ x, past.indicator (fun _ => δ) x ∂η := by
      apply lintegral_mono
      intro x
      change μ {y | x ∈ past ∧ (x,y) ∈ event} ≤ past.indicator (fun _ => δ) x
      by_cases hx : x ∈ past
      · simpa [hx] using hb x
      · simp [hx]
    _ = δ*η past := by rw [lintegral_indicator hp]; simp

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure A} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.anchor_joint_measurable (h : CommonLoss μ P ν F f) (ρ δ : ℝ) :
    Measurable (fun w : Point d × LocalDraws Ω (P.gradientNoise^2) ρ δ =>
      gradientAnchor P f w.1 ρ δ w.2) :=
  freshEstimate_joint_measurable (h.gradient_measurable.comp measurable_swap) _ _ _

theorem CommonLoss.adaptiveAnchor_measurable (h : CommonLoss μ P ν F f)
    {x : A → Point d} (hx : Measurable x) (ρ δ : ℝ) :
    Measurable (fun w : A × LocalDraws Ω (P.gradientNoise^2) ρ δ =>
      gradientAnchor P f (x w.1) ρ δ w.2) := by
  have hX : Measurable (fun w : A × Ω => gradient (f w.2) (x w.1)) :=
    h.gradient_measurable.comp (measurable_snd.prodMk (hx.comp measurable_fst))
  exact freshEstimate_joint_measurable hX (P.gradientNoise^2) ρ δ

/-- The point may be any measurable function of the entire past. Only the
new anchor samples are independent; no independence of the point is assumed. -/
theorem CommonLoss.adaptiveAnchor_past_confidence (h : CommonLoss μ P ν F f)
    {x : A → Point d} (hx : Measurable x) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    {past : Set A} (hp : MeasurableSet past) :
    (η.prod (localLaw μ (P.gradientNoise^2) ρ δ))
      {w | w.1 ∈ past ∧ ρ < ‖gradientAnchor P f (x w.1) ρ δ w.2-gradient F (x w.1)‖} ≤
      ENNReal.ofReal δ*η past := by
  have hg : Measurable (fun w : A × LocalDraws Ω (P.gradientNoise^2) ρ δ => gradient F (x w.1)) :=
    (contDiff_gradient_one h.population_smooth).continuous.measurable.comp (hx.comp measurable_fst)
  exact fresh_event_past_bound
    (measurableSet_lt measurable_const ((h.adaptiveAnchor_measurable hx ρ δ).sub hg).norm)
    (fun a => h.anchor_confidence (x a) hρ hδ) hp

theorem CommonLoss.adaptiveAnchor_confidence (h : CommonLoss μ P ν F f)
    {x : A → Point d} (hx : Measurable x) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    (η.prod (localLaw μ (P.gradientNoise^2) ρ δ))
      {w | ρ < ‖gradientAnchor P f (x w.1) ρ δ w.2-gradient F (x w.1)‖} ≤ ENNReal.ofReal δ := by
  simpa using h.adaptiveAnchor_past_confidence (η := η) hx hρ hδ MeasurableSet.univ

end
end SecondOrder
