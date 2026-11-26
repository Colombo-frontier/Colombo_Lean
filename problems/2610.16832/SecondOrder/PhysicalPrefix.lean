import SecondOrder.IdealEpochEnergy

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def stateMoves {d : ℕ} (z : IdealState d) : ℕ := z.gradientMoves+z.curvatureMoves

theorem idealStep_moves_mono {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool) :
    stateMoves z ≤ stateMoves (idealStep L s z a b) := by
  cases hr : z.running <;> cases a <;> simp [stateMoves,idealStep,hr] <;> omega

theorem idealStep_moves_le {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool) :
    stateMoves (idealStep L s z a b) ≤ stateMoves z+1 := by
  cases hr : z.running <;> cases a <;> simp [stateMoves,idealStep,hr] <;> omega

theorem idealStep_stopped_moves {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool)
    (hr : (idealStep L s z a b).running = false) :
    stateMoves (idealStep L s z a b) = stateMoves z := by
  cases hz : z.running <;> cases a <;> simp_all [idealStep,stateMoves]

theorem idealStep_stopped_increments {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool)
    (hr : (idealStep L s z a b).running = false) :
    stepDrift L z a = 0 ∧ stepDirection s z a = 0 := by
  cases hz : z.running <;> cases a <;> simp_all [idealStep,stepDrift,stepDirection]

theorem idealPath_moves_mono {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) :
    Monotone (fun t => stateMoves (idealPath L s policy w t)) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [idealPath_succ]
  exact idealStep_moves_mono L s _ _ _

theorem idealPath_moves_le {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (t : ℕ) :
    stateMoves (idealPath L s policy w t) ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [idealPath_succ]
    exact (idealStep_moves_le L s _ _ _).trans (by omega)

theorem idealPath_stopped_frozen {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool)
    {t k : ℕ} (htk : t ≤ k) (hr : (idealPath L s policy w t).running = false) :
    idealPath L s policy w k = idealPath L s policy w t := by
  induction k,htk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [idealPath_succ,ih]; simp [idealStep,hr]

/-- Before the deterministic cap, actual moves occupy exactly the prefix
whose length is the final gradient-plus-curvature count. The halt decision
itself and all subsequent padded iterations are not physical moves. -/
theorem idealPath_physical_prefix {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool)
    {M t : ℕ} (ht : t < M) :
    (idealPath L s policy w (t+1)).running = true ↔ t < stateMoves (idealPath L s policy w M) := by
  constructor
  · intro hr
    have hc := idealRun_running_count L s policy (t+1) (fun i => w i.val) hr
    have hm := idealPath_moves_mono L s policy w (show t+1 ≤ M by omega)
    change stateMoves (idealPath L s policy w (t+1)) = t+1 at hc
    change stateMoves (idealPath L s policy w (t+1)) ≤ stateMoves (idealPath L s policy w M) at hm
    omega
  · intro hc
    cases hr : (idealPath L s policy w (t+1)).running
    · have hf := idealPath_stopped_frozen L s policy w (show t+1 ≤ M by omega) hr
      have hs := idealStep_stopped_moves L s (idealPath L s policy w t)
        (policy t (fun i => w i.val) (idealPath L s policy w t)) (w t) hr
      have hb := idealPath_moves_le L s policy w t
      change stateMoves (idealPath L s policy w (t+1)) = stateMoves (idealPath L s policy w t) at hs
      rw [hf,hs] at hc
      omega
    · rfl

theorem idealPath_increments_after_length {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool)
    {M t : ℕ} (ht : t < M) (hc : stateMoves (idealPath L s policy w M) ≤ t) :
    pathDrift L s policy w t = 0 ∧ pathInnovation L s policy w t = 0 := by
  have hr : (idealPath L s policy w (t+1)).running = false := by
    cases he : (idealPath L s policy w (t+1)).running
    · rfl
    · have hh := (idealPath_physical_prefix L s policy w ht).mp he
      omega
  have hi := idealStep_stopped_increments L s (idealPath L s policy w t)
    (policy t (fun i => w i.val) (idealPath L s policy w t)) (w t) hr
  refine ⟨hi.1,?_⟩
  change signValue (w t)•stepDirection s (idealPath L s policy w t)
    (policy t (fun i => w i.val) (idealPath L s policy w t)) = 0
  rw [hi.2,smul_zero]

def idealPhysicalLength {d M : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : Fin M → Bool) : ℕ :=
  stateMoves (idealRun L s policy M w)

theorem idealPhysicalLength_le {d M : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : Fin M → Bool) :
    idealPhysicalLength L s policy w ≤ M := by
  have hh := idealPath_moves_le L s policy (extendSigns w) M
  simpa only [idealPath_extendSigns] using hh

theorem idealPhysicalLength_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M : ℕ) :
    Measurable (fun w : Ξ × (Fin M → Bool) => idealPhysicalLength L s (policy w.1) w.2) := by
  have hz := state_measurable_fields.mp (idealRun_measurable L s hm M)
  exact hz.2.2.1.add hz.2.2.2.1

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.idealPhysicalLength_integral (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) :
    let count := fun w : Ξ × (Fin M → Bool) =>
      (idealPhysicalLength P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 : ℝ)
    Integrable count (η.prod (signLaw M)) ∧
      (∫ w, count w ∂η.prod (signLaw M)) ≤ idealMoveBudget P ν τ γ :=
  h.idealMixture_total_moves hτ hγ policy hv M (idealRun_total_moves_measurable _ _ hm M)

end
end SecondOrder
