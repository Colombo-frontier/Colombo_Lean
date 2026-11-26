import SecondOrder.IdealExecution

open MeasureTheory
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.idealStep_count_progress (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (z : IdealState d) (a : IdealMove d)
    (hv : z.running = true → ValidIdealMove F τ γ z.point a) :
    uniformMean (fun b : Bool =>
      let y := idealStep P.gradientLip (curvatureRadius P.hessianHolder ν γ) z a b
      countWork P.gradientLip τ γ (curvatureRadius P.hessianHolder ν γ) y+F y.point) ≤
      countWork P.gradientLip τ γ (curvatureRadius P.hessianHolder ν γ) z+F z.point := by
  cases hz : z.running
  · simp [idealStep, hz]
  · have ha := hv hz
    cases a with
    | halt => simp [idealStep, hz, countWork]
    | gradient g =>
      have hd := (h.gradientNext_progress z.point g hτ ha.1 ha.2).1
      simp only [idealStep, hz, ↓reduceIte, countWork, Nat.cast_add, Nat.cast_one,
        uniformMean_const]
      nlinarith
    | curvature u =>
      have hd := h.curvatureNext_progress z.point u hγ ha.1 ha.2
      rw [PMF.integral_eq_sum] at hd
      change _ ≤ F z.point-uniformMean (fun b : Bool =>
        F (curvatureNext (curvatureRadius P.hessianHolder ν γ) z.point u b)) at hd
      simp only [idealStep, hz, ↓reduceIte, countWork, Nat.cast_add, Nat.cast_one,
        uniformMean_add, uniformMean_const]
      nlinarith

theorem CommonLoss.idealStep_energy_progress (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (z : IdealState d) (a : IdealMove d)
    (hv : z.running = true → ValidIdealMove F τ γ z.point a) :
    uniformMean (fun b : Bool =>
      let y := idealStep P.gradientLip (curvatureRadius P.hessianHolder ν γ) z a b
      energyWork P.gradientLip γ y+F y.point) ≤ energyWork P.gradientLip γ z+F z.point := by
  cases hz : z.running
  · simp [idealStep, hz]
  · have ha := hv hz
    cases a with
    | halt => simp [idealStep, hz, energyWork]
    | gradient g =>
      have hd := (h.gradientNext_progress z.point g hτ ha.1 ha.2).2
      simp only [idealStep, hz, ↓reduceIte, energyWork, uniformMean_const]
      nlinarith
    | curvature u =>
      have hd := h.curvatureNext_progress z.point u hγ ha.1 ha.2
      rw [PMF.integral_eq_sum] at hd
      change _ ≤ F z.point-uniformMean (fun b : Bool =>
        F (curvatureNext (curvatureRadius P.hessianHolder ν γ) z.point u b)) at hd
      simp only [idealStep, hz, ↓reduceIte, energyWork,
        curvatureNext_displacement _ _ _ ha.1, uniformMean_add, uniformMean_const]
      nlinarith

/-- Telescoping expected descent on the actual recursively constructed path.
The policy may depend on every past sign, but cannot inspect the next sign. -/
theorem idealRun_potential {L s : ℝ} (policy : IdealPolicy d) (V : IdealState d → ℝ)
    (hp : ∀ t w, uniformMean (fun b : Bool =>
      V (idealStep L s (idealRun L s policy t w) (policy t w (idealRun L s policy t w)) b)) ≤
      V (idealRun L s policy t w)) (t : ℕ) :
    uniformMean (fun w => V (idealRun L s policy t w)) ≤ V (idealInitial d) := by
  induction t with
  | zero => simp [idealRun]
  | succ t ih =>
    rw [uniformMean_snoc]
    simp only [idealRun_snoc]
    exact (uniformMean_mono (hp t)).trans ih

theorem CommonLoss.idealRun_countWork_bound (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (policy : IdealPolicy d)
    (hv : ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy)
    (t : ℕ) :
    uniformMean (fun w => countWork P.gradientLip τ γ (curvatureRadius P.hessianHolder ν γ)
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy t w)) ≤ P.gap := by
  have hd := idealRun_potential policy
    (fun z => countWork P.gradientLip τ γ (curvatureRadius P.hessianHolder ν γ) z+F z.point)
    (fun n w => h.idealStep_count_progress hτ hγ _ _ (hv n w)) t
  have hg := uniformMean_le_const P.gap (fun w : Fin t → Bool =>
    h.gap_bound (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy t w).point)
  simp only [uniformMean_add, countWork, idealInitial, Nat.cast_zero, mul_zero, zero_add] at hd
  rw [uniformMean_sub, uniformMean_const] at hg
  simp only [countWork, uniformMean_add]
  linarith

theorem CommonLoss.idealRun_energyWork_bound (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (policy : IdealPolicy d)
    (hv : ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy)
    (t : ℕ) :
    uniformMean (fun w => energyWork P.gradientLip γ
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy t w)) ≤ P.gap := by
  have hd := idealRun_potential policy (fun z => energyWork P.gradientLip γ z+F z.point)
    (fun n w => h.idealStep_energy_progress hτ hγ _ _ (hv n w)) t
  have hg := uniformMean_le_const P.gap (fun w : Fin t → Bool =>
    h.gap_bound (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy t w).point)
  simp only [uniformMean_add, energyWork, idealInitial, mul_zero, zero_add] at hd
  rw [uniformMean_sub, uniformMean_const] at hg
  simp only [energyWork, uniformMean_add]
  linarith

end
end SecondOrder
