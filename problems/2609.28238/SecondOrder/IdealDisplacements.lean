import SecondOrder.IdealEpochs

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def stepDrift {d : ℕ} (L : ℝ) (z : IdealState d) (a : IdealMove d) : Point d :=
  if z.running then
    match a with
    | .gradient g => (-1/(4*L))•g
    | _ => 0
  else 0

def stepDirection {d : ℕ} (s : ℝ) (z : IdealState d) (a : IdealMove d) : Point d :=
  if z.running then
    match a with
    | .curvature u => s•u
    | _ => 0
  else 0

theorem norm_sign_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Bool) (v : E) :
    ‖signValue b•v‖ = ‖v‖ := by cases b <;> simp [signValue]

/-- The physical increment is its predictable gradient drift plus a
direction fixed before a fresh sign. Stopped executions give zero vectors. -/
theorem idealStep_displacement {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool) :
    (idealStep L s z a b).point-z.point = stepDrift L z a+signValue b•stepDirection s z a := by
  cases hr : z.running <;> cases a <;>
    simp [idealStep,stepDrift,stepDirection,gradientNext,curvatureNext,hr,smul_smul]

theorem idealStep_gradientEnergy {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool) :
    (idealStep L s z a b).gradientEnergy = z.gradientEnergy+‖stepDrift L z a‖^2 := by
  cases hr : z.running <;> cases a <;> simp [idealStep,stepDrift,gradientNext,hr]

theorem idealStep_curvatureEnergy {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool) :
    (idealStep L s z a b).curvatureEnergy = z.curvatureEnergy+‖stepDirection s z a‖^2 := by
  cases hr : z.running <;> cases a <;> cases b <;>
    simp [idealStep,stepDirection,curvatureNext,signValue,hr]

theorem stepDrift_nonzero_gradient {d : ℕ} (L : ℝ) (z : IdealState d) (a : IdealMove d)
    (ha : stepDrift L z a ≠ 0) : isGradientMove z a = true := by
  cases hr : z.running <;> cases a <;> simp_all [stepDrift,isGradientMove]

def idealDrift {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (t : ℕ) (w : Fin t → Bool) : Point d :=
  let z := idealRun L s policy t w
  stepDrift L z (policy t w z)

def idealDirection {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (t : ℕ) (w : Fin t → Bool) : Point d :=
  let z := idealRun L s policy t w
  stepDirection s z (policy t w z)

def pathDrift {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (t : ℕ) : Point d :=
  idealDrift L s policy t (fun i => w i.val)

def pathInnovation {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (t : ℕ) : Point d :=
  signValue (w t)•idealDirection L s policy t (fun i => w i.val)

theorem idealPath_displacement {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (t : ℕ) :
    (idealPath L s policy w (t+1)).point-(idealPath L s policy w t).point =
      pathDrift L s policy w t+pathInnovation L s policy w t := by
  rw [idealPath_succ]
  exact idealStep_displacement L s _ _ _

theorem idealPath_gradientEnergy {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (M : ℕ) :
    (∑ i ∈ Finset.range M, ‖pathDrift L s policy w i‖^2) = (idealPath L s policy w M).gradientEnergy := by
  induction M with
  | zero => simp [idealPath,idealRun,idealInitial]
  | succ n ih => rw [Finset.sum_range_succ,ih,idealPath_succ,idealStep_gradientEnergy]; rfl

theorem idealPath_curvatureEnergy {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) (w : ℕ → Bool) (M : ℕ) :
    (∑ i ∈ Finset.range M, ‖pathInnovation L s policy w i‖^2) = (idealPath L s policy w M).curvatureEnergy := by
  induction M with
  | zero => simp [idealPath,idealRun,idealInitial]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,idealPath_succ,idealStep_curvatureEnergy]
    simp only [pathInnovation,norm_sign_smul]
    rfl

theorem pathDrift_epoch_support {d M q : ℕ} (hq : 0 < q) (L s : ℝ) (policy : IdealPolicy d)
    (w : ℕ → Bool) (e : ℕ) :
    ((epochSteps M q (idealGradientFlag L s policy w) e).filter
      (fun k => pathDrift L s policy w k.val ≠ 0)).card ≤ q := by
  have hh := epoch_drift_support M hq (idealGradientFlag L s policy w)
    (fun k => pathDrift L s policy w k.val)
    (fun k hk => stepDrift_nonzero_gradient L _ _ hk) e
  convert hh using 1
  congr 1
  ext k
  simp

end
end SecondOrder
