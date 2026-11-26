import SecondOrder.ActualProgress

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

inductive IdealMove (d : ℕ)
  | halt
  | gradient (g : Point d)
  | curvature (u : Point d)

structure IdealState (d : ℕ) where
  point : Point d
  running : Bool
  gradientMoves : ℕ
  curvatureMoves : ℕ
  gradientEnergy : ℝ
  curvatureEnergy : ℝ

def idealInitial (d : ℕ) : IdealState d := ⟨0,true,0,0,0,0⟩

def idealStep {d : ℕ} (L s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool) : IdealState d :=
  if z.running then
    match a with
    | .halt => {z with running := false}
    | .gradient g =>
        {z with
          point := gradientNext L z.point g
          gradientMoves := z.gradientMoves+1
          gradientEnergy := z.gradientEnergy+‖gradientNext L z.point g-z.point‖^2}
    | .curvature u =>
        {z with
          point := curvatureNext s z.point u b
          curvatureMoves := z.curvatureMoves+1
          curvatureEnergy := z.curvatureEnergy+‖curvatureNext s z.point u b-z.point‖^2}
  else z

abbrev IdealPolicy (d : ℕ) := (t : ℕ) → (Fin t → Bool) → IdealState d → IdealMove d

/-- The finite prefix of one infinite causal policy. Halted states are frozen;
fresh signs after halting are padding and cannot restart the execution. -/
def idealRun {d : ℕ} (L s : ℝ) (policy : IdealPolicy d) : (t : ℕ) → (Fin t → Bool) → IdealState d
  | 0, _ => idealInitial d
  | t+1, w =>
    let z := idealRun L s policy t (Fin.init w)
    idealStep L s z (policy t (Fin.init w) z) (w (Fin.last t))

@[simp] theorem idealRun_snoc {d : ℕ} (L s : ℝ) (policy : IdealPolicy d)
    (t : ℕ) (w : Fin t → Bool) (b : Bool) :
    idealRun L s policy (t+1) (Fin.snoc w b) =
      idealStep L s (idealRun L s policy t w) (policy t w (idealRun L s policy t w)) b := by
  simp [idealRun]

def ValidIdealMove {d : ℕ} (F : Point d → ℝ) (τ γ : ℝ) (x : Point d) : IdealMove d → Prop
  | .halt => IsSOSP F (10*τ) γ x
  | .gradient g => ‖g-gradient F x‖ ≤ τ ∧ 4*τ ≤ ‖g‖
  | .curvature u => ‖u‖ = 1 ∧ ⟪hessian F x u,u⟫_ℝ ≤ -γ/2

def ValidIdealPolicy {d : ℕ} (F : Point d → ℝ) (L s τ γ : ℝ) (policy : IdealPolicy d) : Prop :=
  ∀ t w, (idealRun L s policy t w).running = true →
    ValidIdealMove F τ γ (idealRun L s policy t w).point
      (policy t w (idealRun L s policy t w))

def countWork {d : ℕ} (L τ γ s : ℝ) (z : IdealState d) : ℝ :=
  (τ^2/L)*(z.gradientMoves : ℝ)+(3*γ*s^2/16)*(z.curvatureMoves : ℝ)

def energyWork {d : ℕ} (L γ : ℝ) (z : IdealState d) : ℝ :=
  L*z.gradientEnergy+(3*γ/16)*z.curvatureEnergy

theorem idealStep_energy_nonnegative {d : ℕ} (L s : ℝ) (z : IdealState d)
    (a : IdealMove d) (b : Bool) (hg : 0 ≤ z.gradientEnergy) (hc : 0 ≤ z.curvatureEnergy) :
    0 ≤ (idealStep L s z a b).gradientEnergy ∧ 0 ≤ (idealStep L s z a b).curvatureEnergy := by
  cases hz : z.running <;> cases a <;> simp only [idealStep, hz, Bool.false_eq_true,
    ↓reduceIte] <;> constructor <;> positivity

theorem idealRun_energy_nonnegative {d : ℕ} (L s : ℝ) (policy : IdealPolicy d)
    (t : ℕ) (w : Fin t → Bool) :
    0 ≤ (idealRun L s policy t w).gradientEnergy ∧ 0 ≤ (idealRun L s policy t w).curvatureEnergy := by
  induction t with
  | zero => simp [idealRun, idealInitial]
  | succ t ih =>
    exact idealStep_energy_nonnegative L s _ _ _ (ih (Fin.init w)).1 (ih (Fin.init w)).2

theorem idealRun_running_count {d : ℕ} (L s : ℝ) (policy : IdealPolicy d)
    (t : ℕ) (w : Fin t → Bool) (hl : (idealRun L s policy t w).running = true) :
    (idealRun L s policy t w).gradientMoves+(idealRun L s policy t w).curvatureMoves = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    let z := idealRun L s policy t (Fin.init w)
    let a := policy t (Fin.init w) z
    change (idealStep L s z a (w (Fin.last t))).running = true at hl
    change (idealStep L s z a (w (Fin.last t))).gradientMoves+
      (idealStep L s z a (w (Fin.last t))).curvatureMoves = t+1
    cases hz : z.running
    · simp [idealStep, hz] at hl
    · have hp := ih (Fin.init w) hz
      change z.gradientMoves+z.curvatureMoves = t at hp
      cases ha : a with
      | halt => simp [idealStep, hz, ha] at hl
      | gradient g =>
        simp only [idealStep, hz, ↓reduceIte]
        omega
      | curvature u =>
        simp only [idealStep, hz, ↓reduceIte]
        omega

theorem idealRun_stopped_sosp {d : ℕ} {F : Point d → ℝ} {L s τ γ : ℝ}
    {policy : IdealPolicy d} (hv : ValidIdealPolicy F L s τ γ policy)
    (t : ℕ) (w : Fin t → Bool) (hl : (idealRun L s policy t w).running = false) :
    IsSOSP F (10*τ) γ (idealRun L s policy t w).point := by
  induction t with
  | zero => simp [idealRun, idealInitial] at hl
  | succ t ih =>
    let z := idealRun L s policy t (Fin.init w)
    let a := policy t (Fin.init w) z
    change (idealStep L s z a (w (Fin.last t))).running = false at hl
    change IsSOSP F (10*τ) γ (idealStep L s z a (w (Fin.last t))).point
    cases hz : z.running
    · simpa [idealStep, hz] using ih (Fin.init w) hz
    · have ha := hv t (Fin.init w) hz
      change ValidIdealMove F τ γ z.point a at ha
      cases ha' : a with
      | halt => simpa [idealStep, hz, ha', ValidIdealMove] using ha
      | gradient g => simp [idealStep, hz, ha'] at hl
      | curvature u => simp [idealStep, hz, ha'] at hl

end
end SecondOrder
