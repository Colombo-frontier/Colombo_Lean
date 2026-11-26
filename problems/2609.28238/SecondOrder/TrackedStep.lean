import SecondOrder.TrackerMemory
import SecondOrder.PhysicalPrefix

open scoped Classical

namespace SecondOrder
noncomputable section

structure TrackedState (d L : ℕ) where
  physical : IdealState d
  clock : EpochClock
  memory : TrackerMemory d L

def trackedInitial {d L : ℕ} (anchor : Point d) : TrackedState d L :=
  ⟨idealInitial d,⟨0,0,0⟩,trackerReset 0 anchor⟩

def trackedMove {d L : ℕ} (τ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) : IdealMove d :=
  decideMove τ (trackerRead z.memory) r

def trackedNext {d L : ℕ} (Lip s τ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) : IdealState d :=
  idealStep Lip s z.physical (trackedMove τ z r) b

def trackedClock {d L : ℕ} (q : ℕ) (τ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) : EpochClock :=
  epochClockStep q (stateMoves z.physical) (isGradientMove z.physical (trackedMove τ z r)) z.clock

def trackedRestart {d L : ℕ} (q : ℕ) (τ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) : Prop :=
  (trackedClock q τ z r).number ≠ z.clock.number

/-- The physical decision uses the stored tracker and the pre-sign curvature
reply. After moving, insert all new chords; if the gradient counter resets,
replace the memory by a fresh anchor at the new point. The supplied packets
are local routine outputs, not an assertion that they are accurate. -/
def trackedStep {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (packet : BinaryNode L → Point d) (anchor : Point d) : TrackedState d L :=
  let p := trackedNext Lip s τ z r b
  if p.running then
    ⟨p,trackedClock q τ z r,
      if trackedRestart q τ z r then trackerReset p.point anchor else trackerPush z.memory p.point packet⟩
  else {z with physical := p}

def TrackedConsistent {d L : ℕ} (F : Point d → ℝ) (τ ρ : ℝ) (z : TrackedState d L) : Prop :=
  TrackerAccurate F τ ρ z.memory ∧ z.memory.points z.memory.length = z.physical.point

/-- Exactly the local success conditions needed by this physical step.
No curvature guarantee is needed on the gradient branch, and no post-move
packet or anchor condition is imposed when the execution halts. -/
def TrackedLocalGood {d L : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s τ γ ρ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (packet : BinaryNode L → Point d) (anchor : Point d) : Prop :=
  (z.physical.running = true → ‖trackerRead z.memory‖ ≤ 4*τ → ValidCurvatureReply F γ z.physical.point r) ∧
  ((trackedNext Lip s τ z r b).running = true →
    (∀ i ∈ createdNodes L z.memory.length,
      ‖packet i-(gradient F (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i))-
        gradient F (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i)))‖ ≤ ρ) ∧
    (trackedRestart q τ z r → ‖anchor-gradient F (trackedNext Lip s τ z r b).point‖ ≤ τ/4))

theorem trackedInitial_consistent {d L : ℕ} {F : Point d → ℝ} {τ ρ : ℝ}
    (anchor : Point d) (ha : ‖anchor-gradient F 0‖ ≤ τ/4) :
    TrackedConsistent F τ ρ (trackedInitial (L := L) anchor) :=
  ⟨trackerReset_accurate 0 anchor ha,rfl⟩

theorem trackedStep_physical {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (packet : BinaryNode L → Point d) (anchor : Point d) :
    (trackedStep q Lip s τ z r b packet anchor).physical = trackedNext Lip s τ z r b := by
  dsimp only [trackedStep]
  split_ifs <;> rfl

theorem idealStep_stopped_point {d : ℕ} (Lip s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool)
    (hr : (idealStep Lip s z a b).running = false) : (idealStep Lip s z a b).point = z.point := by
  cases hz : z.running <;> cases a <;> simp_all [idealStep]

theorem trackedStep_point_consistent {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (packet : BinaryNode L → Point d) (anchor : Point d)
    (hz : z.memory.points z.memory.length = z.physical.point) :
    let next := trackedStep q Lip s τ z r b packet anchor
    next.memory.points next.memory.length = next.physical.point := by
  dsimp only
  rw [trackedStep_physical]
  by_cases hr : (trackedNext Lip s τ z r b).running = true
  · by_cases he : trackedRestart q τ z r
    · simp [trackedStep,hr,he,trackerReset]
    · simp [trackedStep,hr,he,trackerPush]
  · have hf : (trackedNext Lip s τ z r b).running = false := Bool.eq_false_iff.mpr hr
    have hp := idealStep_stopped_point Lip s z.physical (trackedMove τ z r) b hf
    simp only [trackedStep,hr,↓reduceIte]
    exact hz.trans hp.symm

theorem trackedStep_memory_length {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (packet : BinaryNode L → Point d) (anchor : Point d) :
    (trackedStep q Lip s τ z r b packet anchor).memory.length ≤ z.memory.length+1 := by
  dsimp only [trackedStep]
  split_ifs <;> simp [trackerReset,trackerPush]

theorem trackedStep_consistent {d L : ℕ} {F : Point d → ℝ} {τ γ ρ : ℝ}
    (q : ℕ) (Lip s : ℝ) (z : TrackedState d L) (hz : TrackedConsistent F τ ρ z)
    (r : CurvatureReply d) (b : Bool) (packet : BinaryNode L → Point d) (anchor : Point d)
    (hg : TrackedLocalGood F q Lip s τ γ ρ z r b packet anchor) :
    TrackedConsistent F τ ρ (trackedStep q Lip s τ z r b packet anchor) := by
  refine ⟨?_,trackedStep_point_consistent q Lip s τ z r b packet anchor hz.2⟩
  by_cases hr : (trackedNext Lip s τ z r b).running = true
  · by_cases he : trackedRestart q τ z r
    · simpa only [trackedStep,hr,↓reduceIte,he] using
        trackerReset_accurate (trackedNext Lip s τ z r b).point anchor ((hg.2 hr).2 he)
    · simpa only [trackedStep,hr,↓reduceIte,he] using
        trackerPush_accurate z.memory hz.1 (trackedNext Lip s τ z r b).point packet (hg.2 hr).1
  · simpa only [trackedStep,hr,↓reduceIte] using hz.1

theorem trackedMove_valid {d L : ℕ} {F : Point d → ℝ} {τ γ ρ : ℝ}
    (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hL : (L : ℝ)*ρ ≤ τ/4)
    (z : TrackedState d L) (hz : TrackedConsistent F τ ρ z) (hn : z.memory.length < 2^L)
    (r : CurvatureReply d) (hr : ‖trackerRead z.memory‖ ≤ 4*τ → ValidCurvatureReply F γ z.physical.point r) :
    ValidIdealMove F τ γ z.physical.point (trackedMove τ z r) := by
  apply decideMove_valid hτ z.physical.point (trackerRead z.memory) r
  · have hh := trackerRead_accurate z.memory hz.1 hρ hL hn
    rw [hz.2] at hh
    exact hh
  · exact hr

end
end SecondOrder
