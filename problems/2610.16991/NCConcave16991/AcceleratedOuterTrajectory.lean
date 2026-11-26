import NCConcave16991.AcceleratedOuterPath
import NCConcave16991.AcceleratedBudgetParameters
import NCConcave16991.UpperProbability

/-! # A full checked accelerated trajectory at the public outer parameters -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.Accelerated

abbrev OuterNoise (p : ProblemParameters) :=
  ProxSeed p (gapCap p) (dualRegularization p) (outerTolerance p) (stageFailure p)

abbrev OuterHistory (p : ProblemParameters) :=
  FiniteProcess.History (OuterNoise p) (outerHorizon p)

instance publicOuterHorizon_neZero (p : ProblemParameters) : NeZero (outerHorizon p) :=
  ⟨Nat.ne_of_gt (outerHorizon_bounds p).1⟩

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def publicCenter (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :=
  outerCenter P hAS (gapCap p) (dualRegularization p) (outerTolerance p) (stageFailure p) y0 hy0

def publicBad (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :=
  outerBad P hAS (gapCap p) (dualRegularization p) (outerTolerance p) (stageFailure p) y0 hy0

/-- A finite realized trajectory is extended constantly past its public horizon. -/
def checkedPath (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (h : OuterHistory p) (t : ℕ) : PrimalSpace dx :=
  if ht : t ≤ outerHorizon p then
    publicCenter P hAS y0 hy0 t (FiniteProcess.historyPrefix t (outerHorizon p) ht h)
  else publicCenter P hAS y0 hy0 (outerHorizon p) h

def checkedProxPath (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (h : OuterHistory p) (t : ℕ) : PrimalSpace dx :=
  if t < outerHorizon p then
    proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow (checkedPath P hAS y0 hy0 h t)
  else checkedPath P hAS y0 hy0 h t

theorem checkedPath_zero (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (h : OuterHistory p) :
    checkedPath P hAS y0 hy0 h 0 = P.initialPoint := by
  simp only [checkedPath, Nat.zero_le, dite_eq_left, publicCenter, outerCenter, FiniteProcess.trajectory]

theorem checkedPath_after (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (h : OuterHistory p) {t : ℕ}
    (ht : outerHorizon p ≤ t) :
    checkedPath P hAS y0 hy0 h t = publicCenter P hAS y0 hy0 (outerHorizon p) h := by
  by_cases heq : t = outerHorizon p
  · subst t
    simp only [checkedPath, le_refl, dite_eq_left, FiniteProcess.historyPrefix_self]
  · have hn : ¬t ≤ outerHorizon p := by omega
    simp only [checkedPath, dite_eq_right hn]

theorem checkedPath_succ (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (h : OuterHistory p) {t : ℕ}
    (ht : t < outerHorizon p) :
    checkedPath P hAS y0 hy0 h (t + 1) =
      stochasticProxOutput P hAS (gapCap p) (dualRegularization p) (outerTolerance p) (stageFailure p)
        y0 hy0 (checkedPath P hAS y0 hy0 h t)
          (FiniteProcess.historyPrefix (t + 1) (outerHorizon p) (by omega) h).2 := by
  simp only [checkedPath, dite_eq_left (Nat.succ_le_of_lt ht), dite_eq_left (Nat.le_of_lt ht),
    publicCenter, outerCenter_succ]
  rw [FiniteProcess.historyPrefix_succ_fst]

theorem checkedPath_bounds (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (h : OuterHistory p)
    (hgood : ¬FiniteProcess.everBad (publicBad P hAS y0 hy0) (outerHorizon p) h) (t : ℕ) :
    ‖checkedPath P hAS y0 hy0 h (t + 1) - checkedProxPath P hAS y0 hy0 h t‖ ^ 2 ≤
        2 * outerTolerance p / p.L ∧
      p.L * ‖checkedPath P hAS y0 hy0 h (t + 1) - checkedPath P hAS y0 hy0 h t‖ ^ 2 ≤
        primalObjective K P.component (checkedPath P hAS y0 hy0 h t) -
          primalObjective K P.component (checkedPath P hAS y0 hy0 h (t + 1)) + outerTolerance p := by
  by_cases ht : t < outerHorizon p
  · have hprev := FiniteProcess.noBad_prefix (publicBad P hAS y0 hy0) (Nat.le_of_lt ht) h hgood
    have hstep := FiniteProcess.noBad_step (publicBad P hAS y0 hy0) (Nat.succ_le_of_lt ht) h hgood
    have hgap := outer_gap_on_good P hAS (dualRegularization_pos p) (outerTolerance_pos p) y0 hy0
      (show p.gap + (outerHorizon p : ℝ) * outerTolerance p ≤ gapCap p from le_rfl)
      t (Nat.le_of_lt ht) (FiniteProcess.historyPrefix t (outerHorizon p) (Nat.le_of_lt ht) h) hprev
    have htR : (t : ℝ) ≤ outerHorizon p := by exact_mod_cast Nat.le_of_lt ht
    have hcurrent : primalObjective K P.component (checkedPath P hAS y0 hy0 h t) -
        sInf (range (primalObjective K P.component)) ≤ gapCap p := by
      simp only [checkedPath, dite_eq_left (Nat.le_of_lt ht), publicCenter]
      have hh := mul_le_mul_of_nonneg_right htR (outerTolerance_pos p).le
      exact hgap.trans (by dsimp [gapCap]; linarith only [hh])
    have hc := stochasticProxOutput_certificate P hAS (dualRegularization_pos p) (outerTolerance_pos p)
      y0 hy0 (checkedPath P hAS y0 hy0 h t) hcurrent
      (FiniteProcess.historyPrefix (t + 1) (outerHorizon p) (Nat.succ_le_of_lt ht) h).2
      (by simpa only [publicBad, outerBad, checkedPath, dite_eq_left (Nat.le_of_lt ht), publicCenter] using hstep)
    rw [← checkedPath_succ P hAS y0 hy0 h ht] at hc
    simpa only [checkedProxPath, ite_eq_left ht] using actual_inexact_prox_descent P hAS hc
  · have ht' : outerHorizon p ≤ t := by omega
    rw [checkedProxPath, ite_eq_right ht, checkedPath_after P hAS y0 hy0 h ht',
      checkedPath_after P hAS y0 hy0 h (show outerHorizon p ≤ t + 1 by omega)]
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_self, zero_add]
    exact ⟨div_nonneg (mul_nonneg (by norm_num) (outerTolerance_pos p).le) p.L_pos.le,
      (outerTolerance_pos p).le⟩

end NCConcave16991.Accelerated

