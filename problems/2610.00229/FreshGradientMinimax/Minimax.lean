import FreshGradientMinimax.Algorithm
import Mathlib.Data.ENat.Lattice

/-! Definition 3.3 as a least fixed integer budget, with infinity when no
dimension-uniform algorithm exists. The algorithm is selected BEFORE the
objective and its fixed stochastic oracle, separately for each finite dimension.
Bounds below are reductions between these definitions, not the hard families. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ)

theorem primal_gap_iff_inf {Δ : ℝ} : O.PrimalGapAtMost Δ ↔
    BddBelow (Set.range O.value) ∧ O.value 0 - sInf (Set.range O.value) ≤ Δ := by
  constructor
  · intro h
    have hb : BddBelow (Set.range O.value) := by
      refine ⟨O.value 0 - Δ, ?_⟩
      rintro _ ⟨x, rfl⟩
      have hx := h x
      linarith
    refine ⟨hb, ?_⟩
    have hi : O.value 0 - Δ ≤ sInf (Set.range O.value) := by
      apply le_csInf (Set.range_nonempty O.value)
      rintro _ ⟨x, rfl⟩
      have hx := h x
      linarith
    linarith
  · rintro ⟨hb, h⟩ x
    have hi := csInf_le hb (show O.value x ∈ Set.range O.value from ⟨x, rfl⟩)
    linarith

def successSet (ε : ℝ) : Set (Euclid dx) := {x | ‖gradient O.value x‖ ≤ ε}

theorem successSet_measurable (ε : ℝ) : MeasurableSet (O.successSet ε) := by
  have hg : Continuous (gradient O.value) := by
    have he : gradient O.value = O.primalGradient := funext O.true_primal_gradient
    rw [he]
    exact O.primalGradient_continuous
  exact (isClosed_le hg.norm continuous_const).measurableSet

theorem zero_gap_stationary (hgap : O.PrimalGapAtMost 0) : gradient O.value 0 = 0 := by
  have hmin : IsLocalMin O.value 0 := Filter.Eventually.of_forall (fun x => by
    have h := hgap x
    linarith)
  have hd := hmin.hasFDerivAt_eq_zero (O.value_hasFDerivAt 0)
  have hv := congrArg (fun l : Euclid dx →L[ℝ] ℝ => l (O.primalGradient 0)) hd
  simp only [innerSL_apply, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at hv
  rw [O.true_primal_gradient]
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (O.primalGradient 0)]

end NCObjective

def InLocalizedClass {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ)
    (Δ : ℝ) (localization : Option ℝ) : Prop :=
  O.PrimalGapAtMost Δ ∧ match localization with
    | none => True
    | some G => O.DualLocalized G

def BudgetSuffices (p : Parameters) (localization : Option ℝ) (N : ℕ) : Prop :=
  ∀ dx dy : ℕ, ∃ A : RandomizedAlgorithm dx dy,
    ∀ O : NCObjective dx dy p.L p.μ, ∀ K : FreshOracle O p.σ,
      InLocalizedClass O p.gap localization →
        2 / 3 ≤ (A.outputLaw K.kernel N).real (O.successSet p.ε)

def oracleComplexity (p : Parameters) (localization : Option ℝ) : ℕ∞ :=
  ⨅ N : {n : ℕ // BudgetSuffices p localization n}, (N.val : ℕ∞)

def localizedComplexity (p : Parameters) : ℕ∞ := oracleComplexity p (some p.G)
def unlocalizedComplexity (p : Parameters) : ℕ∞ := oracleComplexity p none

theorem complexity_le_of_budget {p : Parameters} {loc : Option ℝ} {N : ℕ}
    (h : BudgetSuffices p loc N) : oracleComplexity p loc ≤ (N : ℕ∞) :=
  iInf_le (fun N : {n : ℕ // BudgetSuffices p loc n} => (N.val : ℕ∞)) ⟨N, h⟩

theorem complexity_eq_top_iff (p : Parameters) (loc : Option ℝ) :
    oracleComplexity p loc = ⊤ ↔ ∀ N, ¬ BudgetSuffices p loc N := by
  unfold oracleComplexity
  rw [ENat.iInf_coe_eq_top]
  constructor
  · intro h N hN
    exact h.false ⟨N, hN⟩
  · intro h
    exact ⟨fun N => h N.val N.property⟩

theorem localized_budget_of_unlocalized {p : Parameters} {N : ℕ}
    (h : BudgetSuffices p none N) (G : ℝ) : BudgetSuffices p (some G) N := by
  intro dx dy
  obtain ⟨A, hA⟩ := h dx dy
  refine ⟨A, fun O K hclass => hA O K ⟨hclass.1, trivial⟩⟩

theorem localized_complexity_le_unlocalized (p : Parameters) :
    localizedComplexity p ≤ unlocalizedComplexity p := by
  apply le_iInf
  intro N
  exact complexity_le_of_budget (localized_budget_of_unlocalized N.property p.G)

/-- The fixed-hard-horizon reduction needed for Theorem 3.6. Its hypothesis
must be supplied by an actual hard family, and is not claimed as proved here.
The hard dimension is selected before the unrestricted randomized algorithm. -/
theorem infinite_complexity_of_hard_horizons (p : Parameters)
    (hhard : ∀ N : ℕ, ∃ dx dy : ℕ, ∀ A : RandomizedAlgorithm dx dy,
      ∃ O : NCObjective dx dy p.L p.μ, ∃ K : FreshOracle O p.σ,
        O.PrimalGapAtMost p.gap ∧
          (A.outputLaw K.kernel N).real (O.successSet p.ε) < 2 / 3) :
    unlocalizedComplexity p = ⊤ := by
  apply (complexity_eq_top_iff p none).mpr
  intro N hN
  obtain ⟨dx, dy, hdim⟩ := hhard N
  obtain ⟨A, hA⟩ := hN dx dy
  obtain ⟨O, K, hgap, hfail⟩ := hdim A
  exact (not_lt_of_ge (hA O K ⟨hgap, trivial⟩)) hfail

end FreshGradientMinimax
