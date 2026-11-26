import HeavyTail.AdaptiveKernelConcentration
import HeavyTail.CappedRawPolicy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The raw-call budget for the actual stopped state machine, proved under
its recursively generated history law. No conditional-expectation or terminal
count hypothesis is imposed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace HeavyTail.CappedRaw.Rule
universe u v w
variable {Seed Reply : Type u} {State : Type v} {Query Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Reply] [MeasurableSpace State]
  [MeasurableSpace Query] [MeasurableSpace Output]

variable (M : Rule State Query Reply Output)

def rejectionFactor (initial : Seed → State) (n t : ℕ)
    (h : AdaptiveKernel.History Seed Reply t × Reply) : ℝ :=
  if h ∈ M.rejection initial n t then 16 else 1

theorem rejectionFactor_measurable {initial : Seed → State} (hi : Measurable initial)
    (n t : ℕ) : Measurable (M.rejectionFactor initial n t) :=
  Measurable.ite (M.rejection_measurable hi n t) measurable_const measurable_const

theorem rejectionFactor_nonneg (initial : Seed → State) (n t : ℕ)
    (h : AdaptiveKernel.History Seed Reply t × Reply) : 0 ≤ M.rejectionFactor initial n t h := by
  unfold rejectionFactor
  split_ifs <;> norm_num

theorem rejectionFactor_le (initial : Seed → State) (n t : ℕ)
    (h : AdaptiveKernel.History Seed Reply t × Reply) : M.rejectionFactor initial n t h ≤ 16 := by
  unfold rejectionFactor
  split_ifs <;> norm_num

theorem rejectionFactor_integral {initial : Seed → State} (hi : Measurable initial)
    (n t : ℕ) (h : AdaptiveKernel.History Seed Reply t) (Q : Measure Reply)
    [IsProbabilityMeasure Q] :
    (∫ r, M.rejectionFactor initial n t (h, r) ∂Q) =
      1 + 15 * Q.real {r | (h, r) ∈ M.rejection initial n t} := by
  let S : Set Reply := {r | (h, r) ∈ M.rejection initial n t}
  have hS : MeasurableSet S := (M.rejection_measurable hi n t).preimage measurable_prodMk_left
  have he : (fun r => M.rejectionFactor initial n t (h, r)) =
      fun r => (1 : ℝ) + 15 * S.indicator (fun _ => (1 : ℝ)) r := by
    funext r
    by_cases hr : (h, r) ∈ M.rejection initial n t <;> norm_num [rejectionFactor, S, hr]
  rw [he, integral_add (integrable_const 1) (((integrable_const (1 : ℝ)).indicator hS).const_mul 15),
    integral_const, integral_const_mul, integral_indicator_const 1 hS]
  simp [S]

theorem rejectionFactor_product (initial : Seed → State) (n t : ℕ)
    (h : AdaptiveKernel.History Seed Reply t) :
    AdaptiveKernel.historyProduct (M.rejectionFactor initial n) t h =
      (16 : ℝ) ^ M.rejections initial n t h := by
  induction t with
  | zero => simp [AdaptiveKernel.historyProduct, rejections]
  | succ t ih =>
      simp only [AdaptiveKernel.historyProduct, rejections, ih, rejectionFactor]
      by_cases hr : h ∈ M.rejection initial n t <;> simp [hr, pow_succ]

/-- A uniform actual raw rejection probability gives the exponential raw cap
bound for the stopped algorithm itself, with arbitrary random seeds. -/
theorem failure_probability {initial : Seed → State} (hi : Measurable initial)
    (n T : ℕ) (P : Measure Seed) [IsProbabilityMeasure P]
    (K : Kernel Query Reply) [IsMarkovKernel K]
    (hrej : ∀ t (h : AdaptiveKernel.History Seed Reply t),
      (K (M.query (M.state initial n t h).2)).real
        {r | (h, r) ∈ M.rejection initial n t} ≤ 1 / 16) :
    ((M.policy initial hi n T).historyLaw P K (4 * n)).real
      {h | (M.state initial n (4 * n) h).1 < n} ≤ ((2 : ℝ) ^ (8 * n))⁻¹ := by
  have hstep : ∀ t h, (∫ r, M.rejectionFactor initial n t (h, r)
      ∂K ((M.policy initial hi n T).query t h)) ≤ (2 : ℝ) := by
    intro t h
    rw [M.rejectionFactor_integral hi n t h]
    have hp := hrej t h
    change (K ((M.policy initial hi n T).query t h)).real
      {r | (h, r) ∈ M.rejection initial n t} ≤ 1 / 16 at hp
    linarith only [hp]
  have ht := AdaptiveKernel.historyProduct_tail (M.policy initial hi n T) P K
    (by norm_num : (0 : ℝ) ≤ 16) (by norm_num : (0 : ℝ) < 2)
    (inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) (8 * n)))
    (M.rejectionFactor_measurable hi n) (M.rejectionFactor_nonneg initial n)
    (M.rejectionFactor_le initial n) hstep (4 * n)
  apply le_trans (measureReal_mono (s₂ :=
    {h | (2 : ℝ) ^ (4 * n) / ((2 : ℝ) ^ (8 * n))⁻¹ ≤
      AdaptiveKernel.historyProduct (M.rejectionFactor initial n) (4 * n) h}) ?_) ht
  intro h hh
  have hc := M.raw_cap_failure_implies_rejections initial n h hh
  change (2 : ℝ) ^ (4 * n) / ((2 : ℝ) ^ (8 * n))⁻¹ ≤ _
  rw [M.rejectionFactor_product]
  have he : (2 : ℝ) ^ (4 * n) / ((2 : ℝ) ^ (8 * n))⁻¹ = (16 : ℝ) ^ (3 * n) := by
    rw [div_inv_eq_mul, ← pow_add, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
    congr 1
    omega
  rw [he]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) hc

end HeavyTail.CappedRaw.Rule
