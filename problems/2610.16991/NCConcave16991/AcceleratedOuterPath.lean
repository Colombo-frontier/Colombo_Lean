import NCConcave16991.AcceleratedStochasticProx
import NCConcave16991.FinitePrefixes
import NCConcave16991.MoreauDescent

/-! # The actual accelerated outer trajectory and its checked descent -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.Accelerated

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def outerCenter (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ δ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    (t : ℕ) → FiniteProcess.History (ProxSeed p Δ τ δ failure) t → PrimalSpace dx :=
  FiniteProcess.trajectory
    (fun _ c ω ↦ stochasticProxOutput P hAS Δ τ δ failure y0 hy0 c ω) P.initialPoint

def outerBad (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ δ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (t : ℕ)
    (h : FiniteProcess.History (ProxSeed p Δ τ δ failure) t)
    (ω : ProxSeed p Δ τ δ failure) : Prop :=
  stochasticProxBad P hAS Δ τ δ failure y0 hy0 (outerCenter P hAS Δ τ δ failure y0 hy0 t h) ω

theorem outerCenter_succ (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ δ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (t : ℕ)
    (h : FiniteProcess.History (ProxSeed p Δ τ δ failure) (t + 1)) :
    outerCenter P hAS Δ τ δ failure y0 hy0 (t + 1) h =
      stochasticProxOutput P hAS Δ τ δ failure y0 hy0
        (outerCenter P hAS Δ τ δ failure y0 hy0 t h.1) h.2 := rfl

theorem outer_failure_probability (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ : ℝ) {τ δ failure : ℝ} (hτ : 0 < τ) (hτL : τ ≤ p.L) (hδ : 0 < δ)
    (hf : 0 < failure) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (S : ℕ) :
    (FiniteProcess.law (proxLaw p Δ τ δ failure) S).real
      {h | FiniteProcess.everBad (outerBad P hAS Δ τ δ failure y0 hy0) S h} ≤
      S * ((horizon τ p.diameter δ : ℝ) * failure) :=
  FiniteProcess.adaptive_failure_probability (proxLaw p Δ τ δ failure)
    (outerBad P hAS Δ τ δ failure y0 hy0)
    (mul_nonneg (Nat.cast_nonneg _) hf.le)
    (fun t h ↦ stochasticProxBad_probability P hAS Δ hτ hτL hδ hf y0 hy0
      (outerCenter P hAS Δ τ δ failure y0 hy0 t h)) S

/-- A literal inexact objective certificate gives both inequalities used by
the source outer descent, for the actual unrestricted proximal minimizer. -/
theorem actual_inexact_prox_descent (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {c next : PrimalSpace dx} {δ : ℝ}
    (hcert : primalObjective K P.component next + p.L * ‖next - c‖ ^ 2 ≤
      primalObjective K P.component (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) +
        p.L * ‖proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c - c‖ ^ 2 + δ) :
    ‖next - proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c‖ ^ 2 ≤ 2 * δ / p.L ∧
      p.L * ‖next - c‖ ^ 2 ≤ primalObjective K P.component c - primalObjective K P.component next + δ := by
  let prox := proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c
  have hp : IsProxPoint (primalObjective K P.component) p.L c prox :=
    proximalMap_spec p.L_pos (P.primal_continuous hAS) P.value_bddBelow c
  have hg := strongConvex_min_growth (weaklyConvex_prox_strong (P.primal_weaklyConvex hAS) c) hp next
  have hc := hp c
  simp only [proxObjective, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hc
  change primalObjective K P.component prox + p.L * ‖prox - c‖ ^ 2 +
    p.L / 2 * ‖prox - next‖ ^ 2 ≤ primalObjective K P.component next + p.L * ‖next - c‖ ^ 2 at hg
  constructor
  · apply (le_div_iff₀ p.L_pos).2
    rw [norm_sub_rev prox next] at hg
    nlinarith only [hg, hcert]
  · nlinarith only [hc, hcert]

/-- Before an abort, the actual current value gap grows by at most δ per
outer iteration. The cap is a public quantity, independent of sampled data. -/
theorem outer_gap_on_good (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {Δ τ δ failure : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) {S : ℕ}
    (hcap : p.gap + (S : ℝ) * δ ≤ Δ) (t : ℕ) (ht : t ≤ S)
    (h : FiniteProcess.History (ProxSeed p Δ τ δ failure) t)
    (hgood : ¬FiniteProcess.everBad (outerBad P hAS Δ τ δ failure y0 hy0) t h) :
    primalObjective K P.component (outerCenter P hAS Δ τ δ failure y0 hy0 t h) -
      sInf (range (primalObjective K P.component)) ≤ p.gap + t * δ := by
  induction t with
  | zero => simpa only [outerCenter, FiniteProcess.trajectory, Nat.cast_zero, zero_mul, add_zero] using P.initial_gap
  | succ t ih =>
    have hprev : ¬FiniteProcess.everBad (outerBad P hAS Δ τ δ failure y0 hy0) t h.1 :=
      fun hb ↦ hgood (Or.inl hb)
    have hstep : ¬outerBad P hAS Δ τ δ failure y0 hy0 t h.1 h.2 := fun hb ↦ hgood (Or.inr hb)
    have hgap := ih (by omega) h.1 hprev
    have htR : (t : ℝ) ≤ S := by exact_mod_cast (show t ≤ S by omega)
    have hcurrent : primalObjective K P.component
        (outerCenter P hAS Δ τ δ failure y0 hy0 t h.1) -
        sInf (range (primalObjective K P.component)) ≤ Δ := by nlinarith only [hgap, hcap, mul_le_mul_of_nonneg_right htR hδ.le]
    have hc := stochasticProxOutput_certificate P hAS hτ hδ y0 hy0 _ hcurrent h.2 hstep
    have hd := (actual_inexact_prox_descent P hAS hc).2
    rw [outerCenter_succ]
    push_cast
    have hn : 0 ≤ p.L * ‖stochasticProxOutput P hAS Δ τ δ failure y0 hy0
      (outerCenter P hAS Δ τ δ failure y0 hy0 t h.1) h.2 -
        outerCenter P hAS Δ τ δ failure y0 hy0 t h.1‖ ^ 2 := mul_nonneg p.L_pos.le (sq_nonneg _)
    nlinarith only [hgap, hd, hn]

end NCConcave16991.Accelerated
