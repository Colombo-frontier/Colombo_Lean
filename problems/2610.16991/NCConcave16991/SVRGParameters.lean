import NCConcave16991.SVRGConvergence

/-! # Public finite epoch counts for a prescribed SVRG residual failure probability -/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace NNReal

namespace NCConcave16991.SVRG

/-- Public deterministic epoch count; the natural ceiling clips negative logarithms at zero. -/
def residualEpochCount (ell d ζ p : ℝ) : ℕ :=
  Nat.ceil (Real.log (36 * ell ^ 2 * d ^ 2 / (ζ ^ 2 * p)) / Real.log 3)

theorem geometric_failure_budget {R p : ℝ} (hR : 0 ≤ R) (hp : 0 < p)
    (J : ℕ) (hJ : Real.log (R / p) / Real.log 3 ≤ (J : ℝ)) :
    R * (1 / 3 : ℝ) ^ J ≤ p := by
  by_cases hzero : R = 0
  · simp [hzero, hp.le]
  have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl : Real.log (R / p) ≤ (J : ℝ) * Real.log 3 :=
    (div_le_iff₀ hlog3).1 hJ
  have he := Real.exp_le_exp.mpr (neg_le_neg hl)
  have hbase : Real.exp (-Real.log 3) = (1 / 3 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hpow : (1 / 3 : ℝ) ^ J = Real.exp (-(J : ℝ) * Real.log 3) := by
    rw [← hbase, ← Real.exp_nat_mul]
    congr 1
    ring
  have hinv : Real.exp (-Real.log (R / p)) = p / R := by
    rw [Real.exp_neg, Real.exp_log (div_pos hRp hp)]
    field_simp [hp.ne', hRp.ne']
  rw [hinv] at he
  have hh : (1 / 3 : ℝ) ^ J ≤ p / R := by
    rw [hpow]
    convert he using 1 <;> congr 1 <;> ring
  exact (mul_le_mul_of_nonneg_left hh hR).trans_eq (by field_simp [hRp.ne'])

theorem residualEpochCount_failure {ell d ζ p : ℝ}
    (hp : 0 < p) (hζ : 0 < ζ) :
    36 * ell ^ 2 * d ^ 2 / ζ ^ 2 * (1 / 3 : ℝ) ^ residualEpochCount ell d ζ p ≤ p := by
  apply geometric_failure_budget (by positivity) hp
  have heq : 36 * ell ^ 2 * d ^ 2 / ζ ^ 2 / p =
      36 * ell ^ 2 * d ^ 2 / (ζ ^ 2 * p) := by ring
  rw [heq]
  exact Nat.le_ceil _

theorem epochLength_bound {ell μ : ℝ} (hell : 0 < ell) (hμ : 0 < μ) :
    (epochLength ell μ : ℝ) < 12 * ell ^ 2 * Real.log 6 / μ ^ 2 + 1 := by
  apply Nat.ceil_lt_add_one
  exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num)))
    (sq_nonneg μ)

theorem residualEpochCount_bound {ell d ζ p : ℝ} :
    (residualEpochCount ell d ζ p : ℝ) <
      max 0 (Real.log (36 * ell ^ 2 * d ^ 2 / (ζ ^ 2 * p)) / Real.log 3) + 1 := by
  unfold residualEpochCount
  by_cases hx : 0 ≤ Real.log (36 * ell ^ 2 * d ^ 2 / (ζ ^ 2 * p)) / Real.log 3
  · rw [max_eq_right hx]
    exact Nat.ceil_lt_add_one hx
  · rw [max_eq_left (le_of_not_ge hx)]
    rw [Nat.ceil_eq_zero.mpr (le_of_not_ge hx)]
    norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
  (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- With the public fixed epoch count, the actual computable residual fails with probability at most p. -/
theorem residual_failure_at_public_count {G : Fin n → E → E} {ell μ d ζ p : ℝ}
    (hell : 0 < ell) (hμ : 0 < μ) (hd : 0 ≤ d) (hζ : 0 < ζ) (hp : 0 < p)
    (hAS : AveragedSmooth G S ell) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ d)
    (anchor star : S) (hstar : VariationalInequality.IsSolution S (averageMap G) star)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ) :
    (epochsLaw (n := n) ell μ (residualEpochCount ell d ζ p)).real {ω | ζ <
      ‖fullStepResidual S hne hclosed hconvex (averageMap G) ell
        (epochsIterate S hne hclosed hconvex G anchor ell μ (residualEpochCount ell d ζ p) ω)‖} ≤ p :=
  (epochs_residual_failure S hne hclosed hconvex hell hμ hd hζ hAS hdiam anchor star
    hstar hMono (residualEpochCount ell d ζ p)).trans (residualEpochCount_failure hp hζ)

/-- The complete residual-engine guarantee assumes only the actual operator class;
the VI solution used in the proof is constructed by projected contraction. -/
theorem residual_failure_of_strongMonotone {G : Fin n → E → E} {ell μ d ζ p : ℝ}
    (hell : 0 < ell) (hμ : 0 < μ) (hd : 0 ≤ d) (hζ : 0 < ζ) (hp : 0 < p)
    (hAS : AveragedSmooth G S ell) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ d)
    (hMono : ∀ x ∈ S, ∀ y ∈ S,
      μ * ‖x - y‖ ^ 2 ≤ ⟪averageMap G x - averageMap G y, x - y⟫_ℝ)
    (anchor : S) :
    (epochsLaw (n := n) ell μ (residualEpochCount ell d ζ p)).real {ω | ζ <
      ‖fullStepResidual S hne hclosed hconvex (averageMap G) ell
        (epochsIterate S hne hclosed hconvex G anchor ell μ (residualEpochCount ell d ζ p) ω)‖} ≤ p := by
  have hl := hAS.average_lipschitz (Nat.pos_of_ne_zero (NeZero.ne n)) hell.le
  have hLip : LipschitzOnWith (NNReal.mk ell hell.le) (averageMap G) S :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      simpa only [dist_eq_norm, NNReal.coe_mk] using hl x hx y hy
  obtain ⟨star, hstar, _⟩ := VariationalInequality.existsUnique_solution S hne hclosed hconvex
    (averageMap G) (NNReal.mk ell hell.le) hμ hLip hMono
  let starS : S := ⟨star, hstar.1⟩
  exact residual_failure_at_public_count S hne hclosed hconvex hell hμ hd hζ hp hAS hdiam
    anchor starS hstar (fun z hz => hMono z hz star hstar.1)

end NCConcave16991.SVRG
