import NCConcave16991.InnerLoop
import NCConcave16991.SVRGResidual
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Actual finite-seed projected SVRG epoch

The sample path uses fresh uniform component identities and the projected SVRG
estimator.  Its contraction is deduced by integrating the actual projected
iteration, using averaged smoothness without component monotonicity.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.SVRG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
  (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- The paper's step size for an averaged-smooth strongly monotone finite sum. -/
def epochStepSize (ell μ : ℝ) : ℝ := μ / (12 * ell ^ 2)

/-- The deterministic number of stochastic steps in one epoch. -/
def epochLength (ell μ : ℝ) : ℕ := Nat.ceil (12 * ell ^ 2 * Real.log 6 / μ ^ 2)

/-- Actual projected SVRG paths, driven by the genuine product law `seedLaw`. -/
def epochIterate (G : Fin n → E → E) (anchor : S) (η : ℝ) (k : ℕ)
    (ω : InnerAlgorithm.Seed n k) : S :=
  InnerAlgorithm.trajectory S hne hclosed hconvex G (fun _ => 0) anchor 0 η k ω

/-- The actual SVRG estimator: one cached full average and two component evaluations. -/
theorem epoch_estimator (G : Fin n → E → E) (anchor z : E) (i : Fin n) :
    InnerAlgorithm.estimator G (fun _ => 0) anchor 0 z i =
      G i z - G i anchor + averageMap G anchor := by
  simp only [InnerAlgorithm.estimator, add_zero]
  abel

theorem epochIterate_succ (G : Fin n → E → E) (anchor : S) (η : ℝ) (k : ℕ)
    (ω : InnerAlgorithm.Seed n (k + 1)) :
    epochIterate S hne hclosed hconvex G anchor η (k + 1) ω =
      VariationalInequality.projection S hne hclosed hconvex
        ((epochIterate S hne hclosed hconvex G anchor η k ω.1 : E) -
          η • (G ω.2 (epochIterate S hne hclosed hconvex G anchor η k ω.1) -
            G ω.2 anchor + averageMap G anchor)) := by
  simp only [epochIterate, InnerAlgorithm.trajectory, InnerAlgorithm.step, epoch_estimator]

/-- The real expectation of the actual finite-seed epoch path. -/
def epochError (G : Fin n → E → E) (anchor : S) (η : ℝ) (star : E) (k : ℕ) : ℝ :=
  ∫ ω, ‖(epochIterate S hne hclosed hconvex G anchor η k ω : E) - star‖ ^ 2
    ∂InnerAlgorithm.seedLaw k

theorem epochError_initial (G : Fin n → E → E) (anchor : S) (η : ℝ) (star : E) :
    epochError S hne hclosed hconvex G anchor η star 0 = ‖(anchor : E) - star‖ ^ 2 := by
  simp [epochError, epochIterate, InnerAlgorithm.trajectory, InnerAlgorithm.seedLaw]

/-- Fresh-index integration yields the actual affine moment recursion. -/
theorem epochError_recursion {G : Fin n → E → E} {ell μ η : ℝ}
    (hell : 0 ≤ ell) (hAS : AveragedSmooth G S ell) (hη : 0 < η)
    (hsmall : 11 * η * ell ^ 2 ≤ μ) (anchor star : S)
    (hstar : VariationalInequality.IsSolution S (averageMap G) star)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ)
    (k : ℕ) :
    epochError S hne hclosed hconvex G anchor η star (k + 1) ≤
      (1 - η * μ) * epochError S hne hclosed hconvex G anchor η star k +
        2 * η ^ 2 * ell ^ 2 * ‖(anchor : E) - star‖ ^ 2 := by
  have hLip := hAS.average_lipschitz (Nat.pos_of_ne_zero (NeZero.ne n)) hell
  have hs : VariationalInequality.IsSolution S
      (fun w => InnerAlgorithm.operator G (fun _ => 0) w + 0) star := by
    simpa only [InnerAlgorithm.operator, add_zero] using hstar
  have hr := InnerAlgorithm.meanSquare_recursion S hne hclosed hconvex (fun _ => 0)
    hell hAS anchor (0 : E) hη hsmall star hs
    (fun z => μ * ‖z - star‖ ^ 2) (‖(anchor : E) - star‖ ^ 2)
    (fun z hz => by
      simpa only [InnerAlgorithm.operator, add_zero] using
        (hLip z hz star star.property).trans
          (by nlinarith [mul_nonneg hell (norm_nonneg (z - (star : E)))]) )
    (fun z hz => by simpa only [InnerAlgorithm.operator, add_zero] using hMono z hz)
    (fun _ _ => le_rfl) (by rw [norm_sub_rev]) k
  change epochError S hne hclosed hconvex G anchor η star (k + 1) ≤ _ at hr
  have hc : InnerAlgorithm.meanCost S hne hclosed hconvex G (fun _ => 0) anchor 0 η
      (fun z => μ * ‖z - (star : E)‖ ^ 2) k =
      μ * epochError S hne hclosed hconvex G anchor η star k := by
    simp only [InnerAlgorithm.meanCost, epochError, epochIterate, integral_const_mul]
  rw [hc] at hr
  change epochError S hne hclosed hconvex G anchor η star (k + 1) ≤
    epochError S hne hclosed hconvex G anchor η star k -
      η * (μ * epochError S hne hclosed hconvex G anchor η star k) + _ at hr
  nlinarith

theorem epochStepSize_pos {ell μ : ℝ} (hell : 0 < ell) (hμ : 0 < μ) :
    0 < epochStepSize ell μ := div_pos hμ (by positivity)

theorem epochStepSize_small {ell μ : ℝ} (hell : 0 < ell) (hμ : 0 ≤ μ) :
    11 * epochStepSize ell μ * ell ^ 2 ≤ μ := by
  dsimp [epochStepSize]
  field_simp [hell.ne']
  linarith

theorem epochStepSize_noise {ell μ : ℝ} (hell : 0 < ell) :
    2 * epochStepSize ell μ ^ 2 * ell ^ 2 = epochStepSize ell μ * μ / 6 := by
  dsimp [epochStepSize]
  field_simp [hell.ne']
  <;> ring

theorem epoch_rate_nonneg {ell μ : ℝ} (hell : 0 < ell) (hμ : 0 < μ) (hμell : μ ≤ ell) :
    0 ≤ 1 - epochStepSize ell μ * μ := by
  have hs : μ ^ 2 ≤ ell ^ 2 := by nlinarith
  dsimp [epochStepSize]
  apply sub_nonneg.mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 12 * ell ^ 2 by positivity)).2
  nlinarith

/-- An explicit geometric estimate for the actual random projected epoch path. -/
theorem epochError_geometric {G : Fin n → E → E} {ell μ : ℝ}
    (hell : 0 < ell) (hμ : 0 < μ) (hμell : μ ≤ ell) (hAS : AveragedSmooth G S ell)
    (anchor star : S) (hstar : VariationalInequality.IsSolution S (averageMap G) star)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ)
    (k : ℕ) :
    epochError S hne hclosed hconvex G anchor (epochStepSize ell μ) star k ≤
      ((1 - epochStepSize ell μ * μ) ^ k + 1 / 6) * ‖(anchor : E) - star‖ ^ 2 := by
  let η := epochStepSize ell μ
  let V := ‖(anchor : E) - star‖ ^ 2
  have hq := epoch_rate_nonneg hell hμ hμell
  have hb := epochStepSize_noise (μ := μ) hell
  induction k with
  | zero =>
    rw [epochError_initial]
    nlinarith [sq_nonneg ‖(anchor : E) - star‖]
  | succ k ih =>
    have hr := epochError_recursion S hne hclosed hconvex hell.le hAS
      (epochStepSize_pos hell hμ) (epochStepSize_small hell hμ.le) anchor star hstar hMono k
    have hi := mul_le_mul_of_nonneg_left ih hq
    rw [pow_succ]
    rw [hb] at hr
    nlinarith

/-- The prescribed deterministic epoch length suppresses the geometric transient. -/
theorem epoch_transient {ell μ : ℝ} (hell : 0 < ell) (hμ : 0 < μ) (hμell : μ ≤ ell) :
    (1 - epochStepSize ell μ * μ) ^ epochLength ell μ ≤ 1 / 6 := by
  have hq := epoch_rate_nonneg hell hμ hμell
  have hp := pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg (epochStepSize ell μ * μ))
    (epochLength ell μ)
  rw [← Real.exp_nat_mul] at hp
  have hm : 12 * ell ^ 2 * Real.log 6 / μ ^ 2 ≤ (epochLength ell μ : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hm
    (mul_nonneg (epochStepSize_pos hell hμ).le hμ.le)
  have hid : (12 * ell ^ 2 * Real.log 6 / μ ^ 2) *
      (epochStepSize ell μ * μ) = Real.log 6 := by
    dsimp [epochStepSize]
    field_simp [hell.ne', hμ.ne']
  rw [hid] at hmul
  have he : Real.exp ((epochLength ell μ : ℝ) * -(epochStepSize ell μ * μ)) ≤
      Real.exp (-Real.log 6) := Real.exp_le_exp.mpr (by nlinarith)
  have hv : Real.exp (-Real.log 6) = (1 / 6 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 6)]
    norm_num
  exact hp.trans (he.trans_eq hv)

/-- Appendix C's one-epoch contraction for the actual independent finite-seed path. -/
theorem epoch_contraction {G : Fin n → E → E} {ell μ : ℝ}
    (hell : 0 < ell) (hμ : 0 < μ) (hμell : μ ≤ ell) (hAS : AveragedSmooth G S ell)
    (anchor star : S) (hstar : VariationalInequality.IsSolution S (averageMap G) star)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ) :
    epochError S hne hclosed hconvex G anchor (epochStepSize ell μ) star (epochLength ell μ) ≤
      (1 / 3 : ℝ) * ‖(anchor : E) - star‖ ^ 2 := by
  have he := epochError_geometric S hne hclosed hconvex hell hμ hμell hAS
    anchor star hstar hMono (epochLength ell μ)
  have ht := mul_le_mul_of_nonneg_right (epoch_transient hell hμ hμell)
    (sq_nonneg ‖(anchor : E) - star‖)
  nlinarith

end NCConcave16991.SVRG
