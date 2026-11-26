import NCConcave16991.SVRGEpoch
import NCConcave16991.FiniteProcess
import NCConcave16991.UpperProbability

/-!
# Independent repeated SVRG epochs and a computable residual tail bound

Epochs themselves are driven by fresh finite product seeds.  The expected
distance decay and the final normal-cone residual probability follow for the
actual recursively constructed path.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.SVRG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
  (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- Strong monotonicity cannot exceed the Lipschitz constant on a nontrivial domain. -/
theorem eq_of_strongMono_gt_lipschitz {G : Fin n → E → E} {ell μ : ℝ}
    (hell : 0 ≤ ell) (hAS : AveragedSmooth G S ell) (hμell : ell < μ) (star : S)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ)
    (z : S) : z = star := by
  have hm := hMono z z.property
  have hl := hAS.average_lipschitz (Nat.pos_of_ne_zero (NeZero.ne n)) hell
    z z.property star star.property
  have hi := real_inner_le_norm (averageMap G z - averageMap G star) ((z : E) - star)
  have ht := mul_le_mul_of_nonneg_right hl (norm_nonneg ((z : E) - star))
  have hz : ‖(z : E) - star‖ = 0 := by
    by_contra hzero
    have hn : 0 < ‖(z : E) - star‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hp := mul_pos (sub_pos.mpr hμell) (sq_pos_of_pos hn)
    nlinarith
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hz))

/-- The actual epoch contraction also covers the degenerate singleton-domain case. -/
theorem epoch_contraction_unrestricted {G : Fin n → E → E} {ell μ : ℝ}
    (hell : 0 < ell) (hμ : 0 < μ) (hAS : AveragedSmooth G S ell)
    (anchor star : S) (hstar : VariationalInequality.IsSolution S (averageMap G) star)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ) :
    epochError S hne hclosed hconvex G anchor (epochStepSize ell μ) star (epochLength ell μ) ≤
      (1 / 3 : ℝ) * ‖(anchor : E) - star‖ ^ 2 := by
  by_cases hμell : μ ≤ ell
  · exact epoch_contraction S hne hclosed hconvex hell hμ hμell hAS anchor star hstar hMono
  · have heq (z : S) : z = star :=
      eq_of_strongMono_gt_lipschitz S hell.le hAS (lt_of_not_ge hμell) star hMono z
    have hzero : epochError S hne hclosed hconvex G anchor (epochStepSize ell μ) star
        (epochLength ell μ) = 0 := by
      unfold epochError
      simp only [heq, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, integral_zero]
    rw [hzero]
    positivity

/-- Independent epoch seeds are themselves sampled from the genuine finite law. -/
def epochsLaw (ell μ : ℝ) (J : ℕ) :
    Measure (FiniteProcess.History (InnerAlgorithm.Seed n (epochLength ell μ)) J) :=
  FiniteProcess.law (InnerAlgorithm.seedLaw (n := n) (epochLength ell μ)) J

instance epochsLaw_probability (ell μ : ℝ) (J : ℕ) :
    IsProbabilityMeasure (epochsLaw (n := n) ell μ J) := by
  unfold epochsLaw
  infer_instance

/-- The actual recursively restarted finite-seed SVRG procedure. -/
def epochsIterate (G : Fin n → E → E) (anchor : S) (ell μ : ℝ) (J : ℕ)
    (ω : FiniteProcess.History (InnerAlgorithm.Seed n (epochLength ell μ)) J) : S :=
  FiniteProcess.trajectory
    (fun _ z seed => epochIterate S hne hclosed hconvex G z (epochStepSize ell μ)
      (epochLength ell μ) seed) anchor J ω

def epochsError (G : Fin n → E → E) (anchor : S) (ell μ : ℝ) (star : E) (J : ℕ) : ℝ :=
  ∫ ω, ‖(epochsIterate S hne hclosed hconvex G anchor ell μ J ω : E) - star‖ ^ 2
    ∂epochsLaw ell μ J

/-- The complete actual trajectory contracts by 3^{-J} after J independent epochs. -/
theorem epochs_contraction {G : Fin n → E → E} {ell μ : ℝ}
    (hell : 0 < ell) (hμ : 0 < μ) (hAS : AveragedSmooth G S ell)
    (anchor star : S) (hstar : VariationalInequality.IsSolution S (averageMap G) star)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ)
    (J : ℕ) :
    epochsError S hne hclosed hconvex G anchor ell μ star J ≤
      (1 / 3 : ℝ) ^ J * ‖(anchor : E) - star‖ ^ 2 := by
  induction J with
  | zero =>
    simp [epochsError, epochsLaw, epochsIterate, FiniteProcess.trajectory, FiniteProcess.law]
  | succ J ih =>
    have ht := FiniteProcess.trajectory_integral_succ
      (InnerAlgorithm.seedLaw (n := n) (epochLength ell μ))
      (fun _ z seed => epochIterate S hne hclosed hconvex G z (epochStepSize ell μ)
        (epochLength ell μ) seed) anchor (fun z : S => ‖(z : E) - star‖ ^ 2) J
    change epochsError S hne hclosed hconvex G anchor ell μ star (J + 1) = _ at ht
    rw [ht]
    have hi := integral_mono (μ := epochsLaw (n := n) ell μ J)
      (f := fun ω => epochError S hne hclosed hconvex G
        (epochsIterate S hne hclosed hconvex G anchor ell μ J ω)
        (epochStepSize ell μ) star (epochLength ell μ))
      (g := fun ω => (1 / 3 : ℝ) *
        ‖(epochsIterate S hne hclosed hconvex G anchor ell μ J ω : E) - star‖ ^ 2)
      Integrable.of_finite Integrable.of_finite
      (fun ω => epoch_contraction_unrestricted S hne hclosed hconvex hell hμ hAS
        (epochsIterate S hne hclosed hconvex G anchor ell μ J ω) star hstar hMono)
    rw [integral_const_mul] at hi
    change _ ≤ (1 / 3 : ℝ) * epochsError S hne hclosed hconvex G anchor ell μ star J at hi
    change _ ≤ _ at hi
    have hs := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [pow_succ]
    change (∫ ω, epochError S hne hclosed hconvex G
      (epochsIterate S hne hclosed hconvex G anchor ell μ J ω)
      (epochStepSize ell μ) star (epochLength ell μ) ∂epochsLaw ell μ J) ≤ _
    nlinarith

/-- The actual final residual has the paper's second-moment estimate. -/
theorem epochs_residual_mean_square {G : Fin n → E → E} {ell μ : ℝ}
    (hell : 0 < ell) (hμ : 0 < μ) (hAS : AveragedSmooth G S ell)
    (anchor star : S) (hstar : VariationalInequality.IsSolution S (averageMap G) star)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ)
    (J : ℕ) :
    (∫ ω, ‖fullStepResidual S hne hclosed hconvex (averageMap G) ell
      (epochsIterate S hne hclosed hconvex G anchor ell μ J ω)‖ ^ 2 ∂epochsLaw ell μ J) ≤
      36 * ell ^ 2 * (1 / 3 : ℝ) ^ J * ‖(anchor : E) - star‖ ^ 2 := by
  have hl := hAS.average_lipschitz (Nat.pos_of_ne_zero (NeZero.ne n)) hell.le
  have hp := integral_mono (μ := epochsLaw (n := n) ell μ J)
    Integrable.of_finite Integrable.of_finite
    (fun ω => fullStepResidual_sq_bound S hne hclosed hconvex (averageMap G) hell hl
      (epochsIterate S hne hclosed hconvex G anchor ell μ J ω) star hstar)
  rw [integral_const_mul] at hp
  change _ ≤ 36 * ell ^ 2 * epochsError S hne hclosed hconvex G anchor ell μ star J at hp
  have hc := mul_le_mul_of_nonneg_left
    (epochs_contraction S hne hclosed hconvex hell hμ hAS anchor star hstar hMono J)
    (show 0 ≤ 36 * ell ^ 2 by positivity)
  exact hp.trans (by nlinarith)

/-- The observable normal-cone residual has the claimed actual probability tail. -/
theorem epochs_residual_failure {G : Fin n → E → E} {ell μ d ζ : ℝ}
    (hell : 0 < ell) (hμ : 0 < μ) (hd : 0 ≤ d) (hζ : 0 < ζ)
    (hAS : AveragedSmooth G S ell) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ d)
    (anchor star : S) (hstar : VariationalInequality.IsSolution S (averageMap G) star)
    (hMono : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ ⟪averageMap G z - averageMap G star, z - star⟫_ℝ)
    (J : ℕ) :
    (epochsLaw (n := n) ell μ J).real {ω | ζ <
      ‖fullStepResidual S hne hclosed hconvex (averageMap G) ell
        (epochsIterate S hne hclosed hconvex G anchor ell μ J ω)‖} ≤
      36 * ell ^ 2 * d ^ 2 / ζ ^ 2 * (1 / 3 : ℝ) ^ J := by
  let R := fun ω => ‖fullStepResidual S hne hclosed hconvex (averageMap G) ell
    (epochsIterate S hne hclosed hconvex G anchor ell μ J ω)‖
  have hm := epochs_residual_mean_square S hne hclosed hconvex hell hμ hAS
    anchor star hstar hMono J
  have hd2 := pow_le_pow_left₀ (norm_nonneg ((anchor : E) - star))
    (hdiam anchor anchor.property star star.property) 2
  have hb := mul_le_mul_of_nonneg_left hd2
    (show 0 ≤ 36 * ell ^ 2 * (1 / 3 : ℝ) ^ J by positivity)
  have hmean : (∫ ω, R ω ^ 2 ∂epochsLaw ell μ J) ≤
      (36 * ell ^ 2 * d ^ 2 / ζ ^ 2 * (1 / 3 : ℝ) ^ J) * ζ ^ 2 := by
    have heq : (36 * ell ^ 2 * d ^ 2 / ζ ^ 2 * (1 / 3 : ℝ) ^ J) * ζ ^ 2 =
        36 * ell ^ 2 * (1 / 3 : ℝ) ^ J * d ^ 2 := by field_simp [hζ.ne'] <;> ring
    rw [heq]
    exact hm.trans hb
  have hf := markov_mean_square_bound (epochsLaw (n := n) ell μ J)
    (fun ω => norm_nonneg _) Integrable.of_finite hζ hmean
  apply (measureReal_mono ?_).trans hf
  intro ω hω
  change ζ < R ω at hω
  change ζ ≤ R ω
  exact le_of_lt hω

end NCConcave16991.SVRG
