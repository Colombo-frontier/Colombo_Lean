import HeavyTail.SignLoss
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Genuine Euclidean hard instances

Convexity, Lipschitzness, a bounded measurable selected subgradient, quadratic
strong convexity, and the previously proved minimizer/loss facts are established
for the manuscript's actual absolute-value family, not assumed as membership.
-/

open scoped BigOperators InnerProductSpace

namespace HeavyTail

abbrev HardSpace (k : ℕ) := EuclideanSpace ℝ (Fin k)

theorem hardSpace_norm_sq {k : ℕ} (x : HardSpace k) :
    ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin k ↦ ℝ) x

noncomputable def hardLoss {k : ℕ} (a ρ : ℝ) (v : Fin k → ℝ)
    (x : HardSpace k) : ℝ :=
  (a / Real.sqrt (k : ℝ)) * ∑ j, |x j - ρ * v j|

noncomputable def hardGradient {k : ℕ} (a ρ : ℝ) (v : Fin k → ℝ)
    (x : HardSpace k) : HardSpace k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun j ↦ (a / Real.sqrt (k : ℝ)) * Real.sign (x j - ρ * v j))

noncomputable def hardRegularizer {k : ℕ} (μ : ℝ) (x : HardSpace k) : ℝ :=
  μ / 2 * ‖x‖ ^ 2

lemma scalar_abs_subgradient (x y c : ℝ) :
    |x - c| - |y - c| ≤ Real.sign (x - c) * (x - y) := by
  rcases lt_trichotomy (x - c) 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]
    nlinarith [neg_le_abs (y - c)]
  · rw [hx, Real.sign_zero, abs_zero]
    nlinarith [abs_nonneg (y - c)]
  · rw [Real.sign_of_pos hx, abs_of_pos hx]
    nlinarith [le_abs_self (y - c)]

/-- The selected vector satisfies the global convex subgradient inequality. -/
theorem hardLoss_subgradient {k : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (ρ : ℝ) (v : Fin k → ℝ) (x y : HardSpace k) :
    hardLoss a ρ v x - hardLoss a ρ v y ≤
      ⟪hardGradient a ρ v x, x - y⟫_ℝ := by
  have hb : 0 ≤ a / Real.sqrt (k : ℝ) := div_nonneg ha (Real.sqrt_nonneg _)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    mul_le_mul_of_nonneg_left (scalar_abs_subgradient (x j) (y j) (ρ * v j)) hb)
  simpa [hardLoss, hardGradient, PiLp.inner_apply, Finset.mul_sum,
    Finset.sum_sub_distrib, mul_sub, sub_mul, mul_assoc, mul_comm] using h

theorem hardGradient_norm_le {k : ℕ} (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a)
    (ρ : ℝ) (v : Fin k → ℝ) (x : HardSpace k) : ‖hardGradient a ρ v x‖ ≤ a := by
  have hcoordinate (j : Fin k) :
      ((a / Real.sqrt (k : ℝ)) * Real.sign (x j - ρ * v j)) ^ 2 ≤
        (a / Real.sqrt (k : ℝ)) ^ 2 := by
    rcases Real.sign_apply_eq (x j - ρ * v j) with h | h | h
    · rw [h]; simp
    · rw [h]; simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · rw [h]; simp
  have hnorm : ‖hardGradient a ρ v x‖ ^ 2 ≤ a ^ 2 := by
    rw [hardSpace_norm_sq]
    calc
      (∑ j, (hardGradient a ρ v x j) ^ 2) ≤
          ∑ _ : Fin k, (a / Real.sqrt (k : ℝ)) ^ 2 :=
        Finset.sum_le_sum (fun j _ ↦ hcoordinate j)
      _ = (k : ℝ) * (a / Real.sqrt (k : ℝ)) ^ 2 := by simp
      _ = a ^ 2 := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
        have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
        field_simp
  nlinarith [norm_nonneg (hardGradient a ρ v x)]

theorem hardLoss_difference_bound {k : ℕ} (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a)
    (ρ : ℝ) (v : Fin k → ℝ) (x y : HardSpace k) :
    hardLoss a ρ v x - hardLoss a ρ v y ≤ a * ‖x - y‖ := by
  calc
    _ ≤ ⟪hardGradient a ρ v x, x - y⟫_ℝ := hardLoss_subgradient ha ρ v x y
    _ ≤ ‖hardGradient a ρ v x‖ * ‖x - y‖ := real_inner_le_norm _ _
    _ ≤ a * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (hardGradient_norm_le hk ha ρ v x) (norm_nonneg _)

/-- The unknown loss has the required global Euclidean Lipschitz constant. -/
theorem hardLoss_lipschitz {k : ℕ} (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a)
    (ρ : ℝ) (v : Fin k → ℝ) : LipschitzWith ⟨a, ha⟩ (hardLoss a ρ v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  change |hardLoss a ρ v x - hardLoss a ρ v y| ≤ a * ‖x - y‖
  apply abs_le.mpr
  constructor
  · have h := hardLoss_difference_bound hk ha ρ v y x
    rw [norm_sub_rev] at h
    linarith
  · exact hardLoss_difference_bound hk ha ρ v x y

theorem hardLoss_convex {k : ℕ} {a : ℝ} (ha : 0 ≤ a) (ρ : ℝ) (v : Fin k → ℝ) :
    ConvexOn ℝ Set.univ (hardLoss a ρ v) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy α β hα hβ hsum
  let z := α • x + β • y
  have hvec : α • (z - x) + β • (z - y) = 0 := by
    have hβ' : β = 1 - α := by linarith
    dsimp [z]
    rw [hβ']
    module
  have hinner : α * ⟪hardGradient a ρ v z, z - x⟫_ℝ +
      β * ⟪hardGradient a ρ v z, z - y⟫_ℝ = 0 := by
    calc
      _ = ⟪hardGradient a ρ v z, α • (z - x) + β • (z - y)⟫_ℝ := by
        simp [inner_add_right, inner_smul_right]
      _ = 0 := by rw [hvec]; simp
  have hx' := mul_le_mul_of_nonneg_left (hardLoss_subgradient ha ρ v z x) hα
  have hy' := mul_le_mul_of_nonneg_left (hardLoss_subgradient ha ρ v z y) hβ
  have hzsum : α * hardLoss a ρ v z + β * hardLoss a ρ v z = hardLoss a ρ v z := by
    rw [← add_mul, hsum, one_mul]
  change hardLoss a ρ v z ≤ α * hardLoss a ρ v x + β * hardLoss a ρ v y
  linarith only [hx', hy', hinner, hzsum]

theorem real_sign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

theorem hardGradient_measurable {k : ℕ} (a ρ : ℝ) (v : Fin k → ℝ) :
    Measurable (hardGradient a ρ v) := by
  apply (PiLp.continuous_equiv_symm (p := 2) (β := fun _ : Fin k ↦ ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro j
  have hj : Measurable (fun x : HardSpace k ↦ x j) :=
    (EuclideanSpace.proj j).continuous.measurable
  exact (real_sign_measurable.comp (hj.sub_const (ρ * v j))).const_mul _

theorem hardRegularizer_strongConvex {k : ℕ} (μ : ℝ) :
    StrongConvexOn (Set.univ : Set (HardSpace k)) μ (hardRegularizer μ) := by
  rw [strongConvexOn_iff_convex]
  simpa only [hardRegularizer, sub_self] using
    (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (HardSpace k))))

theorem hardRegularizer_convex {k : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) :
    ConvexOn ℝ (Set.univ : Set (HardSpace k)) (hardRegularizer μ) :=
  strongConvexOn_zero.mp ((hardRegularizer_strongConvex μ).mono hμ)

theorem hardComposite_eq_signObjective {k : ℕ} (a μ ρ : ℝ) (v : Fin k → ℝ)
    (x : HardSpace k) :
    hardLoss a ρ v x + hardRegularizer μ x =
      signObjective (a / Real.sqrt (k : ℝ)) μ ρ v (fun j ↦ x j) := by
  simp only [hardLoss, hardRegularizer, hardSpace_norm_sq,
    signObjective, coordinateSignLoss, Finset.sum_add_distrib, Finset.mul_sum]

noncomputable def hardCenter {k : ℕ} (μ D a : ℝ) (v : Fin k → ℝ) : HardSpace k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun j ↦ envelopeRadius μ D a / Real.sqrt (k : ℝ) * v j)

theorem hardComposite_minimizer {k : ℕ} (hk : 0 < k) {μ D a : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (v : Fin k → ℝ) (hv : ∀ j, v j = -1 ∨ v j = 1) (x : HardSpace k) :
    hardLoss a (envelopeRadius μ D a / Real.sqrt (k : ℝ)) v (hardCenter μ D a v) +
      hardRegularizer μ (hardCenter μ D a v) ≤
    hardLoss a (envelopeRadius μ D a / Real.sqrt (k : ℝ)) v x + hardRegularizer μ x := by
  rw [hardComposite_eq_signObjective, hardComposite_eq_signObjective]
  exact manuscript_sign_minimizer hk hμ hD ha hv (fun j ↦ x j)

theorem hardCenter_initialization {k : ℕ} (hk : 0 < k) {μ D a : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (v : Fin k → ℝ) (hv : ∀ j, v j = -1 ∨ v j = 1) :
    ‖hardCenter μ D a v‖ ≤ D := by
  have hsq : ‖hardCenter μ D a v‖ ^ 2 ≤ D ^ 2 := by
    rw [hardSpace_norm_sq]
    exact manuscript_center_initialization hk hμ hD ha hv
  nlinarith [norm_nonneg (hardCenter μ D a v)]

theorem hardComposite_loss_hamming {k : ℕ} (hk : 0 < k) {μ D a : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (v : Fin k → ℝ) (hv : ∀ j, v j = -1 ∨ v j = 1) (x : HardSpace k) :
    envelope μ D a / k * (signHamming v (fun j ↦ x j) : ℝ) ≤
      (hardLoss a (envelopeRadius μ D a / Real.sqrt (k : ℝ)) v x + hardRegularizer μ x) -
      (hardLoss a (envelopeRadius μ D a / Real.sqrt (k : ℝ)) v (hardCenter μ D a v) +
        hardRegularizer μ (hardCenter μ D a v)) := by
  rw [hardComposite_eq_signObjective, hardComposite_eq_signObjective]
  exact manuscript_loss_hamming hk hμ hD ha hv (fun j ↦ x j)

end HeavyTail
