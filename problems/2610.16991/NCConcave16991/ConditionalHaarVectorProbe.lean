import NCConcave16991.ConditionalHaarProbe

/-! # Actual conditional Haar moments for observation-dependent physical vectors -/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.Haar

noncomputable section

theorem inner_eq_probe {k : ℕ} (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (j : Fin k) (Q : OrthogonalGroup k) :
    ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ =
      probe (fun i Q ↦ a Q i) j Q := by
  simp [PiLp.inner_apply, RCLike.inner_apply, probe, entry, mul_comm]

theorem observed_coordinate_stronglyMeasurable {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) (i : Fin k) :
    StronglyMeasurable[columnSigma A] (fun Q ↦ a Q i) :=
  ((PiLp.continuous_apply 2 _ i).measurable.comp ha.measurable).stronglyMeasurable

/-- The query vector may depend arbitrarily on the already revealed images;
it is not conditioned on a future response. Its genuinely unrevealed Haar
inner product has conditional mean zero. -/
theorem conditional_inner_mean_zero {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) {C : ℝ} (hb : ∀ Q, ‖a Q‖ ≤ C)
    (j : Fin k) (hj : j ∉ A) :
    (haarLaw k)[(fun Q ↦ ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ) | columnSigma A]
      =ᵐ[haarLaw k] fun _ ↦ (0:ℝ) := by
  have he : (fun Q ↦ ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ) =
      probe (fun i Q ↦ a Q i) j := funext (inner_eq_probe a j)
  rw [he]
  exact conditional_probe_mean_zero A _
    (observed_coordinate_stronglyMeasurable A a ha)
    (fun i Q ↦ (PiLp.norm_apply_le (a Q) i).trans (hb Q)) j hj

/-- The exact residual-projector conditional variance, for a physical probe
chosen measurably from the actual observed images. -/
theorem conditional_inner_second_moment {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ Q, ‖a Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) :
    (haarLaw k)[(fun Q ↦ ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ ^ 2) | columnSigma A]
      =ᵐ[haarLaw k] fun Q ↦ (‖a Q‖ ^ 2 -
        ∑ l : A, ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector l.val)⟫_ℝ ^ 2) / (Aᶜ.card : ℝ) := by
  have he : (fun Q ↦ ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ ^ 2) =
      fun Q ↦ probe (fun i Q ↦ a Q i) j Q ^ 2 := by
    funext Q
    rw [inner_eq_probe]
  rw [he]
  have hh := conditional_probe_variance_formula A (fun i Q ↦ a Q i) hC
    (observed_coordinate_stronglyMeasurable A a ha)
    (fun i Q ↦ (PiLp.norm_apply_le (a Q) i).trans (hb Q)) j hj
  apply hh.trans
  filter_upwards with Q
  simp_rw [← inner_eq_probe a]
  rw [← EuclideanSpace.real_norm_sq_eq]

theorem conditional_inner_second_moment_bound {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ Q, ‖a Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) :
    ∀ᵐ Q ∂haarLaw k,
      ((haarLaw k)[(fun Q ↦ ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ ^ 2) | columnSigma A]) Q ≤
        C ^ 2 / (Aᶜ.card : ℝ) := by
  filter_upwards [conditional_inner_second_moment A a ha hC hb j hj] with Q hQ
  rw [hQ]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsum : 0 ≤ ∑ l : A, ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector l.val)⟫_ℝ ^ 2 :=
    Finset.sum_nonneg (fun l _ ↦ sq_nonneg _)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (hb Q) 2
  linarith

end

end NCConcave16991.Haar
