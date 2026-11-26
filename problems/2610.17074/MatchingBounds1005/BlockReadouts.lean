import MatchingBounds1005.BlockGradientBound
import MatchingBounds1005.OrthogonalReadouts

/-! Orthogonal ridge estimates instantiated on the actual Euclidean blocks. -/
noncomputable section
namespace MatchingBounds1005.BlockGeometry

open scoped ContDiff InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def normalizedBlockReadout (n : ℕ) (a : E) (A : ℝ) (i : Fin (n + 1)) :
    BlockSpace (E := E) n := (WithLp.equiv 2 _).symm (Pi.single i (A⁻¹ • a))

theorem normalizedBlockReadout_inner (n : ℕ) (a : E) (A : ℝ)
    (i : Fin (n + 1)) (z : BlockSpace (E := E) n) :
    ⟪normalizedBlockReadout n a A i, z⟫_ℝ = A⁻¹ * ⟪a, z i⟫_ℝ := by
  simp only [normalizedBlockReadout, PiLp.inner_apply, WithLp.equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  · simp [real_inner_smul_left]
  · intro j _ hji
    simp [Pi.single_apply, hji]
  · simp

theorem normalizedBlockReadout_orthonormal (n : ℕ) {a : E} {A : ℝ}
    (hA : 0 < A) (ha : ‖a‖ = A) :
    Orthonormal ℝ (normalizedBlockReadout n a A) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [normalizedBlockReadout_inner]
  by_cases hij : i = j
  · subst j
    simp only [normalizedBlockReadout, WithLp.equiv_symm_pi_apply, Pi.single_eq_same,
      real_inner_smul_right, real_inner_self_eq_norm_sq, ha, if_pos rfl]
    field_simp
    ring
  · simp [normalizedBlockReadout, Pi.single_apply, hij]

variable (G : BlockGeometry E)

def euclideanPotential (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n) : ℝ :=
  G.tau * ∑ i, Primitive.potential r ⟪G.a, z i⟫_ℝ

theorem euclideanPotential_eq_ridge {A : ℝ} (hA : 0 < A) (r : ℝ) (n : ℕ) :
    G.euclideanPotential r n = fun z =>
      G.tau * ridgeSum (normalizedBlockReadout n G.a A) (Primitive.potential r) A z := by
  funext z
  unfold euclideanPotential ridgeSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [normalizedBlockReadout_inner]
  congr 1
  field_simp

theorem euclideanPotential_smooth (r : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (G.euclideanPotential r n) := by
  unfold euclideanPotential
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i _
  let pr : BlockSpace (E := E) n →L[ℝ] E :=
    PiLp.proj 2 (fun _ : Fin (n + 1) => E) i
  change ContDiff ℝ ∞ (Primitive.potential r ∘ ((innerSL ℝ G.a) ∘ pr))
  exact (Primitive.potential_smooth r).comp
    ((innerSL ℝ G.a).contDiff.comp pr.contDiff)

/-- Concrete block potential, with no factor depending on the number of blocks. -/
theorem euclideanPotential_derivative_bound {A : ℝ} (hA : 0 < A) (ha : ‖G.a‖ = A)
    (r : ℝ) (n k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |iteratedDeriv (k + 2) (Primitive.potential r) u| ≤ C)
    (z : BlockSpace (E := E) n) :
    ‖iteratedFDeriv ℝ (k + 2) (G.euclideanPotential r n) z‖ ≤
      |G.tau| * C * A ^ (k + 2) := by
  rw [G.euclideanPotential_eq_ridge hA]
  have hlevel : ((k + 2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    generalize k + 2 = j
    exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have hs := (ridgeSum_smooth (normalizedBlockReadout n G.a A)
    (Primitive.potential_smooth r) A).of_le hlevel
  change ‖iteratedFDeriv ℝ (k + 2)
    (G.tau • ridgeSum (normalizedBlockReadout n G.a A) (Primitive.potential r) A) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply hs.contDiffAt,
    norm_smul G.tau (iteratedFDeriv ℝ (k + 2)
      (ridgeSum (normalizedBlockReadout n G.a A) (Primitive.potential r) A) z), Real.norm_eq_abs]
  have h := ridgeSum_derivative_bound (normalizedBlockReadout n G.a A)
    (normalizedBlockReadout_orthonormal n hA ha) (Primitive.potential_smooth r) A k C hC hb z
  rw [abs_of_pos hA] at h
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg G.tau)).trans_eq (by ring)

end MatchingBounds1005.BlockGeometry
