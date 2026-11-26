import MatchingBounds1005.GaussianProduct
import MatchingBounds1005.InnovationGaussianKL

/-!
# Orthogonal projections of independent Gaussian coordinate blocks

The coordinate splitting used for the actual Gaussian product law is linear
and preserves the sum of the block inner products. Consequently the fitted
projection and unobserved residual split into their two physical channels.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.GaussianBlockProjection
open GaussianVector GaussianProduct AdaptiveGaussian InnovationGaussianKL

def splitLinearEquiv (a b : ℕ) : Vec (a + b) ≃ₗ[ℝ] (Vec a × Vec b) where
  toEquiv := (splitEquiv a b).toEquiv
  map_add' x y := by
    apply Prod.ext
    · ext i
      change (splitEquiv a b (x + y)).1 i = (splitEquiv a b x).1 i + (splitEquiv a b y).1 i
      simp only [splitEquiv_fst]
      rfl
    · ext i
      change (splitEquiv a b (x + y)).2 i = (splitEquiv a b x).2 i + (splitEquiv a b y).2 i
      simp only [splitEquiv_snd]
      rfl
  map_smul' c x := by
    apply Prod.ext
    · ext i
      change (splitEquiv a b (c • x)).1 i = c * (splitEquiv a b x).1 i
      simp only [splitEquiv_fst]
      rfl
    · ext i
      change (splitEquiv a b (c • x)).2 i = c * (splitEquiv a b x).2 i
      simp only [splitEquiv_snd]
      rfl

theorem splitLinearEquiv_apply (a b : ℕ) (z : Vec (a + b)) :
    splitLinearEquiv a b z = splitEquiv a b z := rfl

theorem inner_split (a b : ℕ) (z w : Vec (a + b)) :
    ⟪z, w⟫_ℝ = ⟪(splitLinearEquiv a b z).1, (splitLinearEquiv a b w).1⟫_ℝ +
      ⟪(splitLinearEquiv a b z).2, (splitLinearEquiv a b w).2⟫_ℝ := by
  simp only [splitLinearEquiv_apply, PiLp.inner_apply, splitEquiv_fst, splitEquiv_snd]
  exact Fin.sum_univ_add (fun i : Fin (a + b) => ⟪z i, w i⟫_ℝ)

def blockSpace {a b : ℕ} (V : Submodule ℝ (Vec a)) (W : Submodule ℝ (Vec b)) :
    Submodule ℝ (Vec (a + b)) := (V.prod W).comap (splitLinearEquiv a b).toLinearMap

theorem mem_blockSpace {a b : ℕ} (V : Submodule ℝ (Vec a)) (W : Submodule ℝ (Vec b))
    (z : Vec (a + b)) : z ∈ blockSpace V W ↔
      (splitLinearEquiv a b z).1 ∈ V ∧ (splitLinearEquiv a b z).2 ∈ W := Iff.rfl

theorem residual_inner {a : ℕ} (V : Submodule ℝ (Vec a)) (x y : Vec a) (hy : y ∈ V) :
    ⟪x - projection V x, y⟫_ℝ = 0 :=
  Submodule.orthogonalProjection_inner_eq_zero x y hy

theorem projection_val {a : ℕ} (V : Submodule ℝ (Vec a)) (x : Vec a) :
    projection V x = (V.orthogonalProjection x : Vec a) := rfl

attribute [local irreducible] projection Submodule.orthogonalProjection

/-- Both fitted blocks are exactly their individual orthogonal projections. -/
theorem block_projection {a b : ℕ} (V : Submodule ℝ (Vec a)) (W : Submodule ℝ (Vec b))
    (z : Vec (a + b)) :
    projection (blockSpace V W) z = (splitLinearEquiv a b).symm
      (projection V (splitLinearEquiv a b z).1, projection W (splitLinearEquiv a b z).2) := by
  rw [projection_val (blockSpace V W) z]
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero
  · rw [mem_blockSpace, LinearEquiv.apply_symm_apply]
    exact ⟨projection_mem V _, projection_mem W _⟩
  · intro u hu
    have hu' := (mem_blockSpace V W u).mp hu
    rw [inner_split, map_sub, LinearEquiv.apply_symm_apply]
    change ⟪(splitLinearEquiv a b z).1 - projection V (splitLinearEquiv a b z).1,
      (splitLinearEquiv a b u).1⟫_ℝ +
      ⟪(splitLinearEquiv a b z).2 - projection W (splitLinearEquiv a b z).2,
        (splitLinearEquiv a b u).2⟫_ℝ = 0
    rw [residual_inner V _ _ hu'.1, residual_inner W _ _ hu'.2, add_zero]

theorem block_projection_split {a b : ℕ} (V : Submodule ℝ (Vec a)) (W : Submodule ℝ (Vec b))
    (z : Vec (a + b)) :
    splitLinearEquiv a b (projection (blockSpace V W) z) =
      (projection V (splitLinearEquiv a b z).1, projection W (splitLinearEquiv a b z).2) := by
  rw [block_projection, LinearEquiv.apply_symm_apply]

theorem block_projection_energy {a b : ℕ} (V : Submodule ℝ (Vec a)) (W : Submodule ℝ (Vec b))
    (z : Vec (a + b)) :
    ‖projection (blockSpace V W) z‖ ^ 2 =
      ‖projection V (splitLinearEquiv a b z).1‖ ^ 2 +
        ‖projection W (splitLinearEquiv a b z).2‖ ^ 2 := by
  have h := splitEquiv_norm_sq a b (projection (blockSpace V W) z)
  change ‖projection (blockSpace V W) z‖ ^ 2 =
    ‖(splitLinearEquiv a b (projection (blockSpace V W) z)).1‖ ^ 2 +
      ‖(splitLinearEquiv a b (projection (blockSpace V W) z)).2‖ ^ 2 at h
  rw [block_projection_split] at h
  exact h

theorem blockSpace_orthogonal {a b : ℕ} (V : Submodule ℝ (Vec a)) (W : Submodule ℝ (Vec b)) :
    blockSpace Vᗮ Wᗮ = (blockSpace V W)ᗮ := by
  ext z
  rw [mem_blockSpace, ← projection_zero_iff V, ← projection_zero_iff W,
    ← projection_zero_iff (blockSpace V W), block_projection]
  constructor
  · rintro ⟨hV, hW⟩
    rw [hV, hW]
    exact map_zero (splitLinearEquiv a b).symm
  · intro hz
    have h := congrArg (splitLinearEquiv a b) hz
    rw [LinearEquiv.apply_symm_apply, map_zero] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem blockSpace_inf {a b : ℕ} (V₁ V₂ : Submodule ℝ (Vec a))
    (W₁ W₂ : Submodule ℝ (Vec b)) :
    blockSpace V₁ W₁ ⊓ blockSpace V₂ W₂ = blockSpace (V₁ ⊓ V₂) (W₁ ⊓ W₂) := by
  ext z
  change ((_ ∈ V₁ ∧ _ ∈ W₁) ∧ (_ ∈ V₂ ∧ _ ∈ W₂)) ↔ ((_ ∈ V₁ ∧ _ ∈ V₂) ∧ (_ ∈ W₁ ∧ _ ∈ W₂))
  tauto

end MatchingBounds1005.GaussianBlockProjection
