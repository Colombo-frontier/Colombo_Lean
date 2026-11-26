import MatchingBounds1005.ChainCopies
import MatchingBounds1005.ChainPositive
import MatchingBounds1005.ChainRadial
import MatchingBounds1005.SymmetricQuadratic

/-! Actual inactive quadratic copies. The objective, gradient, gap, and radial
bounds are proved on the same canonical copy space used by the spectral module. -/
noncomputable section
open scoped InnerProductSpace BigOperators ContDiff

namespace MatchingBounds1005.BlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

def copyProjection (n K : ℕ) (j : Fin (K + 1)) :
    CopySpace (E := E) n K →L[ℝ] BlockSpace (E := E) n :=
  PiLp.proj 2 (fun _ : Fin (K + 1) => BlockSpace (E := E) n) j

theorem copyProjection_norm_le (n K : ℕ) (j : Fin (K + 1)) :
    ‖copyProjection (E := E) n K j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simpa only [one_mul] using PiLp.norm_apply_le z j

theorem chainOperator_pair_symmetric (n : ℕ) (x y : BlockSpace (E := E) n) :
    ⟪x, G.chainOperator n y⟫_ℝ = ⟪G.chainOperator n x, y⟫_ℝ :=
  ((G.chainOperator_symmetric n) x y).symm

def decoyObjective (r : ℝ) (n K : ℕ) (z : CopySpace (E := E) n K) : ℝ :=
  G.euclideanObjective r n (z 0) +
    ∑ j : Fin K, SymmetricQuadratic.energy (G.chainOperator n) 0 (z j.succ)

theorem inactive_energy (n : ℕ) (z : BlockSpace (E := E) n) :
    SymmetricQuadratic.energy (G.chainOperator n) 0 z = (1 / 2 : ℝ) * G.chainBilinear n z z := by
  simp only [SymmetricQuadratic.energy, ContinuousLinearMap.zero_apply, add_zero]
  rw [real_inner_comm (G.chainOperator n z) z, G.chainOperator_inner]

theorem inactive_energy_nonneg (n : ℕ) (z : BlockSpace (E := E) n) :
    0 ≤ SymmetricQuadratic.energy (G.chainOperator n) 0 z := by
  rw [G.inactive_energy]
  exact mul_nonneg (by norm_num) (G.chainBilinear_nonneg n z)

def decoyGradient (r : ℝ) (n K : ℕ) (z : CopySpace (E := E) n K) : CopySpace (E := E) n K :=
  (WithLp.equiv 2 _).symm (Fin.cases (G.euclideanGradient r n (z 0))
    (fun j => G.chainOperator n (z j.succ)))

theorem decoyObjective_hasFDerivAt (r : ℝ) (n K : ℕ) (z : CopySpace (E := E) n K) :
    HasFDerivAt (G.decoyObjective r n K) (innerSL ℝ (G.decoyGradient r n K z)) z := by
  have ha := (G.euclideanObjective_hasFDerivAt r n (z 0)).comp z
    (copyProjection (E := E) n K 0).hasFDerivAt
  have ho : ∀ j : Fin K, HasFDerivAt
      (fun y : CopySpace (E := E) n K => SymmetricQuadratic.energy (G.chainOperator n) 0 (y j.succ))
      ((innerSL ℝ (G.chainOperator n (z j.succ))).comp (copyProjection n K j.succ)) z := by
    intro j
    have h := (SymmetricQuadratic.hasFDerivAt (G.chainOperator n) 0
      (G.chainOperator_pair_symmetric n) (z j.succ)).comp z
        (copyProjection (E := E) n K j.succ).hasFDerivAt
    simpa only [add_zero] using h
  have h := ha.add (HasFDerivAt.sum (u := Finset.univ) (fun j _ => ho j))
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply, copyProjection, PiLp.proj_apply]
  change ⟪G.decoyGradient r n K z, v⟫_ℝ =
    ⟪G.euclideanGradient r n (z 0), v 0⟫_ℝ + ∑ j : Fin K, ⟪G.chainOperator n (z j.succ), v j.succ⟫_ℝ
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp [decoyGradient]

theorem decoyObjective_gradient (r : ℝ) (n K : ℕ) (z : CopySpace (E := E) n K) :
    gradient (G.decoyObjective r n K) z = G.decoyGradient r n K z := by
  have h : HasGradientAt (G.decoyObjective r n K) (G.decoyGradient r n K z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact G.decoyObjective_hasFDerivAt r n K z
  exact h.gradient

theorem active_gradient_le_decoy (r : ℝ) (n K : ℕ) (z : CopySpace (E := E) n K) :
    ‖gradient (G.euclideanObjective r n) (z 0)‖ ≤ ‖gradient (G.decoyObjective r n K) z‖ := by
  rw [G.euclideanObjective_gradient, G.decoyObjective_gradient]
  have h := PiLp.norm_apply_le (G.decoyGradient r n K z) 0
  simpa [decoyGradient] using h

theorem decoyObjective_gap (r : ℝ) (hr : 1 ≤ r) (n K : ℕ) (z : CopySpace (E := E) n K) :
    G.decoyObjective r n K 0 - G.decoyObjective r n K z ≤
      10 * (n + 1 : ℕ) * G.tau + G.kappa / 2 := by
  have h := G.euclideanObjective_gap r hr n (z 0)
  have hp : 0 ≤ ∑ j : Fin K, SymmetricQuadratic.energy (G.chainOperator n) 0 (z j.succ) :=
    Finset.sum_nonneg (fun j _ => G.inactive_energy_nonneg n _)
  simp only [decoyObjective, PiLp.zero_apply, SymmetricQuadratic.energy,
    map_zero, inner_zero_left, mul_zero, ContinuousLinearMap.zero_apply,
    add_zero, Finset.sum_const_zero] at hp ⊢
  linarith

theorem decoyObjective_radial_gap (r : ℝ) (hr : 1 ≤ r) (n K : ℕ) (z : CopySpace (E := E) n K) :
    -(81 / 64 : ℝ) * (10 * (n + 1 : ℕ) * G.tau + G.kappa / 2) ≤
      ⟪z, gradient (G.decoyObjective r n K) z⟫_ℝ := by
  rw [G.decoyObjective_gradient, PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [decoyGradient, WithLp.equiv_symm_pi_apply, Fin.cases_zero, Fin.cases_succ]
  have hp : 0 ≤ ∑ j : Fin K, ⟪z j.succ, G.chainOperator n (z j.succ)⟫_ℝ := by
    apply Finset.sum_nonneg
    intro j _
    rw [real_inner_comm (G.chainOperator n (z j.succ)) (z j.succ), G.chainOperator_inner]
    exact G.chainBilinear_nonneg n _
  have h := G.euclideanObjective_radial_gap r hr n (z 0)
  rw [G.euclideanObjective_gradient] at h
  linarith

end MatchingBounds1005.BlockGeometry
