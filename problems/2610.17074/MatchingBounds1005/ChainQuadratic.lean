import MatchingBounds1005.PathCalibration
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual chain quadratic, its Hessian, and dimension-free operator bounds. -/
noncomputable section
open scoped BigOperators InnerProductSpace ContDiff

namespace MatchingBounds1005.BlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

def chainBilinearLinear (n : ℕ) : BlockSpace (E := E) n →ₗ[ℝ] BlockSpace (E := E) n →ₗ[ℝ] ℝ where
  toFun z :=
    { toFun := fun v =>
        (∑ i, ⟪z i, G.H (v i)⟫_ℝ) + G.kappa * (∑ i, ⟪G.a, z i⟫_ℝ * ⟪G.a, v i⟫_ℝ) -
          G.lam * (∑ i : Fin n, (⟪G.a, z i.castSucc⟫_ℝ * ⟪G.e, v i.succ⟫_ℝ +
            ⟪G.a, v i.castSucc⟫_ℝ * ⟪G.e, z i.succ⟫_ℝ))
      map_add' := by
        intro v w
        simp only [PiLp.add_apply, map_add, inner_add_right, mul_add, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c v
        simp only [PiLp.smul_apply, map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        simp only [Finset.mul_sum, Finset.sum_mul, mul_add, mul_sub]
        simp only [mul_assoc, mul_left_comm, mul_comm] }
  map_add' := by
    intro z w
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, PiLp.add_apply, inner_add_left, inner_add_right, mul_add, add_mul,
      Finset.sum_add_distrib, LinearMap.add_apply]
    ring
  map_smul' := by
    intro c z
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, PiLp.smul_apply, real_inner_smul_left, inner_smul_right,
      smul_eq_mul, RingHom.id_apply, LinearMap.smul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_add, mul_sub]
    simp only [mul_assoc, mul_left_comm, mul_comm]

def chainBilinear (n : ℕ) : BlockSpace (E := E) n →L[ℝ] BlockSpace (E := E) n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (G.chainBilinearLinear n))

theorem chainBilinear_apply (n : ℕ) (z v : BlockSpace (E := E) n) :
    G.chainBilinear n z v =
      (∑ i, ⟪z i, G.H (v i)⟫_ℝ) + G.kappa * (∑ i, ⟪G.a, z i⟫_ℝ * ⟪G.a, v i⟫_ℝ) -
        G.lam * (∑ i : Fin n, (⟪G.a, z i.castSucc⟫_ℝ * ⟪G.e, v i.succ⟫_ℝ +
          ⟪G.a, v i.castSucc⟫_ℝ * ⟪G.e, z i.succ⟫_ℝ)) := rfl

attribute [irreducible] chainBilinearLinear chainBilinear

theorem chainBilinear_symmetric (n : ℕ) (z v : BlockSpace (E := E) n) :
    G.chainBilinear n z v = G.chainBilinear n v z := by
  simp only [G.chainBilinear_apply]
  have hd : (∑ i, ⟪z i, G.H (v i)⟫_ℝ) = ∑ i, ⟪v i, G.H (z i)⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [G.symmetric, real_inner_comm]
  rw [hd]
  simp only [mul_comm, add_comm]

def firstEntry (n : ℕ) : BlockSpace (E := E) n →L[ℝ] ℝ :=
  (innerSL ℝ G.e).comp (PiLp.proj 2 (fun _ : Fin (n + 1) => E) 0)

def euclideanQuadratic (n : ℕ) (z : BlockSpace (E := E) n) : ℝ :=
  (1 / 2 : ℝ) * G.chainBilinear n z z - G.lam * G.firstEntry n z

theorem euclideanQuadratic_smooth (n : ℕ) : ContDiff ℝ ∞ (G.euclideanQuadratic n) := by
  have hB : ContDiff ℝ ∞ (G.chainBilinear n : BlockSpace (E := E) n →
      BlockSpace (E := E) n →L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := BlockSpace (E := E) n)
      (F := BlockSpace (E := E) n →L[ℝ] ℝ) (G.chainBilinear n)
  have hdiag : ContDiff ℝ ∞ (fun z => G.chainBilinear n z z) := hB.clm_apply contDiff_id
  exact (contDiff_const.mul hdiag).sub (contDiff_const.mul (G.firstEntry n).contDiff)

theorem euclideanObjective_decomposition (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n) :
    G.euclideanObjective r n z = G.euclideanQuadratic n z +
      G.tau * ∑ i, Primitive.potential r ⟪G.a, z i⟫_ℝ := by
  simp only [euclideanObjective, objective, localEnergy, sectionEnergy, quadraticBlock,
    euclideanQuadratic, G.chainBilinear_apply, firstEntry,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, innerSL_apply,
    zero_mul, mul_zero, zero_smul, sub_zero, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← pow_two]
  ring

theorem euclideanQuadratic_hasFDerivAt (n : ℕ) (z : BlockSpace (E := E) n) :
    HasFDerivAt (G.euclideanQuadratic n)
      (G.chainBilinear n z - G.lam • G.firstEntry n) z := by
  have hid := hasFDerivAt_id (𝕜 := ℝ) z
  have h := (((G.chainBilinear n).hasFDerivAt_of_bilinear hid hid).const_mul (1 / 2 : ℝ)).sub
    ((G.firstEntry n).hasFDerivAt.const_mul G.lam)
  convert h using 1
  ext v
  change G.chainBilinear n z v - G.lam * G.firstEntry n v =
    (1 / 2 : ℝ) * (G.chainBilinear n z v + G.chainBilinear n v z) -
      G.lam * G.firstEntry n v
  rw [G.chainBilinear_symmetric n v z]
  ring

theorem euclideanQuadratic_fderiv (n : ℕ) :
    fderiv ℝ (G.euclideanQuadratic n) =
      fun z => G.chainBilinear n z - G.lam • G.firstEntry n :=
  funext (fun z => (G.euclideanQuadratic_hasFDerivAt n z).fderiv)

theorem euclideanQuadratic_second_apply (n : ℕ) (z : BlockSpace (E := E) n)
    (v : Fin 2 → BlockSpace (E := E) n) :
    iteratedFDeriv ℝ 2 (G.euclideanQuadratic n) z v = G.chainBilinear n (v 0) (v 1) := by
  rw [iteratedFDeriv_two_apply, G.euclideanQuadratic_fderiv]
  have hB : HasFDerivAt (G.chainBilinear n : BlockSpace (E := E) n →
      BlockSpace (E := E) n →L[ℝ] ℝ) (G.chainBilinear n) z :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := BlockSpace (E := E) n)
      (F := BlockSpace (E := E) n →L[ℝ] ℝ) (G.chainBilinear n) (x := z)
  have hsub := hB.sub (hasFDerivAt_const (𝕜 := ℝ) (G.lam • G.firstEntry n) z)
  have hf : fderiv ℝ (fun y => G.chainBilinear n y - G.lam • G.firstEntry n) z =
      G.chainBilinear n := by simpa only [sub_zero] using hsub.fderiv
  rw [hf]

theorem euclideanQuadratic_higher_zero (n k : ℕ) :
    iteratedFDeriv ℝ (k + 3) (G.euclideanQuadratic n) = 0 := by
  have hconst : iteratedFDeriv ℝ 2 (G.euclideanQuadratic n) =
      fun _ => iteratedFDeriv ℝ 2 (G.euclideanQuadratic n) 0 := by
    funext z
    ext v
    rw [G.euclideanQuadratic_second_apply, G.euclideanQuadratic_second_apply]
  induction k with
  | zero =>
    funext z
    ext v
    rw [iteratedFDeriv_succ_apply_left, hconst]
    simp
  | succ k ih =>
    funext z
    ext v
    change iteratedFDeriv ℝ ((k + 3) + 1) (G.euclideanQuadratic n) z v = 0
    rw [iteratedFDeriv_succ_apply_left, ih]
    simp

theorem sum_block_norm_mul (n : ℕ) (z v : BlockSpace (E := E) n) :
    (∑ i, ‖z i‖ * ‖v i‖) ≤ ‖z‖ * ‖v‖ := by
  calc
    _ ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) * Real.sqrt (∑ i, ‖v i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = _ := by rw [← PiLp.norm_sq_eq_of_L2, ← PiLp.norm_sq_eq_of_L2]; simp

theorem readout_pair_bound (a b : E) (n : ℕ) (z v : BlockSpace (E := E) n) :
    |∑ i, ⟪a, z i⟫_ℝ * ⟪b, v i⟫_ℝ| ≤ (‖a‖ * ‖b‖) * ‖z‖ * ‖v‖ := by
  have heq : (∑ i, ⟪a, z i⟫_ℝ * ⟪b, v i⟫_ℝ) =
      ⟪contraction a z, contraction b v⟫_ℝ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, ⟪a, z i⟫_ℝ * ⟪b, v i⟫_ℝ) = ∑ i, ⟪b, v i⟫_ℝ * ⟪a, z i⟫_ℝ
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  calc
    _ ≤ ‖contraction a z‖ * ‖contraction b v‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖a‖ * ‖z‖) * (‖b‖ * ‖v‖) := by
      gcongr
      · exact norm_contraction_le a z
      · exact norm_contraction_le b v
    _ = _ := by ring

theorem adjacent_readout_bound (a b : E) (n : ℕ) (z v : BlockSpace (E := E) n) :
    |∑ i : Fin n, ⟪a, z i.castSucc⟫_ℝ * ⟪b, v i.succ⟫_ℝ| ≤
      (‖a‖ * ‖b‖) * ‖z‖ * ‖v‖ := by
  have heq : (∑ i : Fin n, ⟪a, z i.castSucc⟫_ℝ * ⟪b, v i.succ⟫_ℝ) =
      ∑ i, ⟪a, z i⟫_ℝ * ⟪b, forwardShift v i⟫_ℝ := by
    rw [Fin.sum_univ_castSucc]
    simp only [forwardShift_castSucc, forwardShift_last, inner_zero_right, mul_zero, add_zero]
  rw [heq]
  exact (readout_pair_bound a b n z (forwardShift v)).trans
    (mul_le_mul_of_nonneg_left (norm_forwardShift_le v) (by positivity))

theorem chainBilinear_bound (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hH : ‖LinearMap.toContinuousLinearMap G.H‖ ≤ C) (z v : BlockSpace (E := E) n) :
    |G.chainBilinear n z v| ≤
      (C + G.kappa * ‖G.a‖ ^ 2 + 2 * G.lam * ‖G.a‖ * ‖G.e‖) * ‖z‖ * ‖v‖ := by
  have hd : |∑ i, ⟪z i, G.H (v i)⟫_ℝ| ≤ C * ‖z‖ * ‖v‖ := by
    calc
      _ ≤ ∑ i, |⟪z i, G.H (v i)⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, C * (‖z i‖ * ‖v i‖) := by
        apply Finset.sum_le_sum
        intro i _
        have hop : ‖G.H (v i)‖ ≤ C * ‖v i‖ :=
          (LinearMap.toContinuousLinearMap G.H).le_opNorm (v i) |>.trans
            (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
        exact (abs_real_inner_le_norm _ _).trans
          ((mul_le_mul_of_nonneg_left hop (norm_nonneg _)).trans_eq (by ring))
      _ = C * (∑ i, ‖z i‖ * ‖v i‖) := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (‖z‖ * ‖v‖) := mul_le_mul_of_nonneg_left (sum_block_norm_mul n z v) hC
      _ = _ := by ring
  have hr := readout_pair_bound G.a G.a n z v
  have hc₁ := adjacent_readout_bound G.a G.e n z v
  have hc₂ := adjacent_readout_bound G.a G.e n v z
  have hk := G.kappa_nonneg
  have hl := G.lam_nonneg
  rw [G.chainBilinear_apply, Finset.sum_add_distrib]
  calc
    _ ≤ (|∑ i, ⟪z i, G.H (v i)⟫_ℝ| +
        G.kappa * |∑ i, ⟪G.a, z i⟫_ℝ * ⟪G.a, v i⟫_ℝ|) +
        G.lam * (|∑ i : Fin n, ⟪G.a, z i.castSucc⟫_ℝ * ⟪G.e, v i.succ⟫_ℝ| +
          |∑ i : Fin n, ⟪G.a, v i.castSucc⟫_ℝ * ⟪G.e, z i.succ⟫_ℝ|) := by
      calc
        _ ≤ |∑ i, ⟪z i, G.H (v i)⟫_ℝ| +
            |G.kappa * ∑ i, ⟪G.a, z i⟫_ℝ * ⟪G.a, v i⟫_ℝ| +
            |G.lam * ((∑ i : Fin n, ⟪G.a, z i.castSucc⟫_ℝ * ⟪G.e, v i.succ⟫_ℝ) +
              ∑ i : Fin n, ⟪G.a, v i.castSucc⟫_ℝ * ⟪G.e, z i.succ⟫_ℝ)| :=
          (abs_sub _ _).trans (add_le_add (abs_add _ _) (le_refl _))
        _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_of_nonneg G.kappa_nonneg, abs_of_nonneg G.lam_nonneg]
          gcongr
          exact abs_add _ _
    _ ≤ (C * ‖z‖ * ‖v‖ + G.kappa * ((‖G.a‖ * ‖G.a‖) * ‖z‖ * ‖v‖)) +
        G.lam * (((‖G.a‖ * ‖G.e‖) * ‖z‖ * ‖v‖) +
          ((‖G.a‖ * ‖G.e‖) * ‖v‖ * ‖z‖)) := by
      gcongr
    _ = _ := by ring

theorem euclideanQuadratic_second_bound (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hH : ‖LinearMap.toContinuousLinearMap G.H‖ ≤ C) (z : BlockSpace (E := E) n) :
    ‖iteratedFDeriv ℝ 2 (G.euclideanQuadratic n) z‖ ≤
      C + G.kappa * ‖G.a‖ ^ 2 + 2 * G.lam * ‖G.a‖ * ‖G.e‖ := by
  have hk := G.kappa_nonneg
  have hl := G.lam_nonneg
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [G.euclideanQuadratic_second_apply, Real.norm_eq_abs]
  simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, mul_assoc] using
    G.chainBilinear_bound n C hC hH (v 0) (v 1)

/-- A positive symmetric operator's quadratic-form bound controls its true
Euclidean operator norm; no dimension factor is introduced. -/
theorem H_norm_of_energy_bound (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ⟪x, G.H x⟫_ℝ ≤ C * ‖x‖ ^ 2) :
    ‖LinearMap.toContinuousLinearMap G.H‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro x hx
  rw [← innerSL_apply_norm ℝ]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro y hy
  change |⟪G.H x, y⟫_ℝ| ≤ C
  have hnp : ‖x + y‖ ^ 2 ≤ 4 := by
    have hh := norm_add_le x y
    rw [hx, hy] at hh
    nlinarith only [hh, norm_nonneg (x + y)]
  have hnm : ‖x - y‖ ^ 2 ≤ 4 := by
    have hh := norm_sub_le x y
    rw [hx, hy] at hh
    nlinarith only [hh, norm_nonneg (x - y)]
  have hp := (hbound (x + y)).trans (mul_le_mul_of_nonneg_left hnp hC)
  have hm := (hbound (x - y)).trans (mul_le_mul_of_nonneg_left hnm hC)
  have hp₀ := G.positive (x + y)
  have hm₀ := G.positive (x - y)
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, G.symmetric x y,
    real_inner_comm y (G.H x)] at hp hm hp₀ hm₀
  have hc : ⟪G.H x, y⟫_ℝ = ⟪y, G.H x⟫_ℝ := real_inner_comm _ _
  rw [hc]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end MatchingBounds1005.BlockGeometry

namespace MatchingBounds1005.PathGreen
variable (L h A : ℝ) (hL : 0 < L) (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (hA : 0 < A)
local notation "G" => actualBlockGeometry L h A hL hh hhsmall hA

theorem actual_H_norm : ‖LinearMap.toContinuousLinearMap (G).H‖ ≤ L * (h ^ 2 + 4) := by
  apply (G).H_norm_of_energy_bound _ (by positivity)
  intro x
  rw [PiLp.norm_sq_eq_of_L2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simpa only [actualBlockGeometry, Real.norm_eq_abs, sq_abs] using
    (pathMatrix_energy_bounds L h hL.le (pathEdges h) (fun i => x i)).2

/-- The manuscript's quadratic allowance, including the extra `γ` from the
conservative and directly verified bound `‖H‖ ≤ 4L+γ`. -/
theorem actual_quadratic_second_bound (n : ℕ)
    (z : BlockGeometry.BlockSpace (E := EuclideanSpace ℝ (Fin (pathEdges h + 1))) n) :
    ‖iteratedFDeriv ℝ 2 ((G).euclideanQuadratic n) z‖ ≤
      4 * L + 2593 * (L * h ^ 2) + 18 * Real.sqrt 2 * L * h * Real.sqrt h := by
  have hb := (G).euclideanQuadratic_second_bound n (L * (h ^ 2 + 4)) (by positivity)
    (actual_H_norm L h A hL hh hhsmall hA) z
  have hnA : ‖(G).a‖ = A := suffixVector_norm A hA.le (pathEdges h)
  have hne : ‖(G).e‖ = 1 := entryVector_norm (pathEdges h)
  rw [hnA, hne, mul_one] at hb
  have hk := (le_div_iff₀ (sq_pos_of_pos hA)).mp
    (actual_kappa_upper L h A hL hh hhsmall hA)
  have hc := actual_coupling_bound L h A hL hh hhsmall hA
  exact hb.trans (by nlinarith only [hk, hc])

end MatchingBounds1005.PathGreen

