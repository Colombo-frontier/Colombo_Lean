import MatchingBounds1005.DecoyObjective
import MatchingBounds1005.ChainSmoothness
import MatchingBounds1005.GradientLipschitz

/-! Copy-count-independent smoothness of the actual spectral decoy objective. -/
noncomputable section
open scoped InnerProductSpace BigOperators ContDiff

namespace MatchingBounds1005.BlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

def decoyLinear (n K : ℕ) : CopySpace (E := E) n K →L[ℝ] ℝ :=
  -G.lam • (G.firstEntry n).comp (copyProjection n K 0)

def decoyQuadratic (n K : ℕ) : CopySpace (E := E) n K → ℝ :=
  SymmetricQuadratic.energy (G.copyOperator n K) (G.decoyLinear n K)

def decoyPotential (r : ℝ) (n K : ℕ) : CopySpace (E := E) n K → ℝ :=
  G.euclideanPotential r n ∘ copyProjection n K 0

def decoyReadout (n K : ℕ) (a : E) (A : ℝ) (i : Fin (n + 1)) : CopySpace (E := E) n K :=
  activeInsert n K (normalizedBlockReadout n a A i)

theorem decoyReadout_inner (n K : ℕ) (a : E) (A : ℝ) (i : Fin (n + 1))
    (z : CopySpace (E := E) n K) :
    ⟪decoyReadout n K a A i, z⟫_ℝ = A⁻¹ * ⟪a, z 0 i⟫_ℝ := by
  rw [decoyReadout, activeInsert_inner, normalizedBlockReadout_inner]

theorem decoyReadout_orthonormal (n K : ℕ) {a : E} {A : ℝ} (hA : 0 < A) (ha : ‖a‖ = A) :
    Orthonormal ℝ (decoyReadout n K a A) :=
  (normalizedBlockReadout_orthonormal n hA ha).comp_linearIsometry (activeInsert n K)

theorem decoyPotential_eq_ridge {A : ℝ} (hA : 0 < A) (r : ℝ) (n K : ℕ) :
    G.decoyPotential r n K = fun z =>
      G.tau * ridgeSum (decoyReadout n K G.a A) (Primitive.potential r) A z := by
  funext z
  change G.tau * (∑ i, Primitive.potential r ⟪G.a, z 0 i⟫_ℝ) = _
  unfold ridgeSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [decoyReadout_inner]
  congr 1
  field_simp

theorem copyOperator_pair_symmetric (n K : ℕ) (x y : CopySpace (E := E) n K) :
    ⟪x, G.copyOperator n K y⟫_ℝ = ⟪G.copyOperator n K x, y⟫_ℝ :=
  ((G.copyOperator_symmetric n K) x y).symm

theorem decoyObjective_decomposition (r : ℝ) (n K : ℕ) :
    G.decoyObjective r n K = G.decoyQuadratic n K + G.decoyPotential r n K := by
  funext z
  have hq : G.decoyQuadratic n K z =
      (1 / 2 : ℝ) * (∑ j, G.chainBilinear n (z j) (z j)) - G.lam * G.firstEntry n (z 0) := by
    simp only [decoyQuadratic, SymmetricQuadratic.energy, decoyLinear,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, copyProjection,
      PiLp.proj_apply, smul_eq_mul]
    rw [real_inner_comm (G.copyOperator n K z) z, G.copyOperator_inner]
    ring
  change G.euclideanObjective r n (z 0) +
      (∑ j : Fin K, SymmetricQuadratic.energy (G.chainOperator n) 0 (z j.succ)) =
        G.decoyQuadratic n K z + G.euclideanPotential r n (z 0)
  simp only [G.inactive_energy]
  rw [Fin.sum_univ_succ (fun j : Fin (K + 1) => G.chainBilinear n (z j) (z j))] at hq
  rw [G.euclideanObjective_decomposition, hq, ← Finset.mul_sum]
  simp only [euclideanQuadratic, euclideanPotential]
  ring

theorem decoyObjective_smooth (r : ℝ) (n K : ℕ) : ContDiff ℝ ∞ (G.decoyObjective r n K) := by
  rw [G.decoyObjective_decomposition]
  exact (SymmetricQuadratic.smooth _ _).add
    ((G.euclideanPotential_smooth r n).comp (copyProjection (E := E) n K 0).contDiff)

theorem chainOperator_norm_bound (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hH : ‖LinearMap.toContinuousLinearMap G.H‖ ≤ C) :
    ‖G.chainOperator n‖ ≤ C + G.kappa * ‖G.a‖ ^ 2 + 2 * G.lam * ‖G.a‖ * ‖G.e‖ := by
  have hk := G.kappa_nonneg
  have hl := G.lam_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [← innerSL_apply_norm ℝ]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [innerSL_apply, Real.norm_eq_abs, G.chainOperator_inner]
  exact G.chainBilinear_bound n C hC hH z v

theorem decoyPotential_jet_bound {A : ℝ} (hA : 0 < A) (ha : ‖G.a‖ = A)
    (r : ℝ) (n K k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |iteratedDeriv (k + 2) (Primitive.potential r) u| ≤ C)
    (z : CopySpace (E := E) n K) :
    ‖iteratedFDeriv ℝ (k + 2) (G.decoyPotential r n K) z‖ ≤ G.tau * C * A ^ (k + 2) := by
  have hlevel : ((k + 2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    generalize k + 2 = j
    exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  rw [decoyPotential, (copyProjection (E := E) n K 0).iteratedFDeriv_comp_right
    (G.euclideanPotential_smooth r n) z hlevel]
  calc
    _ ≤ ‖iteratedFDeriv ℝ (k + 2) (G.euclideanPotential r n) (z 0)‖ *
        ‖copyProjection (E := E) n K 0‖ ^ (k + 2) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ (k + 2) (G.euclideanPotential r n) (z 0)).norm_compContinuousLinearMap_le
          (fun _ => copyProjection (E := E) n K 0)
    _ ≤ ‖iteratedFDeriv ℝ (k + 2) (G.euclideanPotential r n) (z 0)‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg _) (copyProjection_norm_le n K 0)) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_one]
      simpa only [abs_of_nonneg G.tau_nonneg] using
        G.euclideanPotential_derivative_bound hA ha r n k hC hb (z 0)

theorem decoyObjective_jet_bound {A : ℝ} (hA : 0 < A) (ha : ‖G.a‖ = A)
    (r : ℝ) (n K k : ℕ) {C Q : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hb : ∀ u, |iteratedDeriv (k + 2) (Primitive.potential r) u| ≤ C)
    (hquad : ‖G.chainOperator n‖ ≤ Q) (z : CopySpace (E := E) n K) :
    ‖iteratedFDeriv ℝ (k + 2) (G.decoyObjective r n K) z‖ ≤ Q + G.tau * C * A ^ (k + 2) := by
  have hlevel : ((k + 2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    generalize k + 2 = j
    exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have hqs : ContDiff ℝ ∞ (G.decoyQuadratic n K) := SymmetricQuadratic.smooth _ _
  have hps : ContDiff ℝ ∞ (G.decoyPotential r n K) :=
    (G.euclideanPotential_smooth r n).comp (copyProjection (E := E) n K 0).contDiff
  have hqbound : ‖iteratedFDeriv ℝ (k + 2) (G.decoyQuadratic n K) z‖ ≤ Q := by
    rcases k with _ | k
    · exact (SymmetricQuadratic.second_bound _ _ (G.copyOperator_pair_symmetric n K) z).trans
        ((G.copyOperator_norm_le n K).trans hquad)
    · have hz := congrFun (SymmetricQuadratic.higher_zero (G.copyOperator n K)
        (G.decoyLinear n K) (G.copyOperator_pair_symmetric n K) k) z
      change ‖iteratedFDeriv ℝ (k + 3) (G.decoyQuadratic n K) z‖ ≤ Q
      rw [show iteratedFDeriv ℝ (k + 3) (G.decoyQuadratic n K) z = 0 from hz, norm_zero]
      exact hQ
  rw [G.decoyObjective_decomposition, iteratedFDeriv_add_apply
    (hqs.of_le hlevel).contDiffAt (hps.of_le hlevel).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add hqbound (G.decoyPotential_jet_bound hA ha r n K k hC hb z))

theorem decoyObjective_core_jet_bound {A : ℝ} (hA : 0 < A) (ha : ‖G.a‖ = A)
    (n K k : ℕ) {C Q : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hb : ∀ u, |iteratedDeriv (k + 2) (Primitive.potential A) u| ≤ C * A ^ 3 / A ^ (k + 1))
    (hquad : ‖G.chainOperator n‖ ≤ Q) (z : CopySpace (E := E) n K) :
    ‖iteratedFDeriv ℝ (k + 2) (G.decoyObjective A n K) z‖ ≤ Q + C * (G.tau * A ^ 4) := by
  have h := G.decoyObjective_jet_bound hA ha A n K k (by positivity) hQ hb hquad z
  convert h using 1
  congr 1
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  field_simp
  ring

theorem decoyGradient_zero (r : ℝ) (n K : ℕ) :
    G.decoyGradient r n K 0 = activeInsert n K (G.euclideanGradient r n 0) := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [decoyGradient, activeInsert, copyInsert_apply]
  · simp [decoyGradient, activeInsert, copyInsert_apply]

theorem decoyObjective_first_jet_zero (r : ℝ) (n K : ℕ) :
    ‖iteratedFDeriv ℝ 1 (G.decoyObjective r n K) 0‖ = G.lam * ‖G.e‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero,
    (G.decoyObjective_hasFDerivAt r n K 0).fderiv, innerSL_apply_norm,
    G.decoyGradient_zero, LinearIsometry.norm_map, G.euclideanGradient_zero,
    PiLp.norm_equiv_symm_single, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg G.lam_nonneg]

theorem decoyObjective_radial_budget (r : ℝ) (n K j : ℕ) (hj : 2 ≤ j)
    {R b : ℝ} (hR : 0 < R) (hb : 0 ≤ b)
    (hjet : ∀ q, 2 ≤ q → q ≤ j → ∀ z : CopySpace (E := E) n K,
      ‖iteratedFDeriv ℝ q (G.decoyObjective r n K) z‖ ≤ b)
    (x : CopySpace (E := E) n K) :
    ‖iteratedFDeriv ℝ j (G.decoyObjective r n K ∘ radial R) x‖ ≤
      2 * RadialHigher.compositionConstant j *
        (G.lam * ‖G.e‖ * R + ∑ q ∈ Finset.Icc 2 j, b * R ^ q) / R ^ j := by
  have hlevel : (j : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have h := RadialHigher.radial_composition_budget hj
    ((G.decoyObjective_smooth r n K).of_le hlevel) hR (fun _ => b)
    (fun _ _ _ => hb) hjet x
  rwa [G.decoyObjective_first_jet_zero] at h

end MatchingBounds1005.BlockGeometry

namespace MatchingBounds1005.PathGreen
variable (L h A : ℝ) (hL : 0 < L) (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (hA : 0 < A)
local notation "G" => actualBlockGeometry L h A hL hh hhsmall hA

theorem actual_chainOperator_norm (n : ℕ) :
    ‖(G).chainOperator n‖ ≤ 4 * L + 2593 * (L * h ^ 2) +
      18 * Real.sqrt 2 * L * h * Real.sqrt h := by
  have hb := (G).chainOperator_norm_bound n (L * (h ^ 2 + 4)) (by positivity)
    (actual_H_norm L h A hL hh hhsmall hA)
  have hnA : ‖(G).a‖ = A := suffixVector_norm A hA.le (pathEdges h)
  have hne : ‖(G).e‖ = 1 := entryVector_norm (pathEdges h)
  rw [hnA, hne, mul_one] at hb
  have hk := (le_div_iff₀ (sq_pos_of_pos hA)).mp (actual_kappa_upper L h A hL hh hhsmall hA)
  have hc := actual_coupling_bound L h A hL hh hhsmall hA
  exact hb.trans (by nlinarith only [hk, hc])

theorem actual_lam_le_L (hAone : 1 ≤ A) (hsmaller : h ≤ 1 / 37) : (G).lam ≤ L := by
  have hc := actual_coupling_bound L h A hL hh hhsmall hA
  have hs2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsh : Real.sqrt h ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hrhs : 18 * Real.sqrt 2 * L * h * Real.sqrt h ≤ 2 * L := by
    calc
      _ ≤ 18 * 2 * L * h * 1 := by gcongr
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hsmaller hL.le, hL]
  have hla := mul_le_mul_of_nonneg_left hAone (G).lam_nonneg
  nlinarith only [hc, hrhs, hla]

end MatchingBounds1005.PathGreen

namespace MatchingBounds1005.EpsilonCalibration
open PathGreen
variable (a L t : ℝ) (ha : 0 < a) (hL : 0 < L) (ht : 0 < t)
  (hhsmall : pathScale a L t ≤ 1 / 4)
local notation "G" => geometry a L t ha hL ht hhsmall

theorem calibrated_decoy_jet_bound (p : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hprim : ∀ q, 1 ≤ q → q ≤ p → ∀ r, 1 ≤ r → ∀ u,
      |iteratedDeriv (q + 1) (Primitive.potential r) u| ≤ C * r ^ 3 / r ^ q)
    (hbudget : 18 * 8192 * C * a ^ 3 ≤ 4 * L)
    (hr : t ≤ a) (hpath : pathScale a L t ≤ 1 / 37)
    (q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p) (n K : ℕ)
    (z : BlockGeometry.CopySpace (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) n K) :
    ‖iteratedFDeriv ℝ (q + 1) ((G).decoyObjective (amplitude a t) n K) z‖ ≤ 16 * L := by
  have hA := amplitude_pos a t ha ht
  have hnorm : ‖(G).a‖ = amplitude a t := suffixVector_norm (amplitude a t) hA.le _
  have hQ : ‖(G).chainOperator n‖ ≤ 8 * L :=
    (actual_chainOperator_norm L (pathScale a L t) (amplitude a t) hL
      (pathScale_pos a L t ha hL ht) hhsmall hA n).trans
      (quadratic_coefficient_small L (pathScale a L t) hL
        (pathScale_pos a L t ha hL ht) hpath)
  have hqeq : q - 1 + 2 = q + 1 := by omega
  have hcore := (G).decoyObjective_core_jet_bound hA hnorm n K (q - 1) hC (by positivity)
    (by simpa only [hqeq, Nat.sub_add_cancel hq] using
      hprim q hq hqp (amplitude a t) (amplitude_ge_one a t ht hr)) hQ z
  rw [hqeq] at hcore
  have hnonlinear := mul_le_mul_of_nonneg_left
    (calibrated_nonlinear_budget a L t ha hL ht hhsmall) hC
  nlinarith only [hcore, hnonlinear, hbudget, hL]

theorem calibrated_decoy_gradient (hr : t ≤ a) (n K : ℕ)
    (z : BlockGeometry.CopySpace (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) n K)
    (htail : ⟪(G).a, z 0 (Fin.last n)⟫_ℝ = 0) :
    32 * t ^ 3 ≤ ‖gradient ((G).decoyObjective (amplitude a t) n K) z‖ :=
  (calibrated_gradient a L t ha hL ht hhsmall hr n (z 0) htail).trans
    ((G).active_gradient_le_decoy (amplitude a t) n K z)

theorem calibrated_decoy_normalized_gradient (hr : t ≤ a) (n K : ℕ)
    (z : BlockGeometry.CopySpace (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) n K)
    (htail : ⟪BlockGeometry.decoyReadout n K (G).a (amplitude a t) (Fin.last n), z⟫_ℝ = 0) :
    32 * t ^ 3 ≤ ‖gradient ((G).decoyObjective (amplitude a t) n K) z‖ := by
  rw [BlockGeometry.decoyReadout_inner] at htail
  have hzero := (mul_eq_zero.mp htail).resolve_left (inv_ne_zero (amplitude_pos a t ha ht).ne')
  exact calibrated_decoy_gradient a L t ha hL ht hhsmall hr n K z hzero

theorem calibrated_decoy_gap (hr : t ≤ a) (hphase : 1 ≤ phaseCount a t)
    (hsmall : 10368 * 8192 * t ^ 4 ≤ a) (K : ℕ)
    (z : BlockGeometry.CopySpace
      (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) (phaseCount a t - 1) K) :
    (G).decoyObjective (amplitude a t) (phaseCount a t - 1) K 0 -
      (G).decoyObjective (amplitude a t) (phaseCount a t - 1) K z ≤ 1 / 4 := by
  have h := (G).decoyObjective_gap (amplitude a t) (amplitude_ge_one a t ht hr)
    (phaseCount a t - 1) K z
  conv at h => rhs; rw [Nat.sub_add_cancel hphase]
  exact h.trans (calibrated_gap a L t ha hL ht hhsmall hsmall)

theorem calibrated_decoy_radial (hr : t ≤ a) (hphase : 1 ≤ phaseCount a t)
    (hsmall : 10368 * 8192 * t ^ 4 ≤ a) (K : ℕ)
    (z : BlockGeometry.CopySpace
      (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) (phaseCount a t - 1) K) :
    -(81 / 256 : ℝ) ≤
      ⟪z, gradient ((G).decoyObjective (amplitude a t) (phaseCount a t - 1) K) z⟫_ℝ := by
  have h := (G).decoyObjective_radial_gap (amplitude a t) (amplitude_ge_one a t ht hr)
    (phaseCount a t - 1) K z
  conv at h => lhs; rw [Nat.sub_add_cancel hphase]
  have hb := calibrated_gap a L t ha hL ht hhsmall hsmall
  nlinarith only [h, hb]

theorem calibrated_decoy_firstjet (hr : t ≤ a) (hpath : pathScale a L t ≤ 1 / 37) (n K : ℕ) :
    ‖iteratedFDeriv ℝ 1 ((G).decoyObjective (amplitude a t) n K) 0‖ ≤ 16 * L := by
  rw [(G).decoyObjective_first_jet_zero]
  have hne : ‖(G).e‖ = 1 := entryVector_norm _
  rw [hne, mul_one]
  exact (actual_lam_le_L L (pathScale a L t) (amplitude a t) hL
    (pathScale_pos a L t ha hL ht) hhsmall (amplitude_pos a t ha ht)
    (amplitude_ge_one a t ht hr) hpath).trans (by linarith)

theorem calibrated_decoy_lipschitz (p : ℕ) (hp : 1 ≤ p) (C : ℝ) (hC : 0 ≤ C)
    (hprim : ∀ q, 1 ≤ q → q ≤ p → ∀ r, 1 ≤ r → ∀ u,
      |iteratedDeriv (q + 1) (Primitive.potential r) u| ≤ C * r ^ 3 / r ^ q)
    (hbudget : 18 * 8192 * C * a ^ 3 ≤ 4 * L)
    (hr : t ≤ a) (hpath : pathScale a L t ≤ 1 / 37) (n K : ℕ)
    (x y : BlockGeometry.CopySpace (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) n K) :
    ‖gradient ((G).decoyObjective (amplitude a t) n K) x -
      gradient ((G).decoyObjective (amplitude a t) n K) y‖ ≤ 16 * L * ‖x - y‖ :=
  gradient_lipschitz_of_hessian_bound ((G).decoyObjective_smooth (amplitude a t) n K)
    (calibrated_decoy_jet_bound a L t ha hL ht hhsmall p C hC hprim hbudget hr hpath 1 le_rfl hp n K) y x

end MatchingBounds1005.EpsilonCalibration
