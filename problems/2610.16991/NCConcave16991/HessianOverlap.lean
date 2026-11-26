import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual bounded-overlap Hessian summation (Appendix E.14)

Supports are explicit finite sets of Hilbert blocks. Their coordinate
projections are constructed and their exact squared norms are proved. The
weighted incidence count is an actual finite-sum identity. Local C² terms
are precomposed with these projections, so their support is enforced by
their formula rather than supplied as a Hessian-support certificate.
-/

namespace NCConcave16991.HessianOverlap

open scoped BigOperators InnerProductSpace ContDiff

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

section Bilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def bilinearRiesz (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

theorem bilinearRiesz_inner (B : E →L[ℝ] E →L[ℝ] ℝ) (x y : E) :
    ⟪bilinearRiesz B x, y⟫_ℝ = B x y := by
  change ⟪(InnerProductSpace.toDual ℝ E).symm (B x), y⟫_ℝ = _
  exact InnerProductSpace.toDual_symm_apply

/-- Polarization recovers the full bilinear operator norm with no loss. -/
theorem symmetric_bilinear_norm_le (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) {K : ℝ} (hK : 0 ≤ K)
    (hdiag : ∀ x, |B x x| ≤ K * ‖x‖ ^ 2) : ‖B‖ ≤ K := by
  have hA : ‖bilinearRiesz B‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le hK
    intro x y hx hy
    rw [bilinearRiesz_inner]
    simp only [RCLike.re_to_real]
    have hp := (abs_le.mp (hdiag (x + y))).2
    have hm := (abs_le.mp (hdiag (x - y))).1
    have hpol : B (x + y) (x + y) - B (x - y) (x - y) = 4 * B x y := by
      simp only [map_add, map_sub, add_apply, sub_apply, hB y x]
      ring
    have hpar : K * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) = 4 * K := by
      rw [parallelogram_law_with_norm ℝ, hx, hy]
      ring
    nlinarith
  apply B.opNorm_le_bound₂ hK
  intro x y
  rw [Real.norm_eq_abs, ← bilinearRiesz_inner]
  have hc := abs_real_inner_le_norm (bilinearRiesz B x) y
  have hh := (bilinearRiesz B).le_opNorm x
  have hx := mul_le_mul_of_nonneg_right hA (norm_nonneg x)
  exact hc.trans (mul_le_mul_of_nonneg_right (hh.trans hx) (norm_nonneg y))

end Bilinear

section Blocks

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]
    {V : ι → Type*} [∀ j, NormedAddCommGroup (V j)]
    [∀ j, InnerProductSpace ℝ (V j)]

abbrev Blocks (V : ι → Type*) := PiLp 2 V

noncomputable def blockProjectionLinear (I : Finset ι) : Blocks V →ₗ[ℝ] Blocks V where
  toFun x := WithLp.toLp 2 (fun j => if j ∈ I then x j else 0)
  map_add' := by
    intro x y
    ext j
    by_cases hj : j ∈ I <;> simp [hj, PiLp.add_apply]
  map_smul' := by
    intro c x
    ext j
    by_cases hj : j ∈ I <;> simp [hj, PiLp.smul_apply]

omit [Fintype ι] in
theorem blockProjectionLinear_apply (I : Finset ι) (x : Blocks V) (j : ι) :
    blockProjectionLinear I x j = if j ∈ I then x j else 0 := rfl

theorem blockProjectionLinear_norm_sq (I : Finset ι) (x : Blocks V) :
    ‖blockProjectionLinear I x‖ ^ 2 = ∑ j, if j ∈ I then ‖x j‖ ^ 2 else 0 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ I <;> simp [blockProjectionLinear_apply, hj]

theorem blockProjectionLinear_norm_le (I : Finset ι) (x : Blocks V) :
    ‖blockProjectionLinear I x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [blockProjectionLinear_norm_sq, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ∈ I <;> simp [hj]

noncomputable def blockProjection (I : Finset ι) : Blocks V →L[ℝ] Blocks V :=
  (blockProjectionLinear I).mkContinuous 1 (fun x => by
    simpa only [one_mul] using blockProjectionLinear_norm_le I x)

theorem blockProjection_apply (I : Finset ι) (x : Blocks V) (j : ι) :
    blockProjection I x j = if j ∈ I then x j else 0 := rfl

theorem blockProjection_norm_sq (I : Finset ι) (x : Blocks V) :
    ‖blockProjection I x‖ ^ 2 = ∑ j, if j ∈ I then ‖x j‖ ^ 2 else 0 :=
  blockProjectionLinear_norm_sq I x

theorem blockProjection_idempotent (I : Finset ι) (x : Blocks V) :
    blockProjection I (blockProjection I x) = blockProjection I x := by
  ext j
  by_cases hj : j ∈ I <;> simp [blockProjection_apply, hj]

noncomputable def incidentLoad (I : ρ → Finset ι) (C : ρ → ℝ) (j : ι) : ℝ :=
  ∑ r, if j ∈ I r then C r else 0

omit [Fintype ι] in
theorem incidentLoad_uniform (I : ρ → Finset ι) (C : ℝ) (j : ι) :
    incidentLoad I (fun _ => C) j = ((Finset.univ.filter (fun r => j ∈ I r)).card : ℝ) * C := by
  have he : incidentLoad I (fun _ => C) j =
      ∑ r ∈ Finset.univ.filter (fun r => j ∈ I r), C := by
    simp only [Finset.sum_filter, incidentLoad]
  rw [he]
  simp

/-- Exact weighted overlap accounting, before taking a maximum load. -/
theorem weighted_projection_energy (I : ρ → Finset ι) (C : ρ → ℝ) (x : Blocks V) :
    (∑ r, C r * ‖blockProjection (I r) x‖ ^ 2) =
      ∑ j, incidentLoad I C j * ‖x j‖ ^ 2 := by
  simp only [blockProjection_norm_sq, Finset.mul_sum, incidentLoad, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  by_cases hj : j ∈ I r <;> simp [hj]

theorem weighted_projection_bound (I : ρ → Finset ι) (C : ρ → ℝ) (K : ℝ)
    (hload : ∀ j, incidentLoad I C j ≤ K) (x : Blocks V) :
    (∑ r, C r * ‖blockProjection (I r) x‖ ^ 2) ≤ K * ‖x‖ ^ 2 := by
  rw [weighted_projection_energy, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hload j) (sq_nonneg _))

variable [∀ j, CompleteSpace (V j)]

/-- The sharp load bound for pulled-back, genuinely symmetric local forms. -/
theorem pulledBack_sum_norm_le (I : ρ → Finset ι)
    (B : ρ → Blocks V →L[ℝ] Blocks V →L[ℝ] ℝ)
    (C : ρ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hsym : ∀ r x y, B r x y = B r y x)
    (hB : ∀ r, ‖B r‖ ≤ C r)
    (hload : ∀ j, incidentLoad I C j ≤ K) :
    ‖∑ r, (B r).bilinearComp (blockProjection (I r)) (blockProjection (I r))‖ ≤ K := by
  refine symmetric_bilinear_norm_le _ ?_ hK ?_
  · intro x y
    simp only [sum_apply, ContinuousLinearMap.bilinearComp_apply]
    apply Finset.sum_congr rfl
    intro r _
    exact hsym r _ _
  · intro x
    simp only [sum_apply, ContinuousLinearMap.bilinearComp_apply]
    have htri := norm_sum_le Finset.univ
      (fun r => B r (blockProjection (I r) x) (blockProjection (I r) x))
    simp only [Real.norm_eq_abs] at htri
    have hlocal (r : ρ) : |B r (blockProjection (I r) x) (blockProjection (I r) x)| ≤
        C r * ‖blockProjection (I r) x‖ ^ 2 := by
      have hh := (B r).le_opNorm₂ (blockProjection (I r) x) (blockProjection (I r) x)
      have hb := mul_le_mul_of_nonneg_right (hB r) (sq_nonneg ‖blockProjection (I r) x‖)
      rw [Real.norm_eq_abs] at hh
      nlinarith
    exact htri.trans ((Finset.sum_le_sum (fun r _ => hlocal r)).trans
      (weighted_projection_bound I C K hload x))

end Blocks

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual second Fréchet derivative of a function of an explicit linear
projection. This is the support mechanism used in the overlap theorem. -/
theorem hessian_comp_linear (g : E → ℝ) (hg : ContDiff ℝ 2 g) (P : E →L[ℝ] E) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z => g (P z))) x =
      (fderiv ℝ (fderiv ℝ g) (P x)).bilinearComp P P := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have he : fderiv ℝ (fun z => g (P z)) = fun z => (fderiv ℝ g (P z)).comp P := by
    funext z
    exact ((hd (P z)).hasFDerivAt.comp z P.hasFDerivAt).fderiv
  rw [he]
  have hh := (((ContinuousLinearMap.compL ℝ E E ℝ).flip P).hasFDerivAt).comp x
    (((hD (P x)).hasFDerivAt).comp x P.hasFDerivAt)
  change HasFDerivAt (fun z => (fderiv ℝ g (P z)).comp P) _ x at hh
  rw [hh.fderiv]
  ext h k
  rfl

theorem hessian_sum {ρ : Type*} [Fintype ρ] (g : ρ → E → ℝ)
    (hg : ∀ r, ContDiff ℝ 2 (g r)) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z => ∑ r, g r z)) x = ∑ r, fderiv ℝ (fderiv ℝ (g r)) x := by
  have he : fderiv ℝ (fun z => ∑ r, g r z) = fun z => ∑ r, fderiv ℝ (g r) z := by
    funext z
    exact fderiv_fun_sum (fun r _ => ((hg r).differentiable (by norm_num) z))
  rw [he]
  exact fderiv_fun_sum (fun r _ =>
    (((hg r).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x))

end Calculus

section ActualOverlap

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]
    {V : ι → Type*} [∀ j, NormedAddCommGroup (V j)]
    [∀ j, InnerProductSpace ℝ (V j)] [∀ j, CompleteSpace (V j)]

/-- E.14 with actual C² functions and explicit finite supports. The right
side is any upper bound on the incident sum of local Hessian constants. -/
theorem actual_hessian_overlap_bound (I : ρ → Finset ι)
    (g : ρ → Blocks V → ℝ) (hg : ∀ r, ContDiff ℝ 2 (g r))
    (C : ρ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hlocal : ∀ r z, ‖fderiv ℝ (fderiv ℝ (g r)) z‖ ≤ C r)
    (hload : ∀ j, incidentLoad I C j ≤ K) (x : Blocks V) :
    ‖fderiv ℝ (fderiv ℝ (fun z => ∑ r, g r (blockProjection (I r) z))) x‖ ≤ K := by
  have hproj (r : ρ) : ContDiff ℝ 2 (blockProjection (I r) : Blocks V → Blocks V) :=
    ContinuousLinearMap.contDiff (blockProjection (V := V) (I r))
  have hterms (r : ρ) : ContDiff ℝ 2 (fun z => g r (blockProjection (I r) z)) :=
    (hg r).comp (hproj r)
  rw [hessian_sum (fun r z => g r (blockProjection (I r) z)) hterms]
  simp only [hessian_comp_linear _ (hg _) _ _]
  apply pulledBack_sum_norm_le I _ C hK
  · intro r u v
    exact ((hg r).contDiffAt.isSymmSndFDerivAt (by norm_num)) u v
  · intro r
    exact hlocal r _
  · exact hload

/-- The usual `d₀ C` version, with the degree bound stated as an actual
cardinality of the finite family of incident supports. -/
theorem actual_hessian_overlap_degree_bound (I : ρ → Finset ι)
    (g : ρ → Blocks V → ℝ) (hg : ∀ r, ContDiff ℝ 2 (g r))
    (C : ℝ) (hC : 0 ≤ C) (d₀ : ℕ)
    (hlocal : ∀ r z, ‖fderiv ℝ (fderiv ℝ (g r)) z‖ ≤ C)
    (hdegree : ∀ j, (Finset.univ.filter (fun r => j ∈ I r)).card ≤ d₀) (x : Blocks V) :
    ‖fderiv ℝ (fderiv ℝ (fun z => ∑ r, g r (blockProjection (I r) z))) x‖ ≤ (d₀ : ℝ) * C := by
  apply actual_hessian_overlap_bound I g hg (fun _ => C) (by positivity) hlocal
  intro j
  rw [incidentLoad_uniform]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree j) hC

end ActualOverlap
end NCConcave16991.HessianOverlap
