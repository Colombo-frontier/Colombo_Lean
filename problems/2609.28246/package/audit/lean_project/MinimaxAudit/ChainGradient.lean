import MinimaxAudit.GateHessian
import MinimaxAudit.Geometry

/-!
# Actual block-chain gradient and its global contraction

Blocks are the orthogonal coordinates (a_i,b_{i+1}) and the terminal block
(a_n,b_1), hence differ from the paper's displayed chain ordering by a coordinate
permutation. The terminal component includes the seed. All nonlinear functions
below are the concrete integral gates, not hypothetical Lipschitz maps.
The coordinate permutation and signed reversal of the full primal-dual frame
remain separate assembly obligations.
-/

namespace MinimaxAudit

/-- Gradient of the actual terminal double primitive, with a dummy zero slot. -/
noncomputable def terminalGateGradient (profile : GateProfile) (tau : ℝ)
    (v : GatePlane) : GatePlane :=
  WithLp.toLp 2 ![gate profile tau (v 0), 0]

/-- The actual terminal gradient is globally one-Lipschitz. -/
theorem terminalGateGradient_norm_sub_le (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (v w : GatePlane) :
    ‖terminalGateGradient profile tau w - terminalGateGradient profile tau v‖ ≤ ‖w - v‖ := by
  have hg := gate_norm_sub_le profile htau (v 0) (w 0)
  have hs := pow_le_pow_left₀ (abs_nonneg _) hg 2
  simp only [sq_abs] at hs
  have hsquares : ‖terminalGateGradient profile tau w - terminalGateGradient profile tau v‖ ^ 2 ≤
      ‖w - v‖ ^ 2 := by
    rw [gatePlane_norm_sq, gatePlane_norm_sq]
    simpa [terminalGateGradient] using
      (hs.trans (le_add_of_nonneg_right (sq_nonneg (w 1 - v 1))))
  have hn1 := norm_nonneg (terminalGateGradient profile tau w - terminalGateGradient profile tau v)
  have hn2 := norm_nonneg (w - v)
  nlinarith

section FiniteChain

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The block extraction is a continuous linear map. -/
noncomputable def gateBlockProjection (j : J) :
    EuclideanSpace ℝ (J × Fin 2) →L[ℝ] GatePlane :=
  (show EuclideanSpace ℝ (J × Fin 2) →ₗ[ℝ] GatePlane from
    { toFun := fun v => gateBlockVector v j
      map_add' := by
        intro v w
        ext i
        simp [gateBlockVector]
      map_smul' := by
        intro c v
        ext i
        simp [gateBlockVector] }).toContinuousLinearMap

/-- The concrete scalar potential of one gate module, terminal included. -/
noncomputable def chainModulePotential (profile : GateProfile) (tau : ℝ)
    (terminal j : J) (v : GatePlane) : ℝ :=
  if j = terminal then doubleGate profile tau (v 0)
  else scalarGate profile tau (v 0) (v 1)

/-- Concrete unscaled gradient of a gate module, with one terminal module. -/
noncomputable def chainModuleGradient (profile : GateProfile) (tau : ℝ)
    (terminal j : J) (v : GatePlane) : GatePlane :=
  if j = terminal then terminalGateGradient profile tau v
  else scalarGateGradient profile tau v

/- Each concrete module gradient is the full Euclidean gradient of its
scalar integral potential. -/
omit [Fintype J] in
theorem chainModulePotential_hasFDerivAt (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (terminal j : J) (v : GatePlane) :
    HasFDerivAt (chainModulePotential profile tau terminal j)
      (innerSL ℝ (chainModuleGradient profile tau terminal j v)) v := by
  by_cases hj : j = terminal
  · have hd := (doubleGate_hasDerivAt profile htau (v 0)).comp_hasFDerivAt v
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt)
    convert! hd using 1
    · ext w
      simp [chainModulePotential, hj]
    · ext w
      simp [chainModuleGradient, hj, terminalGateGradient, innerSL_apply_apply,
        PiLp.inner_apply, Fin.sum_univ_two]
      ring
  · have hfun : chainModulePotential profile tau terminal j =
        fun w : GatePlane => scalarGate profile tau (w 0) (w 1) := by
      funext w
      simp [chainModulePotential, hj]
    rw [hfun]
    simpa [chainModuleGradient, hj] using
      scalarGate_hasFDerivAt_gradient profile htau v

/- Every actual module is nonexpansive, including the terminal one. -/
omit [Fintype J] in
theorem chainModuleGradient_norm_sub_le (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (terminal j : J) (v w : GatePlane) :
    ‖chainModuleGradient profile tau terminal j w -
      chainModuleGradient profile tau terminal j v‖ ≤ ‖w - v‖ := by
  by_cases hj : j = terminal
  · simpa [chainModuleGradient, hj] using terminalGateGradient_norm_sub_le profile htau v w
  · simpa [chainModuleGradient, hj] using scalarGateGradient_norm_sub_le profile htau v w

/-- Orthogonal direct sum of the actual gate and terminal gradients. -/
noncomputable def chainUnscaledGradient (profile : GateProfile) (tau : ℝ)
    (terminal : J) (v : EuclideanSpace ℝ (J × Fin 2)) : EuclideanSpace ℝ (J × Fin 2) :=
  WithLp.toLp 2 (fun ji =>
    chainModuleGradient profile tau terminal ji.1 (gateBlockVector v ji.1) ji.2)

/-- A finite direct sum preserves the Lipschitz constant, for every chain size. -/
theorem chainUnscaledGradient_norm_sub_le (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (terminal : J) (v w : EuclideanSpace ℝ (J × Fin 2)) :
    ‖chainUnscaledGradient profile tau terminal w -
      chainUnscaledGradient profile tau terminal v‖ ≤ ‖w - v‖ := by
  have hsquares :
      (∑ j : J, ‖chainModuleGradient profile tau terminal j (gateBlockVector w j) -
        chainModuleGradient profile tau terminal j (gateBlockVector v j)‖ ^ 2) ≤
      ∑ j : J, ‖gateBlockVector w j - gateBlockVector v j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    have h := chainModuleGradient_norm_sub_le profile htau terminal j
      (gateBlockVector v j) (gateBlockVector w j)
    have hn1 := norm_nonneg (chainModuleGradient profile tau terminal j (gateBlockVector w j) -
      chainModuleGradient profile tau terminal j (gateBlockVector v j))
    have hn2 := norm_nonneg (gateBlockVector w j - gateBlockVector v j)
    nlinarith
  have hleft : ‖chainUnscaledGradient profile tau terminal w -
      chainUnscaledGradient profile tau terminal v‖ ^ 2 =
      ∑ j : J, ‖chainModuleGradient profile tau terminal j (gateBlockVector w j) -
        chainModuleGradient profile tau terminal j (gateBlockVector v j)‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, chainUnscaledGradient, Fintype.sum_prod_type]
  have hright : ‖w - v‖ ^ 2 = ∑ j : J, ‖gateBlockVector w j - gateBlockVector v j‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, gateBlockVector, Fintype.sum_prod_type]
  have hn1 := norm_nonneg (chainUnscaledGradient profile tau terminal w -
    chainUnscaledGradient profile tau terminal v)
  have hn2 := norm_nonneg (w - v)
  nlinarith

/-- The actual gradient after scaling q and adding the fixed linear seed. -/
noncomputable def chainBlockGradient (profile : GateProfile) (tau q c : ℝ)
    (terminal : J) (v : EuclideanSpace ℝ (J × Fin 2)) : EuclideanSpace ℝ (J × Fin 2) :=
  q • chainUnscaledGradient profile tau terminal v +
    EuclideanSpace.single (terminal, 1) c

/-- The actual scalar block-chain potential, including terminal and seed.
This is ψ in the orthogonally permuted module ordering. -/
noncomputable def chainBlockPotential (profile : GateProfile) (tau q c : ℝ)
    (terminal : J) (v : EuclideanSpace ℝ (J × Fin 2)) : ℝ :=
  q * (∑ j : J, chainModulePotential profile tau terminal j (gateBlockVector v j)) +
    c * v (terminal, 1)

/-- Inner product decomposition into all orthogonal modules. -/
theorem chainUnscaledGradient_inner (profile : GateProfile) (tau : ℝ)
    (terminal : J) (v w : EuclideanSpace ℝ (J × Fin 2)) :
    inner ℝ (chainUnscaledGradient profile tau terminal v) w =
      ∑ j : J, inner ℝ
        (chainModuleGradient profile tau terminal j (gateBlockVector v j)) (gateBlockVector w j) := by
  simp [PiLp.inner_apply, chainUnscaledGradient, gateBlockVector, Fintype.sum_prod_type]

/-- The assembled concrete vector field is the full Euclidean gradient of the
assembled scalar potential, including its q scaling and linear seed. -/
theorem chainBlockPotential_hasFDerivAt (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (q c : ℝ) (terminal : J)
    (v : EuclideanSpace ℝ (J × Fin 2)) :
    HasFDerivAt (chainBlockPotential profile tau q c terminal)
      (innerSL ℝ (chainBlockGradient profile tau q c terminal v)) v := by
  have hmodule (j : J) :=
    (chainModulePotential_hasFDerivAt profile htau terminal j (gateBlockVector v j)).comp v
      ((gateBlockProjection j).hasFDerivAt)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hmodule j)
  have hseed := ((EuclideanSpace.proj (𝕜 := ℝ) (terminal, (1 : Fin 2))).hasFDerivAt
    (x := v)).const_mul c
  have hresult := (hsum.const_mul q).add hseed
  convert! hresult using 1
  ext w
  simp [chainBlockGradient, innerSL_apply_apply, EuclideanSpace.inner_single_left,
    chainUnscaledGradient_inner, ContinuousLinearMap.comp_apply, gateBlockProjection]

/-- The seed cancels in differences; the actual complete module gradient is
q-Lipschitz, with no dependence on chain length. -/
theorem chainBlockGradient_norm_sub_le (profile : GateProfile) {tau q c : ℝ}
    (htau : tau ≠ 0) (hq : 0 ≤ q) (terminal : J)
    (v w : EuclideanSpace ℝ (J × Fin 2)) :
    ‖chainBlockGradient profile tau q c terminal w -
      chainBlockGradient profile tau q c terminal v‖ ≤ q * ‖w - v‖ := by
  have h := chainUnscaledGradient_norm_sub_le profile htau terminal v w
  have heq : chainBlockGradient profile tau q c terminal w -
      chainBlockGradient profile tau q c terminal v =
      q • (chainUnscaledGradient profile tau terminal w -
        chainUnscaledGradient profile tau terminal v) := by
    simp [chainBlockGradient, ← smul_sub]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
  exact mul_le_mul_of_nonneg_left h hq

/-- Signed coordinate reversal, or any orthogonal map, preserves the actual
module-gradient contraction; its identity perturbation is strongly monotone. -/
theorem rotated_chain_residual_strong_monotone (profile : GateProfile)
    {tau q c lam : ℝ} (htau : tau ≠ 0) (hq : 0 ≤ q) (hlam : 0 ≤ lam)
    (terminal : J) (R : EuclideanSpace ℝ (J × Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (J × Fin 2))
    (v w : EuclideanSpace ℝ (J × Fin 2)) :
    lam * (1 - q) * ‖v - w‖ ^ 2 ≤
      inner ℝ
        (lam • (v - R (chainBlockGradient profile tau q c terminal v)) -
          lam • (w - R (chainBlockGradient profile tau q c terminal w))) (v - w) := by
  apply contraction_residual_strong_monotone hlam
  intro x y
  rw [← R.map_sub, R.norm_map]
  exact chainBlockGradient_norm_sub_le profile htau hq terminal y x

/-- The actual rotated module gradient has a unique fixed point whenever
0≤q<1. This is the Banach existence step for every finite chain size. -/
theorem rotated_chain_exists_unique_fixedPoint (profile : GateProfile)
    {tau q c : ℝ} (htau : tau ≠ 0) (hq : 0 ≤ q) (hqlt : q < 1)
    (terminal : J) (R : EuclideanSpace ℝ (J × Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (J × Fin 2)) :
    ∃! z, R (chainBlockGradient profile tau q c terminal z) = z := by
  let T : EuclideanSpace ℝ (J × Fin 2) → EuclideanSpace ℝ (J × Fin 2) :=
    fun z => R (chainBlockGradient profile tau q c terminal z)
  let K : NNReal := ⟨q, hq⟩
  have hL : LipschitzWith K T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖R (chainBlockGradient profile tau q c terminal x) -
      R (chainBlockGradient profile tau q c terminal y)‖ ≤ q * ‖x - y‖
    rw [← R.map_sub, R.norm_map]
    exact chainBlockGradient_norm_sub_le profile htau hq terminal y x
  have hC : ContractingWith K T := ⟨hqlt, hL⟩
  refine ⟨ContractingWith.fixedPoint T hC, hC.fixedPoint_isFixedPt, ?_⟩
  intro z hz
  exact hC.fixedPoint_unique hz

end FiniteChain

end MinimaxAudit
