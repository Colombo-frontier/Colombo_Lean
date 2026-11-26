import MinimaxAudit.ChainGradient
import MinimaxAudit.GateHighOrder
import MinimaxAudit.OrthogonalTensor

/-!
# Dimension-independent high-order bound for the actual block-chain potential

This file assembles the actual derivative tensors of the concrete scalar
potential. The product-sum bound is applied to its actual orthogonal block
projections, whose square norms add to the ambient squared norm. The number of
modules is an arbitrary finite cardinality and never appears in the bound.
-/

open scoped ContDiff

namespace MinimaxAudit

/-- The uniform module bound; its only tau dependence is tau^(1-p). -/
noncomputable def chainDerivativeConstant (p : ℕ) (profile : GateProfile) (tau : ℝ) : ℝ :=
  gateDerivativeConstant p profile tau * (1 + (2 : ℝ) ^ (p + 1))

/-- The fixed cutoff/order constant is independent of tau and chain length. -/
noncomputable def chainSmoothnessConstant (p : ℕ) (profile : GateProfile) : ℝ :=
  gateBp p profile * (1 + (2 : ℝ) ^ (p + 1))

theorem chainSmoothnessConstant_pos (p : ℕ) (profile : GateProfile) :
    0 < chainSmoothnessConstant p profile := by
  have hbp : 1 ≤ gateBp p profile := by
    unfold gateBp
    exact le_max_left _ _
  unfold chainSmoothnessConstant
  exact mul_pos (by linarith) (by positivity)

theorem chainDerivativeConstant_scale (p : ℕ) (profile : GateProfile) (tau : ℝ) :
    chainDerivativeConstant p profile tau =
      chainSmoothnessConstant p profile * tau ^ (1 - (p : ℤ)) := by
  unfold chainDerivativeConstant chainSmoothnessConstant gateDerivativeConstant
  ring

theorem chainDerivativeConstant_nonneg (p : ℕ) (profile : GateProfile)
    {tau : ℝ} (htau : 0 < tau) : 0 ≤ chainDerivativeConstant p profile tau := by
  unfold chainDerivativeConstant
  exact mul_nonneg (gateDerivativeConstant_nonneg p profile htau) (by positivity)

/-- The two coordinate forms on the fixed two-dimensional module have norm≤1. -/
theorem gatePlane_proj_norm_le (i : Fin 2) :
    ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa using PiLp.norm_apply_le v i

section FiniteChain
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] in
theorem chainModulePotential_contDiff (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (terminal j : J) :
    ContDiff ℝ ∞ (chainModulePotential profile tau terminal j) := by
  by_cases hj : j = terminal
  · have hfun : chainModulePotential profile tau terminal j =
        doubleGate profile tau ∘ EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) := by
      funext v
      simp [chainModulePotential, hj ]
    rw [hfun]
    exact (doubleGate_contDiff profile htau).comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  · have hfun : chainModulePotential profile tau terminal j =
        (fun z : ℝ × ℝ => scalarGate profile tau z.1 z.2) ∘
          (fun v : GatePlane => (v 0, v 1)) := by
      funext v
      simp [chainModulePotential, hj ]
    rw [hfun]
    exact (scalarGate_contDiff profile htau).comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.prodMk
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)

/- Uniform high-order derivative norm for every actual module, including H. -/
omit [Fintype J] in
theorem chainModule_high_derivative_bound (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (terminal j : J) (v : GatePlane) :
    ‖iteratedFDeriv ℝ (p + 1) (chainModulePotential profile tau terminal j) v‖ ≤
      chainDerivativeConstant p profile tau := by
  let A : GatePlane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let B : GatePlane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hA : ‖A‖ ≤ 1 := gatePlane_proj_norm_le 0
  have hB : ‖B‖ ≤ 1 := gatePlane_proj_norm_le 1
  have hK := gateDerivativeConstant_nonneg p profile htau
  have hpow : 0 ≤ (2 : ℝ) ^ (p + 1) := by positivity
  by_cases hj : j = terminal
  · have hfun : chainModulePotential profile tau terminal j = doubleGate profile tau ∘ A := by
      funext w
      simp [chainModulePotential, hj, A]
    rw [hfun]
    have h := doubleGate_pullback_high_derivative_bound profile hp htau A v
    have hApow := pow_le_pow_left₀ (norm_nonneg A) hA (p + 1)
    have hm := mul_le_mul_of_nonneg_left hApow hK
    dsimp [chainDerivativeConstant]
    norm_num only [one_pow] at hm
    nlinarith
  · have hfun : chainModulePotential profile tau terminal j =
        fun w => scalarGate profile tau (A w) (B w) := by
      funext w
      simp [chainModulePotential, hj, A, B]
    rw [hfun]
    have h := scalarGate_pullback_high_derivative_bound profile hp htau A B v
    have hplus : ‖A + B‖ ≤ 2 := (norm_add_le A B).trans (by linarith)
    have hminus : ‖A - B‖ ≤ 2 := (norm_sub_le A B).trans (by linarith)
    have hpplus := pow_le_pow_left₀ (norm_nonneg (A + B)) hplus (p + 1)
    have hpminus := pow_le_pow_left₀ (norm_nonneg (A - B)) hminus (p + 1)
    have hm1 := mul_le_mul_of_nonneg_left hpplus hK
    have hm2 := mul_le_mul_of_nonneg_left hpminus hK
    dsimp [chainDerivativeConstant]
    nlinarith

/-- Smoothness of the concrete assembled chain potential. -/
theorem chainBlockPotential_contDiff (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (q c : ℝ) (terminal : J) :
    ContDiff ℝ ∞ (chainBlockPotential profile tau q c terminal) := by
  have hmodule (j : J) : ContDiff ℝ ∞
      (fun v => chainModulePotential profile tau terminal j (gateBlockVector v j)) :=
    (chainModulePotential_contDiff profile htau terminal j).comp (gateBlockProjection j).contDiff
  have hsum : ContDiff ℝ ∞ (fun v =>
      ∑ j : J, chainModulePotential profile tau terminal j (gateBlockVector v j)) :=
    ContDiff.sum (fun j (_ : j ∈ (Finset.univ : Finset J)) => hmodule j)
  exact (contDiff_const.mul hsum).add (contDiff_const.mul
    (EuclideanSpace.proj (𝕜 := ℝ) (terminal, (1 : Fin 2))).contDiff)

/- Every derivative of a continuous linear seed of order at least two is zero. -/
omit [DecidableEq J] in
theorem linear_seed_high_derivative_zero {p : ℕ} (hp : 1 ≤ p)
    (A : EuclideanSpace ℝ (J × Fin 2) →L[ℝ] ℝ) (z : EuclideanSpace ℝ (J × Fin 2)) :
    iteratedFDeriv ℝ (p + 1) A z = 0 := by
  ext m
  rw [iteratedFDeriv_succ_apply_right]
  have hfun : fderiv ℝ (fun x => A x) = fun _ => A := by
    funext x
    exact A.fderiv
  rw [hfun]
  simp [iteratedFDeriv_const_of_ne (show p ≠ 0 by omega)]

/-- Actual tensor of each concrete module, pulled into ambient coordinates. -/
noncomputable def chainModuleTensor (profile : GateProfile) (tau : ℝ)
    (p : ℕ) (terminal j : J) (z : EuclideanSpace ℝ (J × Fin 2)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (p + 1) => EuclideanSpace ℝ (J × Fin 2)) ℝ :=
  (iteratedFDeriv ℝ (p + 1) (chainModulePotential profile tau terminal j) (gateBlockVector z j)).compContinuousLinearMap (fun _ => gateBlockProjection j)

/-- The actual derivative tensor is q times the sum of module tensors; the
linear seed disappears. This is derivative assembly, not a field assumption. -/
theorem chainBlockPotential_high_derivative_eq (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (q c : ℝ) (terminal : J)
    (z : EuclideanSpace ℝ (J × Fin 2)) :
    iteratedFDeriv ℝ (p + 1) (chainBlockPotential profile tau q c terminal) z =
      q • ∑ j : J, chainModuleTensor profile tau p terminal j z := by
  let f : EuclideanSpace ℝ (J × Fin 2) → ℝ :=
    fun v => ∑ j : J, chainModulePotential profile tau terminal j (gateBlockVector v j)
  let A : EuclideanSpace ℝ (J × Fin 2) →L[ℝ] ℝ :=
    c • EuclideanSpace.proj (terminal, (1 : Fin 2))
  have hmodule (j : J) : ContDiff ℝ (p + 1)
      (fun v => chainModulePotential profile tau terminal j (gateBlockVector v j)) :=
    (contDiff_infty.mp (chainModulePotential_contDiff profile htau.ne' terminal j) (p + 1)).comp (gateBlockProjection j).contDiff
  have hf : ContDiff ℝ (p + 1) f := ContDiff.sum (fun j _ => hmodule j)
  have hfun : chainBlockPotential profile tau q c terminal = fun v => q • f v + A v := by
    funext v
    simp [chainBlockPotential, f, A, smul_eq_mul]
  rw [hfun, fun_iteratedFDeriv_add_apply (hf.const_smul q).contDiffAt A.contDiff.contDiffAt,
    iteratedFDeriv_const_smul_apply' hf.contDiffAt,
    linear_seed_high_derivative_zero (by omega) A z, add_zero]
  congr 1
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => (hmodule j).contDiffAt)]
  apply Finset.sum_congr rfl
  intro j _
  exact (gateBlockProjection j).iteratedFDeriv_comp_right
    (contDiff_infty.mp (chainModulePotential_contDiff profile htau.ne' terminal j) (p + 1)) z le_rfl

/-- The actual sum of all pulled-back derivative tensors has dimension-free
operator norm. Orthogonal Pythagoras supplies the square-sum hypotheses. -/
theorem chainModuleTensor_sum_norm_le (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (terminal : J)
    (z : EuclideanSpace ℝ (J × Fin 2)) :
    ‖∑ j : J, chainModuleTensor profile tau p terminal j z‖ ≤
      chainDerivativeConstant p profile tau := by
  have hC := chainDerivativeConstant_nonneg p profile htau
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro m
  let l0 : Fin (p + 1) := ⟨0, by omega⟩
  let l1 : Fin (p + 1) := ⟨1, by omega⟩
  have hne : l0 ≠ l1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [l0, l1] at hv
  have hprod := module_product_sum_le_product
    (Finset.univ : Finset J) (Finset.univ : Finset (Fin (p + 1)))
    (fun j l => ‖gateBlockVector (m l) j‖) (fun l => ‖m l‖)
    (l0 := l0) (l1 := l1) (by simp) (by simp) hne
    (fun j _ l _ => norm_nonneg _) (fun l _ => norm_nonneg _)
    (fun l _ => (gateBlock_norm_sq (m l)).ge)
  have hvalue (j : J) : ‖chainModuleTensor profile tau p terminal j z m‖ ≤
      chainDerivativeConstant p profile tau * ∏ l, ‖gateBlockVector (m l) j‖ := by
    simpa [chainModuleTensor, gateBlockProjection] using
      ContinuousMultilinearMap.le_of_opNorm_le
        (chainModule_high_derivative_bound profile hp htau terminal j (gateBlockVector z j))
        (fun l => gateBlockVector (m l) j)
  calc
    ‖(∑ j : J, chainModuleTensor profile tau p terminal j z) m‖ ≤
        ∑ j : J, ‖chainModuleTensor profile tau p terminal j z m‖ := by
      simp only [sum_apply]
      exact norm_sum_le _ _
    _ ≤ ∑ j : J, chainDerivativeConstant p profile tau * ∏ l, ‖gateBlockVector (m l) j‖ :=
      Finset.sum_le_sum (fun j _ => hvalue j)
    _ = chainDerivativeConstant p profile tau *
        ∑ j : J, ∏ l, ‖gateBlockVector (m l) j‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ chainDerivativeConstant p profile tau * ∏ l, ‖m l‖ :=
      mul_le_mul_of_nonneg_left hprod hC

/-- Dimension-free high-order bound for the actual concrete scalar potential,
for every finite number of gate modules and every p≥2. -/
theorem chainBlockPotential_high_derivative_bound (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (q c : ℝ) (terminal : J)
    (z : EuclideanSpace ℝ (J × Fin 2)) :
    ‖iteratedFDeriv ℝ (p + 1) (chainBlockPotential profile tau q c terminal) z‖ ≤
      |q| * chainDerivativeConstant p profile tau := by
  rw [chainBlockPotential_high_derivative_eq profile hp htau q c terminal z,
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (chainModuleTensor_sum_norm_le profile hp htau terminal z) (abs_nonneg q)

/-- The actual p-th derivative of the concrete scalar block potential is
Lipschitz with the same dimension-independent constant. -/
theorem chainBlockPotential_high_derivative_lipschitz (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (q c : ℝ) (terminal : J)
    (v w : EuclideanSpace ℝ (J × Fin 2)) :
    ‖iteratedFDeriv ℝ p (chainBlockPotential profile tau q c terminal) w -
      iteratedFDeriv ℝ p (chainBlockPotential profile tau q c terminal) v‖ ≤
        (|q| * chainDerivativeConstant p profile tau) * ‖w - v‖ := by
  have hc := chainBlockPotential_contDiff profile htau.ne' q c terminal
  have hd : Differentiable ℝ
      (iteratedFDeriv ℝ p (chainBlockPotential profile tau q c terminal)) :=
    ContDiff.differentiable_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self p) (contDiff_infty.mp hc (p + 1))
  have hb (z : EuclideanSpace ℝ (J × Fin 2)) :
      ‖fderiv ℝ (iteratedFDeriv ℝ p (chainBlockPotential profile tau q c terminal)) z‖ ≤
        |q| * chainDerivativeConstant p profile tau := by
    rw [norm_fderiv_iteratedFDeriv]
    exact chainBlockPotential_high_derivative_bound profile hp htau q c terminal z
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd z) (fun z _ => hb z) (Set.mem_univ v) (Set.mem_univ w)

/-- Pulling the actual scalar chain back through a contraction, including a
frame-coordinate projection, preserves the dimension-free high derivative bound. -/
theorem chainBlockPotential_pullback_high_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau)
    (q c : ℝ) (terminal : J) (A : E →L[ℝ] EuclideanSpace ℝ (J × Fin 2))
    (hA : ‖A‖ ≤ 1) (z : E) :
    ‖iteratedFDeriv ℝ (p + 1) (chainBlockPotential profile tau q c terminal ∘ A) z‖ ≤
      |q| * chainDerivativeConstant p profile tau := by
  rw [A.iteratedFDeriv_comp_right
    (contDiff_infty.mp (chainBlockPotential_contDiff profile htau.ne' q c terminal) (p + 1)) z le_rfl]
  have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ (p + 1) (chainBlockPotential profile tau q c terminal) (A z))
    (fun _ => A)
  have hpow := pow_le_pow_left₀ (norm_nonneg A) hA (p + 1)
  have hC : 0 ≤ |q| * chainDerivativeConstant p profile tau :=
    mul_nonneg (abs_nonneg q) (chainDerivativeConstant_nonneg p profile htau)
  have hmodule := chainBlockPotential_high_derivative_bound profile hp htau q c terminal (A z)
  have hmul := mul_le_mul hmodule hpow (pow_nonneg (norm_nonneg A) _) hC
  calc
    _ ≤ ‖iteratedFDeriv ℝ (p + 1) (chainBlockPotential profile tau q c terminal) (A z)‖ *
        ‖A‖ ^ (p + 1) := by simpa using hnorm
    _ ≤ |q| * chainDerivativeConstant p profile tau := by simpa using hmul

end FiniteChain

end MinimaxAudit
