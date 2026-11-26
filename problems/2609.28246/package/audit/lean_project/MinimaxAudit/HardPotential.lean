import MinimaxAudit.FrameOperators
import MinimaxAudit.ChainSmoothness

/-!
# The actual framed scalar hard potential

The potential below uses the manuscript's concrete integral chain, the actual
paired Euclidean frame, and the actual primal/dual saddle signature. Generic
involutive orthogonal signatures are used only to prove reusable calculus
lemmas; the final specialization uses euclideanSaddleSign and blockPairedFrame.
-/

open scoped ContDiff

namespace MinimaxAudit

section Signature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthogonal involution is self-adjoint. -/
theorem involutive_isometry_inner (S : E ≃ₗᵢ[ℝ] E)
    (hS : Function.Involutive S) (x y : E) :
    inner ℝ (S x) y = inner ℝ x (S y) := by
  have h := S.inner_map_map x (S y)
  simpa [hS y] using h

noncomputable def signedQuadratic (S : E ≃ₗᵢ[ℝ] E) (z : E) : ℝ :=
  inner ℝ (S z) z / 2

/-- Full Fréchet gradient of the signed quadratic term. -/
theorem signedQuadratic_hasFDerivAt (S : E ≃ₗᵢ[ℝ] E)
    (hS : Function.Involutive S) (z : E) :
    HasFDerivAt (signedQuadratic S) (innerSL ℝ (S z)) z := by
  have h := (S.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.inner ℝ
    (hasFDerivAt_id z)).const_mul (1 / 2 : ℝ)
  convert! h using 1
  · ext w
    simp [signedQuadratic]
    ring
  · ext w
    simp [innerSL_apply_apply, fderivInnerCLM_apply]
    rw [involutive_isometry_inner S hS w z, real_inner_comm w (S z)]
    ring

theorem signedQuadratic_contDiff (S : E ≃ₗᵢ[ℝ] E) :
    ContDiff ℝ ∞ (signedQuadratic S) := by
  exact (S.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.inner ℝ contDiff_id).div_const 2

/-- Continuous linear maps have no derivatives of order two or above. -/
theorem clm_high_derivative_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℕ} (hp : 1 ≤ p) (A : E →L[ℝ] F) (z : E) :
    iteratedFDeriv ℝ (p + 1) A z = 0 := by
  ext m
  rw [iteratedFDeriv_succ_apply_right]
  have hfun : fderiv ℝ (fun x => A x) = fun _ => A := by
    funext x
    exact A.fderiv
  rw [hfun]
  simp [iteratedFDeriv_const_of_ne (show p ≠ 0 by omega)]

/-- The concrete signed quadratic contributes no p+1 tensor when p≥2. -/
theorem signedQuadratic_high_derivative_zero (S : E ≃ₗᵢ[ℝ] E)
    (hS : Function.Involutive S) {p : ℕ} (hp : 2 ≤ p) (z : E) :
    iteratedFDeriv ℝ (p + 1) (signedQuadratic S) z = 0 := by
  let L : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp S.toContinuousLinearEquiv.toContinuousLinearMap
  have hfun : fderiv ℝ (signedQuadratic S) = fun z => L z := by
    funext z
    exact (signedQuadratic_hasFDerivAt S hS z).fderiv
  ext m
  rw [iteratedFDeriv_succ_apply_right, hfun]
  have hzero : iteratedFDeriv ℝ p L z = 0 := by
    have heq : p = (p - 1) + 1 := by omega
    rw [heq]
    exact clm_high_derivative_zero (by omega) L z
  rw [hzero]
  simp

end Signature

section Framed
variable {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {W : J × Fin 2 → E}

noncomputable def framedHardPotential (profile : GateProfile) (tau lam q c : ℝ)
    (S : E ≃ₗᵢ[ℝ] E) (hW : Orthonormal ℝ W) (terminal : J) (z : E) : ℝ :=
  lam * (signedQuadratic S z - chainBlockPotential profile tau q c terminal (frameAnalysis hW z))

/-- Exact full derivative of the actual scalar hard potential. -/
theorem framedHardPotential_hasFDerivAt (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (lam q c : ℝ) (S : E ≃ₗᵢ[ℝ] E)
    (hS : Function.Involutive S) (hW : Orthonormal ℝ W) (terminal : J) (z : E) :
    HasFDerivAt (framedHardPotential profile tau lam q c S hW terminal)
      (innerSL ℝ (lam • (S z - frameSynthesis hW
        (chainBlockGradient profile tau q c terminal (frameAnalysis hW z))))) z := by
  have hpull := (chainBlockPotential_hasFDerivAt profile htau q c terminal (frameAnalysis hW z)).comp z (frameAnalysis hW).hasFDerivAt
  have hpull' : HasFDerivAt
      (fun w => chainBlockPotential profile tau q c terminal (frameAnalysis hW w))
      (innerSL ℝ (frameSynthesis hW
        (chainBlockGradient profile tau q c terminal (frameAnalysis hW z)))) z := by
    convert! hpull using 1
    ext w
    simp only [innerSL_apply_apply, ContinuousLinearMap.comp_apply]
    exact (frame_adjoint_pairing hW _ w).symm
  have h := ((signedQuadratic_hasFDerivAt S hS z).sub hpull').const_mul lam
  convert! h using 1
  ext w
  simp [innerSL_apply_apply]

/-- The actual framed scalar potential is globally smooth. -/
theorem framedHardPotential_contDiff (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (lam q c : ℝ) (S : E ≃ₗᵢ[ℝ] E)
    (hW : Orthonormal ℝ W) (terminal : J) :
    ContDiff ℝ ∞ (framedHardPotential profile tau lam q c S hW terminal) := by
  exact contDiff_const.mul ((signedQuadratic_contDiff S).sub
    ((chainBlockPotential_contDiff profile htau q c terminal).comp (frameAnalysis hW).contDiff))

/-- Contractivity of the actual frame analysis operator. -/
theorem framed_analysis_opNorm_le (hW : Orthonormal ℝ W) : ‖frameAnalysis hW‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa [frameAnalysis] using frameAnalysis_norm_le hW z

/-- The concrete rotated chain perturbation is q-Lipschitz in ambient space. -/
theorem framedHardPerturbation_norm_sub_le (profile : GateProfile) {tau q c : ℝ}
    (htau : tau ≠ 0) (hq : 0 ≤ q) (S : E ≃ₗᵢ[ℝ] E)
    (hW : Orthonormal ℝ W) (terminal : J) (z w : E) :
    ‖S (frameSynthesis hW (chainBlockGradient profile tau q c terminal (frameAnalysis hW z))) -
      S (frameSynthesis hW (chainBlockGradient profile tau q c terminal (frameAnalysis hW w)))‖ ≤
        q * ‖z - w‖ := by
  rw [← S.map_sub, S.norm_map, ← (frameSynthesis hW).map_sub, (frameSynthesis hW).norm_map]
  have h := chainBlockGradient_norm_sub_le profile (c := c) htau hq terminal (frameAnalysis hW w) (frameAnalysis hW z)
  have ha : ‖frameAnalysis hW z - frameAnalysis hW w‖ ≤ ‖z - w‖ := by
    rw [← map_sub]
    exact frameAnalysis_norm_le hW (z - w)
  exact h.trans (mul_le_mul_of_nonneg_left ha hq)

/-- The p+1 derivative of the actual framed scalar potential has the required
uniform tau^(1-p) bound; the quadratic tensor vanishes and the frame contracts. -/
theorem framedHardPotential_high_derivative_bound (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (lam q c : ℝ)
    (S : E ≃ₗᵢ[ℝ] E) (hS : Function.Involutive S)
    (hW : Orthonormal ℝ W) (terminal : J) (z : E) :
    ‖iteratedFDeriv ℝ (p + 1) (framedHardPotential profile tau lam q c S hW terminal) z‖ ≤
      |lam| * |q| * chainDerivativeConstant p profile tau := by
  have hcQ := contDiff_infty.mp (signedQuadratic_contDiff S) (p + 1)
  have hcP := (contDiff_infty.mp (chainBlockPotential_contDiff profile htau.ne' q c terminal) (p + 1)).comp (frameAnalysis hW).contDiff
  have hfun : framedHardPotential profile tau lam q c S hW terminal =
      fun z => lam • (signedQuadratic S z -
        (chainBlockPotential profile tau q c terminal ∘ frameAnalysis hW) z) := by
    funext z
    rfl
  rw [hfun, iteratedFDeriv_const_smul_apply' (hcQ.sub hcP).contDiffAt]
  change ‖lam • iteratedFDeriv ℝ (p + 1)
    (signedQuadratic S - chainBlockPotential profile tau q c terminal ∘ frameAnalysis hW) z‖ ≤ _
  rw [iteratedFDeriv_sub_apply hcQ.contDiffAt hcP.contDiffAt,
    signedQuadratic_high_derivative_zero S hS hp z, zero_sub, norm_smul, norm_neg, Real.norm_eq_abs]
  have h := chainBlockPotential_pullback_high_derivative_bound profile hp htau q c terminal
    (frameAnalysis hW) (framed_analysis_opNorm_le hW) z
  have hm := mul_le_mul_of_nonneg_left h (abs_nonneg lam)
  simpa [mul_assoc] using hm

variable [CompleteSpace E]

/-- Identification with Mathlib's actual Euclidean/Hilbert gradient. -/
theorem framedHardPotential_gradient (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (lam q c : ℝ) (S : E ≃ₗᵢ[ℝ] E)
    (hS : Function.Involutive S) (hW : Orthonormal ℝ W) (terminal : J) (z : E) :
    gradient (framedHardPotential profile tau lam q c S hW terminal) z =
      lam • (S z - frameSynthesis hW
        (chainBlockGradient profile tau q c terminal (frameAnalysis hW z))) := by
  have hd := framedHardPotential_hasFDerivAt profile htau lam q c S hS hW terminal z
  have hg : HasGradientAt (framedHardPotential profile tau lam q c S hW terminal)
      (lam • (S z - frameSynthesis hW
        (chainBlockGradient profile tau q c terminal (frameAnalysis hW z)))) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hd
  exact hd.differentiableAt.hasGradientAt.unique hg

/-- The actual signed gradient has exactly the identity-minus-perturbation form. -/
theorem framedHardPotential_saddle_operator (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (lam q c : ℝ) (S : E ≃ₗᵢ[ℝ] E)
    (hS : Function.Involutive S) (hW : Orthonormal ℝ W) (terminal : J) (z : E) :
    S (gradient (framedHardPotential profile tau lam q c S hW terminal) z) =
      lam • (z - S (frameSynthesis hW
        (chainBlockGradient profile tau q c terminal (frameAnalysis hW z)))) := by
  rw [framedHardPotential_gradient profile htau lam q c S hS hW terminal z,
    S.map_smul, S.map_sub, hS z]

/-- Strong monotonicity of the actual scalar saddle operator. -/
theorem framedHardPotential_strong_monotone (profile : GateProfile) {tau q lam c : ℝ}
    (htau : tau ≠ 0) (hq : 0 ≤ q) (hlam : 0 ≤ lam) (S : E ≃ₗᵢ[ℝ] E)
    (hS : Function.Involutive S) (hW : Orthonormal ℝ W) (terminal : J) (z w : E) :
    lam * (1 - q) * ‖z - w‖ ^ 2 ≤
      inner ℝ (S (gradient (framedHardPotential profile tau lam q c S hW terminal) z) -
        S (gradient (framedHardPotential profile tau lam q c S hW terminal) w)) (z - w) := by
  rw [framedHardPotential_saddle_operator profile htau lam q c S hS hW terminal z,
    framedHardPotential_saddle_operator profile htau lam q c S hS hW terminal w]
  exact contraction_residual_strong_monotone hlam
    (fun x y => framedHardPerturbation_norm_sub_le profile htau hq S hW terminal x y) z w

/- The actual p-th derivative has the same global Lipschitz constant. -/
omit [CompleteSpace E] in
theorem framedHardPotential_high_derivative_lipschitz (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (lam q c : ℝ)
    (S : E ≃ₗᵢ[ℝ] E) (hS : Function.Involutive S)
    (hW : Orthonormal ℝ W) (terminal : J) (z w : E) :
    ‖iteratedFDeriv ℝ p (framedHardPotential profile tau lam q c S hW terminal) w -
      iteratedFDeriv ℝ p (framedHardPotential profile tau lam q c S hW terminal) z‖ ≤
        (|lam| * |q| * chainDerivativeConstant p profile tau) * ‖w - z‖ := by
  have hc := framedHardPotential_contDiff profile htau.ne' lam q c S hW terminal
  have hd : Differentiable ℝ
      (iteratedFDeriv ℝ p (framedHardPotential profile tau lam q c S hW terminal)) :=
    ContDiff.differentiable_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self p) (contDiff_infty.mp hc (p + 1))
  have hb (u : E) :
      ‖fderiv ℝ (iteratedFDeriv ℝ p (framedHardPotential profile tau lam q c S hW terminal)) u‖ ≤
        |lam| * |q| * chainDerivativeConstant p profile tau := by
    rw [norm_fderiv_iteratedFDeriv]
    exact framedHardPotential_high_derivative_bound profile hp htau lam q c S hS hW terminal u
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun u _ => hd u) (fun u _ => hb u) (Set.mem_univ z) (Set.mem_univ w)

/-- The ambient actual scalar saddle operator has a unique zero when q<1 and
λ>0. This does not yet bound its coordinates or place it inside the public balls. -/
theorem framedHardPotential_exists_unique_zero (profile : GateProfile)
    {tau q lam c : ℝ} (htau : tau ≠ 0) (hq : 0 ≤ q) (hqlt : q < 1) (hlam : 0 < lam)
    (S : E ≃ₗᵢ[ℝ] E) (hS : Function.Involutive S)
    (hW : Orthonormal ℝ W) (terminal : J) :
    ∃! z, S (gradient (framedHardPotential profile tau lam q c S hW terminal) z) = 0 := by
  let T : E → E := fun z => S (frameSynthesis hW
    (chainBlockGradient profile tau q c terminal (frameAnalysis hW z)))
  let K : NNReal := ⟨q, hq⟩
  have hK : (K : ℝ) = q := rfl
  have hL : LipschitzWith K T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, hK]
    change ‖S (frameSynthesis hW (chainBlockGradient profile tau q c terminal (frameAnalysis hW x))) -
      S (frameSynthesis hW (chainBlockGradient profile tau q c terminal (frameAnalysis hW y)))‖ ≤
        q * ‖x - y‖
    exact framedHardPerturbation_norm_sub_le profile (c := c) htau hq S hW terminal x y
  have hC : ContractingWith K T := ⟨hqlt, hL⟩
  refine ⟨ContractingWith.fixedPoint T hC, ?_, ?_⟩
  · change S (gradient (framedHardPotential profile tau lam q c S hW terminal)
      (ContractingWith.fixedPoint T hC)) = 0
    rw [framedHardPotential_saddle_operator profile htau lam q c S hS hW terminal]
    change lam • (ContractingWith.fixedPoint T hC - T (ContractingWith.fixedPoint T hC)) = 0
    rw [hC.fixedPoint_isFixedPt]
    simp
  · intro z hz
    change S (gradient (framedHardPotential profile tau lam q c S hW terminal) z) = 0 at hz
    rw [framedHardPotential_saddle_operator profile htau lam q c S hS hW terminal] at hz
    have hsub : z - T z = 0 := (smul_eq_zero.mp hz).resolve_left (ne_of_gt hlam)
    exact hC.fixedPoint_unique (sub_eq_zero.mp hsub).symm

end Framed

/-- The actual source saddle signature is an involution. -/
theorem euclideanSaddleSign_involutive (dx dy : ℕ) :
    Function.Involutive (euclideanSaddleSign dx dy) := by
  intro z
  ext i
  cases i <;> simp [euclideanSaddleSign]

/-- Actual source potential, in the equivalent orthogonal module ordering. -/
noncomputable def minimaxHardPotential {n dx dy : ℕ} (profile : GateProfile)
    (tau lam q c : ℝ) {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) : SaddleSpace dx dy → ℝ :=
  framedHardPotential profile tau lam q c (euclideanSaddleSign dx dy)
    (blockPairedFrame_orthonormal hU hV) (Fin.last n)

/-- Strong monotonicity is instantiated for the actual primal/dual signed
scalar gradient and actual paired frame, without an assumed operator formula. -/
theorem minimaxHardPotential_strong_monotone {n dx dy : ℕ} (profile : GateProfile)
    {tau q lam c : ℝ} (htau : tau ≠ 0) (hq : 0 ≤ q) (hlam : 0 ≤ lam)
    {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (z w : SaddleSpace dx dy) :
    lam * (1 - q) * ‖z - w‖ ^ 2 ≤
      inner ℝ
        (euclideanSaddleSign dx dy (gradient (minimaxHardPotential profile tau lam q c hU hV) z) -
          euclideanSaddleSign dx dy (gradient (minimaxHardPotential profile tau lam q c hU hV) w)) (z - w) := by
  exact framedHardPotential_strong_monotone profile htau hq hlam (euclideanSaddleSign dx dy)
    (euclideanSaddleSign_involutive dx dy) (blockPairedFrame_orthonormal hU hV) (Fin.last n) z w

/-- Exact operator formula specialized to the actual source signature/frame. -/
theorem minimaxHardPotential_saddle_operator {n dx dy : ℕ} (profile : GateProfile)
    {tau : ℝ} (htau : tau ≠ 0) (lam q c : ℝ)
    {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (z : SaddleSpace dx dy) :
    euclideanSaddleSign dx dy (gradient (minimaxHardPotential profile tau lam q c hU hV) z) =
      lam • (z - euclideanSaddleSign dx dy
        (frameSynthesis (blockPairedFrame_orthonormal hU hV)
          (chainBlockGradient profile tau q c (Fin.last n)
            (frameAnalysis (blockPairedFrame_orthonormal hU hV) z)))) :=
  framedHardPotential_saddle_operator profile htau lam q c (euclideanSaddleSign dx dy)
    (euclideanSaddleSign_involutive dx dy) (blockPairedFrame_orthonormal hU hV) (Fin.last n) z

/-- Full actual source-potential smoothness, including the highest derivative
Lipschitz estimate, with a constant independent of ambient dimension and n. -/
theorem minimaxHardPotential_high_derivative_lipschitz {n dx dy : ℕ} (profile : GateProfile)
    {p : ℕ} (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (lam q c : ℝ)
    {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (z w : SaddleSpace dx dy) :
    ‖iteratedFDeriv ℝ p (minimaxHardPotential profile tau lam q c hU hV) w -
      iteratedFDeriv ℝ p (minimaxHardPotential profile tau lam q c hU hV) z‖ ≤
      (|lam| * |q| * chainDerivativeConstant p profile tau) * ‖w - z‖ :=
  framedHardPotential_high_derivative_lipschitz profile hp htau lam q c (euclideanSaddleSign dx dy)
    (euclideanSaddleSign_involutive dx dy) (blockPairedFrame_orthonormal hU hV) (Fin.last n) z w

/-- With the manuscript's amplitude calibration and 0≤q≤1, the concrete
source objective satisfies Lip(D^p φ)≤L on the entire ambient space. -/
theorem minimaxHardPotential_calibrated_smoothness {n dx dy : ℕ} (profile : GateProfile)
    {p : ℕ} (hp : 2 ≤ p) {tau L q c : ℝ} (htau : 0 < tau) (hL : 0 ≤ L)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (z w : SaddleSpace dx dy) :
    let lam := L * tau ^ (p - 1) / chainSmoothnessConstant p profile
    ‖iteratedFDeriv ℝ p (minimaxHardPotential profile tau lam q c hU hV) w -
      iteratedFDeriv ℝ p (minimaxHardPotential profile tau lam q c hU hV) z‖ ≤ L * ‖w - z‖ := by
  intro lam
  have hC := chainSmoothnessConstant_pos p profile
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hexp : 1 - (p : ℤ) = -((p - 1 : ℕ) : ℤ) := by omega
  have hcal : lam * chainDerivativeConstant p profile tau = L := by
    rw [chainDerivativeConstant_scale, hexp, zpow_neg, zpow_natCast]
    dsimp [lam]
    field_simp [ne_of_gt hC, pow_ne_zero (p - 1) htau.ne']
  have hscale : |lam| * |q| * chainDerivativeConstant p profile tau ≤ L := by
    rw [abs_of_nonneg hlam, abs_of_nonneg hq0]
    calc
      lam * q * chainDerivativeConstant p profile tau =
          q * (lam * chainDerivativeConstant p profile tau) := by ring
      _ = q * L := by rw [hcal]
      _ ≤ L := by nlinarith
  exact (minimaxHardPotential_high_derivative_lipschitz profile hp htau lam q c hU hV z w).trans
    (mul_le_mul_of_nonneg_right hscale (norm_nonneg (w - z)))

end MinimaxAudit
