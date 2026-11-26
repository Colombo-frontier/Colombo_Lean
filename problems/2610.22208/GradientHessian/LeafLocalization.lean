import GradientHessian.LeafFunctions

/-! Actual numerical gradients, convex-mixture localization, and capped-leaf
activation. Additional terms may be arbitrary on the other physical blocks. -/

noncomputable section
namespace GradientHessian.Leaf
open InnerCoordinates
open scoped InnerProductSpace

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {m : ℕ}

def numericalForce (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (Z : Space Y E m) : Y :=
  gradient (fun y => Inner.residual b a v (replaceNumerical Z y))
    (numerical Y E m (Inner.absoluteDepth+2) Z)

def numericalMatrix (A : Y →L[ℝ] Y) (Z : Space Y E m) : Y →L[ℝ] Y :=
  LeafNumerical.gradientMatrix m (capRadius m) A (numerical Y E m (Inner.absoluteDepth+2) Z)

omit [CompleteSpace E] in
theorem numericalForce_bound (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1) (Z : Space Y E m) :
    ‖numericalForce b a v Z‖ ≤ Inner.innerConstant :=
  (Inner.residual_numerical_gradient_bound b a v hb ha Z).trans Inner.innerConstant_numerical

omit [CompleteSpace Y] [CompleteSpace E] in
theorem numericalMatrix_lower (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hA : InverseGate.LowerBound A) (hAn : ‖A‖ ≤ m) (Z : Space Y E m) :
    InverseGate.LowerBound (numericalMatrix A Z) :=
  LeafNumerical.gradientMatrix_lower (by exact_mod_cast hm) (capRadius_pos hm) A hA hAn _

omit [CompleteSpace Y] [CompleteSpace E] in
theorem numericalMatrix_norm (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hAn : ‖A‖ ≤ m) (Z : Space Y E m) : ‖numericalMatrix A Z‖ ≤ 12*m :=
  LeafNumerical.gradientMatrix_norm (Nat.cast_nonneg m) (capRadius_pos hm) A hAn _

omit [CompleteSpace Y] [CompleteSpace E] in
theorem replaceNumerical_contDiff (Z : Space Y E m) : ContDiff ℝ 3 (replaceNumerical Z) :=
  contDiff_const.add ((insertNumerical Y E m (Inner.absoluteDepth+2)).contDiff.comp
    (contDiff_id.sub contDiff_const))

omit [CompleteSpace E] in
theorem objective_numerical_hasGradientAt (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    HasGradientAt (fun y => objective A b a v (replaceNumerical Z y))
      (numericalMatrix A Z (numerical Y E m (Inner.absoluteDepth+2) Z) + numericalForce b a v Z)
      (numerical Y E m (Inner.absoluteDepth+2) Z) := by
  have hf := (((Inner.residual_contDiff b a v).comp (replaceNumerical_contDiff Z)).differentiable
    (by norm_num) (numerical Y E m (Inner.absoluteDepth+2) Z)).hasGradientAt.hasFDerivAt
  have h := ((LeafNumerical.base_hasGradientAt (M := m) (capRadius_pos hm) A hsym
    (numerical Y E m (Inner.absoluteDepth+2) Z)).hasFDerivAt.add_const
      (Inner.publicQuadratic m Inner.absoluteDepth Z)).add hf
  have he : (fun y => objective A b a v (replaceNumerical Z y)) =
      (fun y => LeafNumerical.base m (capRadius m) A y +
        Inner.publicQuadratic m Inner.absoluteDepth Z + Inner.residual b a v (replaceNumerical Z y)) := by
    funext y
    simp only [objective_decomposition, numerical_replaceNumerical, Inner.publicQuadratic,
      tasks_replaceNumerical]
  rw [hasGradientAt_iff_hasFDerivAt, he]
  simpa only [map_add] using h

omit [CompleteSpace E] in
theorem publicQuadratic_numerical_hasGradientAt (Z : Space Y E m) :
    HasGradientAt (fun y => publicQuadratic m (replaceNumerical Z y))
      ((2*(m:ℝ)) • numerical Y E m (Inner.absoluteDepth+2) Z)
      (numerical Y E m (Inner.absoluteDepth+2) Z) := by
  have he : (fun y => publicQuadratic m (replaceNumerical Z y)) =
      (fun y => (m:ℝ)*‖y‖^2 + Inner.publicQuadratic m Inner.absoluteDepth Z) := by
    funext y
    simp [publicQuadratic, Inner.publicQuadratic]
  rw [hasGradientAt_iff_hasFDerivAt, he]
  convert ((hasStrictFDerivAt_norm_sq (numerical Y E m (Inner.absoluteDepth+2) Z)).hasFDerivAt.const_mul
    (m:ℝ)).add_const (Inner.publicQuadratic m Inner.absoluteDepth Z) using 1
  ext z
  simp only [InnerProductSpace.toDual_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply,
    innerSL_apply, smul_eq_mul, two_smul, ContinuousLinearMap.add_apply]
  ring

omit [CompleteSpace E] in
theorem driven_numerical_hasGradientAt (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin (m+1) → Y)
    (v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E) (l : ℝ) (Z : Space Y E (m+1)) :
    HasGradientAt (fun y => driven A b a v l (replaceNumerical Z y))
      (numericalMatrix A Z (numerical Y E (m+1) (Inner.absoluteDepth+2) Z) + numericalForce b a v Z)
      (numerical Y E (m+1) (Inner.absoluteDepth+2) Z) := by
  have h := (objective_numerical_hasGradientAt (by omega) A hsym b a v Z).hasFDerivAt.sub_const
    (l*outgoing v Z)
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [driven, outgoing, Inner.outgoing, Inner.ports, tasks_replaceNumerical] using h

theorem driven_localization (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A) (hAn : ‖A‖ ≤ m+1)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin (m+1) → Y)
    (v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1) (l : ℝ) (Z : Space Y E (m+1))
    (hg : ‖gradient (driven A b a v l) Z‖ ≤ 1) :
    ‖numerical Y E (m+1) (Inner.absoluteDepth+2) Z‖ ≤ numericalRadius := by
  have hs := (numerical_slice_gradient_norm_le Z (driven A b a v l)
    ((driven_contDiff A b a v l).differentiable (by norm_num) Z)).trans hg
  rw [(driven_numerical_hasGradientAt A hsym b a v l Z).gradient] at hs
  have hl := LeafNumerical.localization (numericalMatrix A Z)
    (numericalMatrix_lower (by omega) A hA (by simpa using hAn) Z) _ _
    (numericalForce_bound b a v hb ha Z) hs
  unfold numericalRadius
  linarith

theorem activation (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A) (hAn : ‖A‖ ≤ m+1)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin (m+1) → Y)
    (v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1)
    (hcert : ∀ i, InverseGate.H₀/4 ≤ ⟪a i,InverseGate.inverse A hA (b i)⟫_ℝ)
    (hv : ∀ i j, ‖v i j‖ = 1) {l : ℝ} (hl : 0 ≤ l) (Z : Space Y E (m+1))
    (hg : ‖gradient (driven A b a v l) Z‖ ≤ 1) :
    outgoing v Z = 1 ∧ (∀ i, Inner.ports v Z i = 1) ∧
      ‖A (numerical Y E (m+1) (Inner.absoluteDepth+2) Z)‖ ≤ 1 := by
  have hZ := driven_localization A hA hAn hsym b a v hb ha l Z hg
  have he := objective_eventually_eq_inner (by omega) A b a v Z
    (lt_of_le_of_lt hZ (numericalRadius_lt_capRadius (by omega)))
  have hd : driven A b a v l =ᶠ[nhds Z] Inner.driven A b a v l := by
    filter_upwards [he] with W hW
    exact congrArg (fun t => t-l*outgoing v W) hW
  have hgrad : gradient (driven A b a v l) Z = gradient (Inner.driven A b a v l) Z := by
    unfold gradient
    rw [hd.fderiv_eq]
  rw [hgrad] at hg
  have h := Inner.absolute_activation A hA hsym b a v hb ha hcert hv hl Z hg
  exact ⟨h.1 (Fin.last m), h⟩

def mixture {ι : Type*} [Fintype ι] (q : ℝ) (w : ι → ℝ)
    (A : ι → Y →L[ℝ] Y) (b a : ι → Fin m → Y)
    (v : ι → Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) : ℝ :=
  q*publicQuadratic m Z + ∑ i, w i*objective (A i) (b i) (a i) (v i) Z

omit [CompleteSpace E] in
theorem mixture_numerical_hasGradientAt {ι : Type*} [Fintype ι] (hm : 1 ≤ m)
    (q : ℝ) (w : ι → ℝ) (A : ι → Y →L[ℝ] Y)
    (hsym : ∀ i x z, ⟪A i x,z⟫_ℝ = ⟪x,A i z⟫_ℝ) (b a : ι → Fin m → Y)
    (v : ι → Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    HasGradientAt (fun y => mixture q w A b a v (replaceNumerical Z y))
      ((q*(2*(m:ℝ))) • numerical Y E m (Inner.absoluteDepth+2) Z +
        ∑ i, w i • (numericalMatrix (A i) Z (numerical Y E m (Inner.absoluteDepth+2) Z) +
          numericalForce (b i) (a i) (v i) Z))
      (numerical Y E m (Inner.absoluteDepth+2) Z) := by
  have hp := (publicQuadratic_numerical_hasGradientAt Z).hasFDerivAt.const_mul q
  have hl := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (objective_numerical_hasGradientAt hm (A i) (hsym i) (b i) (a i) (v i) Z).hasFDerivAt.const_mul (w i))
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [mixture, map_add, map_sum, map_smul, smul_smul] using hp.add hl

/-- The full-gradient localization used by the hierarchy. Its extra term
is required only to be constant along the actual numerical slice. -/
theorem mixture_localization {ι : Type*} [Fintype ι] (hm : 1 ≤ m)
    (q : ℝ) (w : ι → ℝ) (hq : 0 ≤ q) (hw : ∀ i, 0 ≤ w i) (hsum : q+∑ i, w i = 1)
    (A : ι → Y →L[ℝ] Y) (hA : ∀ i, InverseGate.LowerBound (A i)) (hAn : ∀ i, ‖A i‖ ≤ m)
    (hsym : ∀ i x z, ⟪A i x,z⟫_ℝ = ⟪x,A i z⟫_ℝ) (b a : ι → Fin m → Y)
    (v : ι → Fin m → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i j, ‖b i j‖ = InverseGate.H₀) (ha : ∀ i j, ‖a i j‖ = 1)
    (F : Space Y E m → ℝ) (Z : Space Y E m) (hF : DifferentiableAt ℝ F Z) (c : ℝ)
    (hslice : ∀ y, F (replaceNumerical Z y) = mixture q w A b a v (replaceNumerical Z y)+c)
    (hg : ‖gradient F Z‖ ≤ 1) : ‖numerical Y E m (Inner.absoluteDepth+2) Z‖ ≤ numericalRadius := by
  let y := numerical Y E m (Inner.absoluteDepth+2) Z
  let B : Y →L[ℝ] Y := (q*(2*(m:ℝ))) • ContinuousLinearMap.id ℝ Y +
    ∑ i, w i • numericalMatrix (A i) Z
  let f := ∑ i, w i • numericalForce (b i) (a i) (v i) Z
  have hB : InverseGate.LowerBound B := LeafNumerical.convex_matrix_lower w q m hw hq hsum
    (by exact_mod_cast hm) _ (fun i => numericalMatrix_lower hm (A i) (hA i) (hAn i) Z)
  have hf : ‖f‖ ≤ Inner.innerConstant := LeafNumerical.convex_force_bound w hw
    (by linarith) _ Inner.innerConstant_pos.le (fun i => numericalForce_bound (b i) (a i) (v i) (hb i) (ha i) Z)
  have he : (q*(2*(m:ℝ))) • y + ∑ i, w i • (numericalMatrix (A i) Z y +
      numericalForce (b i) (a i) (v i) Z) = B y+f := by
    simp only [B, f, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_add, Finset.sum_add_distrib]
    abel
  have hd := (mixture_numerical_hasGradientAt hm q w A hsym b a v Z).hasFDerivAt.add_const c
  have hgrad : HasGradientAt (fun z => F (replaceNumerical Z z)) (B y+f) y := by
    rw [hasGradientAt_iff_hasFDerivAt, funext hslice]
    rw [← he]
    exact hd
  have hs := (numerical_slice_gradient_norm_le Z F hF).trans hg
  rw [hgrad.gradient] at hs
  have h := LeafNumerical.localization B hB y f hf hs
  unfold numericalRadius
  linarith

end GradientHessian.Leaf
