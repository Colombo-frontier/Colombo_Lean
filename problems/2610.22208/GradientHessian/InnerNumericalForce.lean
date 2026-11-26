import GradientHessian.InnerBounds

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem select_constant_ports_fderiv_bound (m : ℕ) (p : Fin m → ℝ) (e : Fin m → F → ℝ)
    (x : F) {C : ℝ} (hC : 0 ≤ C) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (he : ∀ i, ContDiff ℝ 1 (e i)) (hD : ∀ i, ‖fderiv ℝ (e i) x‖ ≤ C) :
    ‖fderiv ℝ (fun y => InnerSelector.select m p (fun i => e i y)) x‖ ≤ C := by
  induction m with
  | zero => simpa [InnerSelector.select] using hC
  | succ m ih =>
    let T := fun y => InnerSelector.select m (fun i => p i.succ) (fun i => e i.succ y)
    have hT : ContDiff ℝ 1 T :=
      InnerSelector.select_contDiff m _ _ (fun _ => contDiff_const) (fun i => he i.succ)
    have hDT := ih (fun i => p i.succ) (fun i => e i.succ) (fun i => hp i.succ)
      (fun i => he i.succ) (fun i => hD i.succ)
    change ‖fderiv ℝ T x‖ ≤ C at hDT
    have hd := ((((he 0).differentiable (by norm_num) x).hasFDerivAt.const_mul (1 - p 0)).add
      (((hT.differentiable (by norm_num) x).hasFDerivAt).const_mul (p 0))).fderiv
    change fderiv ℝ (fun y => InnerSelector.select (m + 1) p (fun i => e i y)) x = _ at hd
    rw [hd]
    calc
      ‖(1 - p 0) • fderiv ℝ (e 0) x + p 0 • fderiv ℝ T x‖ ≤
          ‖(1 - p 0) • fderiv ℝ (e 0) x‖ + ‖p 0 • fderiv ℝ T x‖ := norm_add_le _ _
      _ = (1 - p 0) * ‖fderiv ℝ (e 0) x‖ + p 0 * ‖fderiv ℝ T x‖ := by
        rw [norm_smul (1 - p 0) (fderiv ℝ (e 0) x),
          norm_smul (p 0) (fderiv ℝ T x), Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr (hp 0).2), abs_of_nonneg (hp 0).1]
      _ ≤ (1 - p 0) * C + p 0 * C := add_le_add
        (mul_le_mul_of_nonneg_left (hD 0) (sub_nonneg.mpr (hp 0).2))
        (mul_le_mul_of_nonneg_left hDT (hp 0).1)
      _ = C := by ring

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def numericalForceBound : ℝ := InverseGate.H₀ + 56 * (12 / InverseGate.alpha)

theorem numericalForceBound_pos : 0 < numericalForceBound := by
  norm_num [numericalForceBound, InverseGate.H₀, InverseGate.alpha]

theorem numericalPayload_contDiff (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) :
    ContDiff ℝ 3 (fun y => payload b a v (replaceNumerical Z y) i) :=
  (payload_contDiff b a v i).comp
    (contDiff_const.add ((insertNumerical Y E m (k + 2)).contDiff.comp
      (contDiff_id.sub contDiff_const)))

theorem residual_numerical_slice (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (y : Y) :
    residual b a v (replaceNumerical Z y) = selfSum v Z - publicQuadratic m k Z -
      InnerSelector.select m (ports v Z) (fun i => payload b a v (replaceNumerical Z y) i) := by
  have hports : ports v (replaceNumerical Z y) = ports v Z := by funext i; simp [ports]
  simp only [residual, selfSum, publicQuadratic, forcingSum, tasks_replaceNumerical, hports]

variable [CompleteSpace Y]

theorem numericalPayload_fderiv_bound (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) (hb : ‖b i‖ = InverseGate.H₀) (ha : ‖a i‖ = 1) (y : Y) :
    ‖fderiv ℝ (fun z => payload b a v (replaceNumerical Z z) i) y‖ ≤ numericalForceBound := by
  let B := input (v i) (tasks Y E m (k + 2) Z i)
  have hB : B ∈ Set.Icc (0 : ℝ) 56 := input_bounds _ _
  have hU := (InverseGate.forcing_hasGradientAt (b i) y).differentiableAt.hasFDerivAt
  have hc := ((InverseGate.gate_contDiff (a i)).differentiable (by norm_num) y).hasFDerivAt
  have hd := (hU.add (hc.const_mul B)).fderiv
  have he : (fun z => payload b a v (replaceNumerical Z z) i) =
      (fun z => InverseGate.forcing (b i) z + B * InverseGate.gate (a i) z) := by
    funext z
    simp [payload, B]
  rw [he, hd]
  have hu : ‖fderiv ℝ (InverseGate.forcing (b i)) y‖ ≤ InverseGate.H₀ := by
    have h := InverseGate.forcing_gradient_norm_le (b i) y
    simpa [gradient, hb] using h
  have hc' : ‖fderiv ℝ (InverseGate.gate (a i)) y‖ ≤ 12 / InverseGate.alpha := by
    have h := InverseGate.gate_gradient_norm_le (a i) y ha
    simpa [gradient] using h
  have hmul := mul_le_mul hB.2 hc' (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 56)
  have hnorm := norm_add_le (fderiv ℝ (InverseGate.forcing (b i)) y)
    (B • fderiv ℝ (InverseGate.gate (a i)) y)
  rw [norm_smul B (fderiv ℝ (InverseGate.gate (a i)) y), Real.norm_eq_abs,
    abs_of_nonneg hB.1] at hnorm
  exact hnorm.trans (add_le_add hu hmul)

/-- The source's shared numerical force bound, even though all payloads use
the same numerical coordinate. -/
theorem residual_numerical_gradient_bound (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1)
    (Z : Space Y E m (k + 2)) :
    ‖gradient (fun y => residual b a v (replaceNumerical Z y)) (numerical Y E m (k + 2) Z)‖ ≤
      numericalForceBound := by
  let e := fun i y => payload b a v (replaceNumerical Z y) i
  have he (i : Fin m) : ContDiff ℝ 1 (e i) :=
    (numericalPayload_contDiff b a v Z i).of_le (by norm_num)
  have h := select_constant_ports_fderiv_bound m (ports v Z) e (numerical Y E m (k + 2) Z)
    numericalForceBound_pos.le (ports_bounds v Z) he
    (fun i => numericalPayload_fderiv_bound b a v Z i (hb i) (ha i) _)
  have hcd := InnerSelector.select_contDiff m (fun i _ => ports v Z i) e
    (fun _ => contDiff_const) he
  have hd := ((hasFDerivAt_const (selfSum v Z - publicQuadratic m k Z)
    (numerical Y E m (k + 2) Z)).sub
      ((hcd.differentiable (by norm_num) _).hasFDerivAt)).fderiv
  simp only [zero_sub] at hd
  rw [funext (residual_numerical_slice b a v Z)]
  simp only [gradient, LinearIsometryEquiv.norm_map]
  rw [hd, norm_neg]
  exact h

end GradientHessian.Inner
