import NCConcave16991.BranchConstructionValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Actual endpoint gradients and scalar source projections -/

namespace NCConcave16991.BranchConstruction

noncomputable section

open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

theorem symmetric_quadratic_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : E →L[ℝ] E) (hD : ∀ x y, ⟪x, D y⟫_ℝ = ⟪D x, y⟫_ℝ) (x : E) :
    HasFDerivAt (fun z ↦ ⟪z, D z⟫_ℝ) ((2 : ℝ) • innerSL ℝ (D x)) x := by
  have hh := (hasFDerivAt_id (𝕜 := ℝ) x).inner ℝ D.hasFDerivAt
  refine hh.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.id_apply, id_eq, smul_apply, innerSL_apply_apply]
  change ⟪x, D h⟫_ℝ + ⟪h, D x⟫_ℝ = 2 * ⟪D x, h⟫_ℝ
  rw [hD x h]
  have hc : ⟪h, D x⟫_ℝ = ⟪D x, h⟫_ℝ := real_inner_comm _ _
  rw [hc]
  ring

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {m : ℕ} (V : Fin ((m + 1) + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)] [∀ j, FiniteDimensional ℝ (V j)]
  (B : ∀ t : Fin (m + 1), BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

theorem terminalCorrection_symmetric (x y : V (Fin.last (m + 1))) :
    ⟪x, terminalCorrection V B y⟫_ℝ = ⟪terminalCorrection V B x, y⟫_ℝ := by
  simp only [terminalCorrection, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [terminalGreenOperator_symmetric]

theorem portValue_hasGradientAt_left (a : V 0) (b : V (Fin.last (m + 1))) :
    HasGradientAt (fun x ↦ portValue V B x b)
      ((2 : ℝ) • a - (terminalTransport V B).toContinuousLinearMap.adjoint b) a := by
  let P := (terminalTransport V B).toContinuousLinearMap
  have hlin := ((innerSL ℝ b).comp P).hasFDerivAt (x := a)
  have hn := symmetric_quadratic_hasFDerivAt (ContinuousLinearMap.id ℝ (V 0)) (fun _ _ ↦ rfl) a
  have hh := (hn.sub hlin).add_const ⟪b, terminalCorrection V B b⟫_ℝ
  have he : (fun x ↦ portValue V B x b) =
      fun x ↦ ‖x‖ ^ 2 - ⟪b, P x⟫_ℝ + ⟪b, terminalCorrection V B b⟫_ℝ := by
    funext x
    exact portValue_formula V B x b
  rw [he, hasGradientAt_iff_hasFDerivAt]
  have hd : InnerProductSpace.toDual ℝ (V 0) ((2 : ℝ) • a - P.adjoint b) =
      (2 : ℝ) • innerSL ℝ a - (innerSL ℝ b).comp P := by
    ext h
    change ⟪(2 : ℝ) • a - P.adjoint b, h⟫_ℝ = 2 * ⟪a, h⟫_ℝ - ⟪b, P h⟫_ℝ
    rw [inner_sub_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  rw [hd]
  convert hh using 1 <;> first
    | rfl
    | (funext x
       simp only [Pi.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
         ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq])

theorem portValue_hasGradientAt_right (a : V 0) (b : V (Fin.last (m + 1))) :
    HasGradientAt (fun y ↦ portValue V B a y)
      ((2 : ℝ) • terminalCorrection V B b - terminalTransport V B a) b := by
  let D := terminalCorrection V B
  let p := terminalTransport V B a
  have hlin : HasFDerivAt (fun y ↦ ⟪y, p⟫_ℝ) (innerSL ℝ p) b := by
    convert (innerSL ℝ p).hasFDerivAt (x := b) using 1
    funext y
    exact real_inner_comm _ _
  have hq := symmetric_quadratic_hasFDerivAt D (terminalCorrection_symmetric V B) b
  have hh := (hq.sub hlin).const_add (‖a‖ ^ 2)
  have he : (fun y ↦ portValue V B a y) = fun y ↦ ‖a‖ ^ 2 + (⟪y, D y⟫_ℝ - ⟪y, p⟫_ℝ) := by
    funext y
    rw [portValue_formula]
    dsimp [D, p]
    ring
  rw [he, hasGradientAt_iff_hasFDerivAt]
  have hd : InnerProductSpace.toDual ℝ (V (Fin.last (m + 1))) ((2 : ℝ) • D b - p) =
      (2 : ℝ) • innerSL ℝ (D b) - innerSL ℝ p := by
    ext h
    change ⟪(2 : ℝ) • D b - p, h⟫_ℝ = 2 * ⟪D b, h⟫_ℝ - ⟪p, h⟫_ℝ
    rw [inner_sub_left, real_inner_smul_left]
  rw [hd]
  exact hh

theorem portValue_left_source_projection (a u : V 0) (b : V (Fin.last (m + 1))) :
    ⟪gradient (fun x ↦ portValue V B x b) a, u⟫_ℝ =
      2 * ⟪a, u⟫_ℝ - ⟪b, terminalTransport V B u⟫_ℝ := by
  rw [(portValue_hasGradientAt_left V B a b).gradient, inner_sub_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem portValue_right_source_projection (a u : V 0) (b : V (Fin.last (m + 1))) :
    ⟪gradient (fun y ↦ portValue V B a y) b, terminalTransport V B u⟫_ℝ =
      2 * ⟪b, terminalTransport V B u⟫_ℝ - ⟪a, u⟫_ℝ := by
  rw [(portValue_hasGradientAt_right V B a b).gradient, inner_sub_left, real_inner_smul_left,
    ← terminalCorrection_symmetric, terminalCorrection_on_transport, (terminalTransport V B).inner_map_map]

end

end NCConcave16991.BranchConstruction
