import FreshGradientMinimax.PathEnergyFormula
import FreshGradientMinimax.FlatLocality
import FreshGradientMinimax.CoordinateMask

/-! A single signed central incidence row represents exactly the already
constructed hard energy. After its predecessor is masked, the whole truncated
operator, and hence the auxiliary reply, is independent of the sign. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def centralPathSigns {n : ℕ} (k : ℕ) (s : ℝ) (i : Fin n) : ℝ :=
  if i.val = k then s else 1

theorem centralPathSigns_sq {n : ℕ} (k : ℕ) {s : ℝ} (hs : s ^ 2 = 1) (i : Fin n) :
    centralPathSigns k s i ^ 2 = 1 := by
  unfold centralPathSigns
  split_ifs
  · exact hs
  · norm_num

theorem centralPathSigns_abs {n : ℕ} (k : ℕ) {s : ℝ} (hs : s ^ 2 = 1) (i : Fin n) :
    |centralPathSigns k s i| ≤ 1 := by
  have h := centralPathSigns_sq k hs i
  nlinarith [sq_abs (centralPathSigns k s i), abs_nonneg (centralPathSigns k s i)]

theorem flatPathEnergy_gauge_central {n : ℕ} (k : ℕ) {s δ : ℝ}
    (hs : s ^ 2 = 1) (hδ : 0 ≤ δ) (x : Euclid (n + 1)) :
    flatEnergy δ (pathIncidence (pathSignsFromVertices (tailVertexSigns k s)) x) =
      flatEnergy δ (pathIncidence (centralPathSigns k s) x) := by
  rw [flatPathEnergy_formula (pathSignsFromVertices_sq (tailVertexSigns_sq k hs)) hδ,
    flatPathEnergy_formula (centralPathSigns_sq k hs) hδ]
  simp only [tailPath_internal_sign k hs, centralPathSigns, Fin.val_succ, Fin.coe_castSucc]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem linearFlatEnergy_gauge_central {n : ℕ} (C : E →L[ℝ] Euclid (n + 1))
    (k : ℕ) {s δ : ℝ} (hs : s ^ 2 = 1) (hδ : 0 ≤ δ) (β : ℝ) :
    linearFlatEnergy ((pathIncidence (pathSignsFromVertices (tailVertexSigns k s))).comp C) β δ =
      linearFlatEnergy ((pathIncidence (centralPathSigns k s)).comp C) β δ := by
  funext x
  unfold linearFlatEnergy
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    flatPathEnergy_gauge_central k hs hδ]

theorem linearFlatGradient_gauge_central {n : ℕ} (C : E →L[ℝ] Euclid (n + 1))
    (k : ℕ) {s δ : ℝ} (hs : s ^ 2 = 1) (hδ : 0 ≤ δ) (β : ℝ) :
    linearFlatGradient ((pathIncidence (pathSignsFromVertices (tailVertexSigns k s))).comp C) β δ =
      linearFlatGradient ((pathIncidence (centralPathSigns k s)).comp C) β δ := by
  funext x
  rw [← linearFlatEnergy_gradient _ β hδ, ← linearFlatEnergy_gradient _ β hδ,
    linearFlatEnergy_gauge_central C k hs hδ β]

omit [CompleteSpace E] in
theorem centralPath_mask_sign_independent {n : ℕ} (C : E →L[ℝ] Euclid n)
    (S : Finset (Fin n)) (k : ℕ) (s : ℝ)
    (hhid : ∀ i : Fin n, i.val + 1 = k → i ∉ S) :
    (pathIncidence (centralPathSigns k s)).comp ((coordinateMask S).comp C) =
      (pathIncidence (fun _ => 1)).comp ((coordinateMask S).comp C) := by
  apply ContinuousLinearMap.ext
  intro x
  ext e
  simp only [ContinuousLinearMap.comp_apply, pathIncidence_apply, one_mul]
  congr 1
  refine Fin.cases ?_ (fun i => ?_) e
  · simp only [Fin.cons_zero, mul_zero]
  · rw [Fin.cons_succ]
    unfold centralPathSigns
    simp only [Fin.val_succ]
    split_ifs with hi
    · simp only [coordinateMask_apply, if_neg (hhid i hi), mul_zero]
    · rw [one_mul]

omit [CompleteSpace E] in
theorem centralPath_bands_sign_independent {N t : ℕ} (ht : t ≤ N)
    (C : E →L[ℝ] Euclid (4 * N + 4)) (s : ℝ) :
    (pathIncidence (centralPathSigns (2 * N + 2) s)).comp
        ((coordinateMask (pathVisible (4 * N + 4) (t + 1))).comp C) =
      (pathIncidence (fun _ => 1)).comp
        ((coordinateMask (pathVisible (4 * N + 4) (t + 1))).comp C) := by
  apply centralPath_mask_sign_independent
  intro i hi
  simp only [mem_pathVisible]
  omega

end FreshGradientMinimax

