import Bilevel.ChiRecursiveSourceGeometry
import Bilevel.ChiCurvatureFloors

/-! The actual recursive `parentScale` with the source's nonuniform
curvature ratios, including the unamplified middle level r_0=1. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiRecursive ChiCurvatureSchedule

def sourceRatio (T : ℝ) : ℕ → ℝ
  | 0 => 1
  | j+1 => curvature T (j+1)/curvature T j

theorem sourceRatio_ge_one {T : ℝ} (hT : 1 ≤ T) (j : ℕ) : 1 ≤ sourceRatio T j := by
  cases j with
  | zero => rfl
  | succ j => exact curvature_ratio_ge_one hT j

theorem sourceRatio_le {T : ℝ} (hT : 1 ≤ T) (j : ℕ) : sourceRatio T j ≤ T := by
  cases j with
  | zero => exact hT
  | succ j =>
    have ha := curvature_bounds hT j
    have hb := curvature_bounds hT (j+1)
    apply (div_le_iff₀ (curvature_pos (by linarith) j)).mpr
    nlinarith [mul_le_mul_of_nonneg_left ha.1 (show 0 ≤ T by linarith)]

theorem source_parent_curvature (initial : Scale) {T : ℝ} (hT : 0 < T)
    (η K : ℝ) (j : ℕ) :
    (parentScale initial (sourceRatio T) (resolution η K) (j+1)).curvature =
      initial.curvature*curvature T j := by
  induction j with
  | zero => simp [parentScale,nextScale,sourceRatio,curvature_zero]
  | succ j ih =>
    change (curvature T (j+1)/curvature T j)*
      (parentScale initial (sourceRatio T) (resolution η K) (j+1)).curvature = _
    rw [ih]
    have ha := (curvature_pos hT j).ne'
    field_simp
    ring

theorem source_parent_width (initial : Scale) {T : ℝ} (hT : 1 ≤ T)
    (hl : 0 < initial.curvature) (η K : ℝ) (j : ℕ) :
    (parentScale initial (sourceRatio T) (resolution η K) (j+1)).width =
      η^j*initial.width/(K*curvature T j) := by
  have ha := source_parent_curvature initial (by linarith : 0 < T) η K j
  have hf := source_force_formula initial (sourceRatio T) (sourceRatio_ge_one hT) η K j
  unfold Scale.force at hf
  rw [ha] at hf
  have hc := (curvature_pos (by linarith : 0 < T) j).ne'
  apply (mul_left_cancel₀ (mul_ne_zero hl.ne' hc))
  calc
    _ = η^j*(initial.curvature*initial.width/K) := hf
    _ = _ := by
      by_cases hK : K = 0
      · simp [hK]
      · field_simp [hc,hK]
        ring

theorem source_high_node_curvature (initial : Scale) {T : ℝ} (hT : 0 < T)
    (η K : ℝ) (j : ℕ) :
    sourceRatio T (j+1)*(parentScale initial (sourceRatio T) (resolution η K) (j+1)).curvature =
      initial.curvature*curvature T (j+1) := by
  rw [source_parent_curvature initial hT]
  change (curvature T (j+1)/curvature T j)*(initial.curvature*curvature T j) = _
  have ha := (curvature_pos hT j).ne'
  field_simp
  ring

theorem source_high_length (cn η T : ℝ) (K : ℝ) (j : ℕ) :
    Nat.floor (cn*sourceRatio T (j+1)/(resolution η K (j+1))^2) = length cn η T j := by
  simp only [sourceRatio,resolution,if_neg (Nat.succ_ne_zero _),length]

theorem parent_force_ratio_bound (initial : Scale) {T η K κ : ℝ}
    (hT : 1 ≤ T) (hTκ : T ≤ κ) (hκ : 1 ≤ κ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hl : 0 ≤ initial.curvature) (hh : 0 ≤ initial.width) (hK : K = κ/6) (j : ℕ) :
    (parentScale initial (sourceRatio T) (resolution η K) (j+1)).force*
      Real.sqrt (sourceRatio T (j+1)) ≤ 6*initial.force := by
  have hg : 0 ≤ initial.force := mul_nonneg hl hh
  have hκp : 0 < κ := by linarith
  have hr0 : 0 ≤ sourceRatio T (j+1) := le_trans zero_le_one (sourceRatio_ge_one hT _)
  have hs : Real.sqrt (sourceRatio T (j+1)) ≤ κ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith,?_⟩
    have hr := (sourceRatio_le hT (j+1)).trans hTκ
    nlinarith [sq_nonneg (κ-1)]
  rw [source_force_formula initial (sourceRatio T) (sourceRatio_ge_one hT),hK]
  have hp := pow_le_one₀ hη hη1 (n:=j)
  have hb := mul_le_mul hp hs (Real.sqrt_nonneg _) zero_le_one
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ initial.force/(κ/6) by positivity)
  convert hm using 1 <;> field_simp <;> ring

end Bilevel.ChiExtensionCalibration
