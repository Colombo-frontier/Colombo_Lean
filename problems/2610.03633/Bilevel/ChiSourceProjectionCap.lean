import Bilevel.ChiSourceGermWidths

/-! A concrete positive common energy cap for all finite source radii and
blind widths. Its size only changes the permissible ambient dimension. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtensionCalibration

def finiteProjectionCap {ι : Type*} [Fintype ι] (radius threshold : ι → ℝ) : ℝ :=
  (1/(1+∑ i : ι,radius i/threshold i))^2

theorem finiteProjectionCap_bounds {ι : Type*} [Fintype ι] (radius threshold : ι → ℝ)
    (hR : ∀ i,0≤radius i) (hT : ∀ i,0<threshold i) :
    0<finiteProjectionCap radius threshold ∧ finiteProjectionCap radius threshold≤1 ∧
      ∀ i,radius i*Real.sqrt (finiteProjectionCap radius threshold)≤threshold i := by
  classical
  let B : ℝ := 1+∑ i : ι,radius i/threshold i
  have hs : 0≤∑ i : ι,radius i/threshold i := Finset.sum_nonneg (fun i _ => div_nonneg (hR i) (hT i).le)
  have hB1 : 1≤B := by dsimp [B];linarith
  have hB : 0<B := lt_of_lt_of_le zero_lt_one hB1
  have hq : 0<1/B := div_pos zero_lt_one hB
  have hq1 : 1/B≤1 := (div_le_iff₀ hB).mpr (by simpa using hB1)
  change 0<(1/B)^2 ∧ (1/B)^2≤1 ∧ ∀ i,radius i*Real.sqrt ((1/B)^2)≤threshold i
  refine ⟨sq_pos_of_pos hq,by nlinarith,?_⟩
  intro i
  rw [Real.sqrt_sq hq.le]
  have hi : radius i/threshold i≤∑ j : ι,radius j/threshold j :=
    Finset.single_le_sum (fun j _ => div_nonneg (hR j) (hT j).le) (Finset.mem_univ i)
  have hiB : radius i/threshold i≤B := by dsimp [B];linarith
  have hr := (div_le_iff₀ (hT i)).mp hiB
  rw [mul_one_div]
  exact (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hr)

open ChiBoundedChain ChiRecursive ChiOuter
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def sourceProjectionRadius (M : Node E) (D : Geometry F) (J : ℕ) : Unit ⊕ (Fin (J+1) ⊕ Unit) → ℝ
  | Sum.inl _ => M.radius
  | Sum.inr (Sum.inl j) => (D j.val []).radius
  | Sum.inr (Sum.inr _) => (D J []).radius

def sourceProjectionThreshold (M : Node E) (D : Geometry F) (J : ℕ) (τ : ℝ) : Unit ⊕ (Fin (J+1) ⊕ Unit) → ℝ
  | Sum.inl _ => M.width/8
  | Sum.inr (Sum.inl j) => (D j.val []).width/8
  | Sum.inr (Sum.inr _) => τ/16

def sourceProjectionCap (M : Node E) (D : Geometry F) (J : ℕ) (τ : ℝ) : ℝ :=
  finiteProjectionCap (sourceProjectionRadius M D J) (sourceProjectionThreshold M D J τ)

theorem sourceProjectionCap_certificate (M : Node E) (D : Geometry F) (J : ℕ) (τ : ℝ)
    (hmR : 0≤M.radius) (hmw : 0<M.width)
    (hR : ∀ j,j≤J → 0≤(D j []).radius) (hw : ∀ j,j≤J → 0<(D j []).width) (hτ : 0<τ) :
    0<sourceProjectionCap M D J τ ∧ sourceProjectionCap M D J τ≤1 ∧
    M.radius*Real.sqrt (sourceProjectionCap M D J τ)≤M.width/8 ∧
    (∀ j,j≤J → (D j []).radius*Real.sqrt (sourceProjectionCap M D J τ)≤(D j []).width/8) ∧
    (D J []).radius*Real.sqrt (sourceProjectionCap M D J τ)≤τ/16 := by
  have h := finiteProjectionCap_bounds (sourceProjectionRadius M D J) (sourceProjectionThreshold M D J τ)
    (by rintro (_|(_|_));exact hmR;exact hR _ (by omega);exact hR J le_rfl)
    (by rintro (_|(_|_));exact div_pos hmw (by norm_num);exact div_pos (hw _ (by omega)) (by norm_num);exact div_pos hτ (by norm_num))
  exact ⟨h.1,h.2.1,h.2.2 (Sum.inl ()),fun j hj => h.2.2 (Sum.inr (Sum.inl ⟨j,by omega⟩)),
    h.2.2 (Sum.inr (Sum.inr ()))⟩

end Bilevel.ChiExtensionCalibration
