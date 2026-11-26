import Bilevel.PartialLegendreHybridTrace

/-! Concrete correction `H₀-mI`, including positive semidefiniteness,
normal annihilation and the unchanged physical tangential response. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiHybrid
open PrimitiveGeometry
variable {X Y U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def correction (H : Y →L[ℝ] Y) (m : ℝ) : Y →L[ℝ] Y := H-m • ContinuousLinearMap.id ℝ Y

theorem correction_apply (H : Y →L[ℝ] Y) (m : ℝ) (y : Y) : correction H m y=H y-m • y := rfl

theorem correction_symmetric (H : Y →L[ℝ] Y) (m : ℝ)
    (hsym : ∀ u v,⟪H u,v⟫=⟪u,H v⟫) (u v : Y) :
    ⟪correction H m u,v⟫=⟪u,correction H m v⟫ := by
  simp only [correction_apply,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hsym]

theorem correction_positive (H : Y →L[ℝ] Y) (m : ℝ)
    (hcoerce : ∀ y,m*‖y‖^2≤⟪y,H y⟫) (y : Y) : 0≤⟪y,correction H m y⟫ := by
  rw [correction_apply,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  exact sub_nonneg.mpr (hcoerce y)

theorem correction_norm_bound (H : Y →L[ℝ] Y) {m : ℝ} (hm : 0≤m) : ‖correction H m‖≤‖H‖+m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) hm)
  intro y
  rw [correction_apply]
  apply (norm_sub_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
  have hh := H.le_opNorm y
  nlinarith only [hh]

theorem correction_kills_normal (H : Joint U V →L[ℝ] Joint U V) (m : ℝ)
    (hH : ∀ v : V,H (pack (0:U) v)=m • pack (0:U) v) (v : V) :
    correction H m (pack (0:U) v)=0 := by rw [correction_apply,hH,sub_self]

theorem correction_response_equation (H : Joint U V →L[ℝ] Joint U V) (m : ℝ)
    (C : X →L[ℝ] Joint U V) (tangent : X → U)
    (hlinear : ∀ x,H (pack (tangent x) (0:V))=C x) (x : X) :
    m • pack (tangent x) (0:V)+correction H m (pack (tangent x) (0:V))=C x := by
  rw [correction_apply,← hlinear x]
  abel

theorem correction_transport_smooth_budget (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    {μ L : ℝ} (hμ : 0<μ) (hκ : 9*μ≤L) (hH : ‖H‖≤L/4) (hC : ‖C‖≤L/4) :
    2*(3*μ/2)+‖correction H (3*μ/2)‖+‖C‖≤L := by
  have hh := correction_norm_bound H (show 0≤3*μ/2 by positivity)
  linarith only [hh,hH,hC,hκ]

end Bilevel.ChiHybrid
