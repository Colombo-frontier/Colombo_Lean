import Bilevel.NearIdentityRadialCoefficient
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The rank-plus-two hypothesis in ni:lem:radial constructs the unit
transverse direction. It is not an additional assumed witness. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.NearIdentityConfinement
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_unit_transverse (U : F →L[ℝ] E) (p : E)
    (hdim : finrank ℝ (LinearMap.range U.toLinearMap)+2≤finrank ℝ E) :
    ∃ e : E,‖e‖=1 ∧ (∀ w,⟪e,U w⟫=0) ∧ ⟪e,p⟫=0 := by
  let V := LinearMap.range U.toLinearMap
  let P := Submodule.span ℝ ({p}:Set E)
  let W := V ⊔ P
  have hpdim : finrank ℝ P≤1 := by
    simpa only [P,Set.toFinset_singleton,Finset.card_singleton] using
      (finrank_span_le_card (R:=ℝ) ({p}:Set E))
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V P
  have hW : finrank ℝ W≤finrank ℝ V+1 := by
    dsimp only [W]
    omega
  have horth := W.finrank_add_finrank_orthogonal
  have hpos : 0<finrank ℝ Wᗮ := by
    change finrank ℝ V+2≤finrank ℝ E at hdim
    omega
  letI : Nontrivial Wᗮ := nontrivial_of_finrank_pos hpos
  obtain ⟨x,hx⟩ := exists_ne (0:Wᗮ)
  have hx0 : (x:E)≠0 := by
    intro h
    exact hx (Subtype.ext h)
  let e : E := ‖(x:E)‖⁻¹ • (x:E)
  have he : ‖e‖=1 := by simpa only [e] using norm_smul_inv_norm hx0
  have hem : e∈Wᗮ := W.orthogonal.smul_mem _ x.property
  have heinner := (W.mem_orthogonal' e).mp hem
  refine ⟨e,he,fun w => heinner (U w) (Submodule.mem_sup_left ?_),
    heinner p (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton p)))⟩
  exact ⟨w,rfl⟩

theorem source_total_radial_coefficient_bound
    (G : E → E) (U : F →L[ℝ] E) (a : E → F) (γ : E → ℝ) (p : E)
    (DG : E →L[ℝ] E) (Dγ : E →L[ℝ] ℝ)
    (hDG : HasFDerivAt G DG p) (hDγ : HasFDerivAt γ Dγ p)
    (hdecomp : ∀ x,G x=U (a x)+γ x • x)
    (hdim : finrank ℝ (LinearMap.range U.toLinearMap)+2≤finrank ℝ E)
    {δ : ℝ} (hbound : ‖DG‖≤δ) : |γ p|≤δ := by
  obtain ⟨e,he,heU,hep⟩ := exists_unit_transverse U p hdim
  exact total_radial_coefficient_bound G U a γ p e DG Dγ hDG hDγ hdecomp heU hep he hbound

end Bilevel.NearIdentityConfinement
