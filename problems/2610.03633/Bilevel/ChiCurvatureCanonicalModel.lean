import Bilevel.ChiCanonicalQueryFamily
import Bilevel.ChiCurvatureFamily

/-! The verified canonical all-gap branch is a hard family in the actual
conservative curvature-constrained original-SFO minimax model. -/
noncomputable section
namespace Bilevel.ChiCurvatureLower
open PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem canonicalFamily_hardness {μ L ρ Δ C κ ε σg cost R₀ σf : ℝ}
    (hR₀ : 0≤R₀) (h : CanonicalFamily.{0,0} μ L ρ Δ C κ ε σg cost) :
    Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) (C*L*κ^2)) ε cost := by
  classical
  obtain ⟨n,dim,cn,rat,res,hd,hAll,sc,w,ζ,CR,Km,v,rad,R,K,B,hB,H,hRate,hP⟩ := h
  choose P r hz hgap hm hcurv hfull using hP
  obtain ⟨F,hF,hcons,hmean⟩ := H.query_family μ ρ Δ R₀ σf σg B cost hR₀ hB P r hgap hz hm hfull hRate
  apply F.hardness _ ε cost _ hF
  intro a
  refine ⟨hcons a,?_⟩
  intro x x'
  change ‖gradient ((F.primitive a).hyperobjective (F.response a)) x-
    gradient ((F.primitive a).hyperobjective (F.response a)) x'‖≤(C*L*κ^2)*‖x-x'‖
  rw [funext (hmean a)]
  exact hcurv a x x'

end Bilevel.ChiCurvatureLower
