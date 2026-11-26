import Bilevel.PrimitiveQueryFamily

/-! Increasing the public mean-curvature bound retains the identical
instance and all original-SFO executions. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
set_option autoImplicit false
variable {G : Geometry} {μ L ρ Δ R₀ σf σg Λ Λ' ε rate : ℝ}

theorem Instance.CurvatureBound.mono {I : Instance G μ L ρ Δ R₀ σf σg}
    (h : I.CurvatureBound Λ) (hΛ : Λ≤Λ') : I.CurvatureBound Λ' := by
  intro x y
  exact (h x y).trans (mul_le_mul_of_nonneg_right hΛ (norm_nonneg _))

theorem Hardness.enlargeCurvature
    (H : Hardness (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε rate) (hΛ : Λ≤Λ') :
    Hardness (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ') ε rate :=
  H.enlarge_class (fun _ _ h => h.mono hΛ)

theorem Hardness.enlargeConservativeCurvature
    (H : Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε rate) (hΛ : Λ≤Λ') :
    Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ') ε rate :=
  H.enlarge_class (fun _ _ h => ⟨h.1,h.2.mono hΛ⟩)

end Bilevel.PrimitiveQuery
