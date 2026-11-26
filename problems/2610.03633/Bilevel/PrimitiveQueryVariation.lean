import Bilevel.PrimitiveQueryFamily
import Bilevel.ChiPrimitiveObjective

/-! Enlarging the public Hessian-variation budget changes no objective,
oracle, seed, sample law, transcript, loss or original-call count. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
set_option autoImplicit false
variable {G : Geometry} {μ L ρ ρ' Δ R₀ σf σg : ℝ}

def Instance.enlargeVariation (I : Instance G μ L ρ Δ R₀ σf σg)
    (ρ' : ℝ) (hρ : ρ≤ρ') : Instance G μ L ρ' Δ R₀ σf σg where
  primitive := ChiPrimitive.enlargeVariation I.primitive ρ' hρ
  response := ChiPrimitive.enlargeVariationResponse I.primitive ρ' hρ I.response
  gap := ⟨I.gap.floor,I.gap.lower_bound,I.gap.gap⟩
  initialization := I.initialization
  Seed := I.Seed
  law := I.law
  upper := I.upper
  lower := I.lower
  upper_truth := I.upper_truth
  lower_truth := I.lower_truth

variable (I : Instance G μ L ρ Δ R₀ σf σg) (hρ : ρ≤ρ')

theorem Instance.enlargeVariation_reply : (I.enlargeVariation ρ' hρ).reply=I.reply := rfl
theorem Instance.enlargeVariation_loss : (I.enlargeVariation ρ' hρ).loss=I.loss := rfl
theorem Instance.enlargeVariation_cost (A : Algorithm G) :
    (I.enlargeVariation ρ' hρ).cost A=I.cost A := rfl
theorem Instance.enlargeVariation_risk (A : Algorithm G) :
    (I.enlargeVariation ρ' hρ).risk A=I.risk A := rfl
theorem Instance.enlargeVariation_conservative :
    (I.enlargeVariation ρ' hρ).IsConservative ↔ I.IsConservative := Iff.rfl
theorem Instance.enlargeVariation_curvature (Λ : ℝ) :
    (I.enlargeVariation ρ' hρ).CurvatureBound Λ ↔ I.CurvatureBound Λ := Iff.rfl

theorem Hardness.enlarge_variation {C : InstanceClass μ L ρ Δ R₀ σf σg}
    {C' : InstanceClass μ L ρ' Δ R₀ σf σg} {ε rate : ℝ}
    (H : Hardness C ε rate) (hρ : ρ≤ρ')
    (hC : ∀ G (I : Instance G μ L ρ Δ R₀ σf σg),C G I → C' G (I.enlargeVariation ρ' hρ)) :
    Hardness C' ε rate := by
  intro A hA
  have hA' : Accurate C ε A := by
    intro G I hI
    exact hA G (I.enlargeVariation ρ' hρ) (hC G I hI)
  obtain ⟨G,I,hI,hcost⟩ := H A hA'
  exact ⟨G,I.enlargeVariation ρ' hρ,hC G I hI,hcost⟩

theorem Hardness.enlargeVariation_conservative {ε rate : ℝ}
    (H : Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg)) ε rate) (hρ : ρ≤ρ') :
    Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=ρ') (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg)) ε rate :=
  H.enlarge_variation hρ (fun _ _ h => h)

theorem Hardness.enlargeVariation_curvature {ε rate Λ : ℝ}
    (H : Hardness (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε rate) (hρ : ρ≤ρ') :
    Hardness (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ') (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε rate :=
  H.enlarge_variation hρ (fun _ _ h => h)

theorem Hardness.enlargeVariation_conservativeCurvature {ε rate Λ : ℝ}
    (H : Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε rate) (hρ : ρ≤ρ') :
    Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ') (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε rate :=
  H.enlarge_variation hρ (fun _ _ h => h)

end Bilevel.PrimitiveQuery
