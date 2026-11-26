import Bilevel.PrimitiveQueryFamily

/-! Larger declared noise budgets retain the identical sample functions,
seed law, paired observation, objective and expected execution cost. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.FreshOracle.Oracle
open MeasureTheory
variable {Q Seed E : Type*} [MeasurableSpace Q] [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure Seed} {σ : ℝ}

def enlargeVariance (O : Oracle (Query:=Q) (E:=E) ν σ) (σ' : ℝ) (hσ : σ^2≤σ'^2) :
    Oracle (Query:=Q) (E:=E) ν σ' :=
  { O with variance := fun q => (O.variance q).trans hσ }

end Bilevel.FreshOracle.Oracle

namespace Bilevel.PrimitiveQuery
variable {G : Geometry} {μ L ρ Δ R₀ σf σg σf' σg' : ℝ}

def Instance.enlargeNoise (I : Instance G μ L ρ Δ R₀ σf σg)
    (σf' σg' : ℝ) (hf : σf^2≤σf'^2) (hg : σg^2≤σg'^2) : Instance G μ L ρ Δ R₀ σf' σg' where
  primitive := I.primitive
  response := I.response
  gap := I.gap
  initialization := I.initialization
  Seed := I.Seed
  law := I.law
  upper := I.upper.enlargeVariance σf' hf
  lower := I.lower.enlargeVariance σg' hg
  upper_truth := I.upper_truth
  lower_truth := I.lower_truth

variable (I : Instance G μ L ρ Δ R₀ σf σg) (hf : σf^2≤σf'^2) (hg : σg^2≤σg'^2)

theorem Instance.enlargeNoise_reply : (I.enlargeNoise σf' σg' hf hg).reply=I.reply := rfl
theorem Instance.enlargeNoise_loss : (I.enlargeNoise σf' σg' hf hg).loss=I.loss := rfl
theorem Instance.enlargeNoise_cost (A : Algorithm G) :
    (I.enlargeNoise σf' σg' hf hg).cost A=I.cost A := rfl
theorem Instance.enlargeNoise_risk (A : Algorithm G) :
    (I.enlargeNoise σf' σg' hf hg).risk A=I.risk A := rfl
theorem Instance.enlargeNoise_conservative :
    (I.enlargeNoise σf' σg' hf hg).IsConservative ↔ I.IsConservative := Iff.rfl
theorem Instance.enlargeNoise_curvature (Λ : ℝ) :
    (I.enlargeNoise σf' σg' hf hg).CurvatureBound Λ ↔ I.CurvatureBound Λ := Iff.rfl

theorem Hardness.enlarge_noise {C : InstanceClass μ L ρ Δ R₀ σf σg}
    {C' : InstanceClass μ L ρ Δ R₀ σf' σg'} {ε rate : ℝ}
    (H : Hardness C ε rate) (hf : σf^2≤σf'^2) (hg : σg^2≤σg'^2)
    (hC : ∀ G (I : Instance G μ L ρ Δ R₀ σf σg),C G I → C' G (I.enlargeNoise σf' σg' hf hg)) :
    Hardness C' ε rate := by
  intro A hA
  have hA' : Accurate C ε A := by
    intro G I hI
    exact hA G (I.enlargeNoise σf' σg' hf hg) (hC G I hI)
  obtain ⟨G,I,hI,hcost⟩ := H A hA'
  exact ⟨G,I.enlargeNoise σf' σg' hf hg,hC G I hI,hcost⟩

theorem Hardness.enlargeNoise_conservative {ε rate : ℝ}
    (H : Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg)) ε rate)
    (hf : σf^2≤σf'^2) (hg : σg^2≤σg'^2) :
    Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf') (σg:=σg')) ε rate :=
  H.enlarge_noise hf hg (fun _ _ h => h)

theorem Hardness.enlargeNoise_curvature {ε rate Λ : ℝ}
    (H : Hardness (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε rate)
    (hf : σf^2≤σf'^2) (hg : σg^2≤σg'^2) :
    Hardness (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf') (σg:=σg') Λ) ε rate :=
  H.enlarge_noise hf hg (fun _ _ h => h)

theorem Hardness.enlargeNoise_conservativeCurvature {ε rate Λ : ℝ}
    (H : Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε rate)
    (hf : σf^2≤σf'^2) (hg : σg^2≤σg'^2) :
    Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf') (σg:=σg') Λ) ε rate :=
  H.enlarge_noise hf hg (fun _ _ h => h)

end Bilevel.PrimitiveQuery
