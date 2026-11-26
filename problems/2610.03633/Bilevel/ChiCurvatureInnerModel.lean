import Bilevel.MultiscaleQueryFamily
import Bilevel.ChiCurvatureFamily

/-! Macro-free branch embedded into the same original full-query model. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Bilevel.ChiCurvatureLower
open PrimitiveQuery PrimitiveGeometry MultiscaleMean CompensatedMean

theorem innerFamily_hardness {μ L ρ Δ C κ ε σg cost R₀ σf : ℝ}
    (hR₀ : 0≤R₀) (h : InnerFamily.{0,0} μ L ρ Δ C κ ε σg cost) :
    Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) (C*L*κ^2)) ε cost := by
  obtain ⟨n,dim,P,hD,hs,hRate,hP⟩ := h
  letI : MeasurableSpace (LowerSpace (EuclideanGaussian.Space dim)) := borel _
  letI : BorelSpace (LowerSpace (EuclideanGaussian.Space dim)) := ⟨rfl⟩
  letI : MeasurableSpace (Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim))) := borel _
  letI : BorelSpace (Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim))) := ⟨rfl⟩
  obtain ⟨F,hF,hcurv,hcons⟩ := inner_model_family P hD (σf:=σf) hR₀ hs hRate hP
  exact F.hardness _ ε cost (fun a => ⟨hcons a,hcurv a⟩) hF

end Bilevel.ChiCurvatureLower
