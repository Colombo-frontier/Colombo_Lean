import Bilevel.ChiOriginalBorelLower
import Bilevel.ChiOriginalBorelUpper
import Bilevel.ChiConservativeScalar

/-! Joint measurability of the literal conservative full-gradient pair.
The upper component retains the full scalar upper objective. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiConservative
variable {A W : Type*} [MeasurableSpace A]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem parametric_sampleGradient_measurable (g g₀ : A → W → ℝ)
    (hg : Measurable (fun p : A × W => gradient (g p.1) p.2))
    (hg₀ : Measurable (fun p : A × W => gradient (g₀ p.1) p.2)) (π : ℝ) :
    Measurable (fun p : (A × W) × Bool => sampleGradient (g p.1.1) (g₀ p.1.1) π p.2 p.1.2) := by
  have hzero := hg₀.comp (measurable_fst : Measurable (Prod.fst : (A × W) × Bool → A × W))
  have hone := hg.comp (measurable_fst : Measurable (Prod.fst : (A × W) × Bool → A × W))
  have hcoin : Measurable (fun p : (A × W) × Bool => if p.2 then π⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then π⁻¹ else (0:ℝ))).comp measurable_snd
  exact hzero.add (hcoin.smul (hone.sub hzero))

theorem parametric_fullPair_measurable (f g g₀ : A → W → ℝ)
    (hf : Measurable (fun p : A × W => gradient (f p.1) p.2))
    (hg : Measurable (fun p : A × W => gradient (g p.1) p.2))
    (hg₀ : Measurable (fun p : A × W => gradient (g₀ p.1) p.2)) (π : ℝ) :
    Measurable (fun p : (A × W) × Bool =>
      (gradient (f p.1.1) p.1.2,sampleGradient (g p.1.1) (g₀ p.1.1) π p.2 p.1.2)) :=
  (hf.comp measurable_fst).prodMk (parametric_sampleGradient_measurable g g₀ hg hg₀ π)

end Bilevel.ChiConservative
