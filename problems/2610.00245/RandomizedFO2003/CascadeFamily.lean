import RandomizedFO2003.CascadeFunction
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

namespace RandomizedFO2003.Cascade

open Primitives MeasureTheory
open scoped BigOperators

variable (N : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Only the operator and vector coefficients vary. All scalar scales are
fixed before sampling the parameters. This product has its ordinary Borel
structure, including at zero or degenerate coefficient vectors. -/
abbrev Coefficients := (Fin (N + 1) → E →L[ℝ] E) ×
  (Fin (N + 1) → E) × (Fin (N + 1) → E)

noncomputable def coefficientsData (p : Coefficients N E) (B α D C₀ K : ℝ) : Data N E where
  A := p.1
  a := p.2.1
  b := p.2.2
  B := B
  α := α
  D := D
  C₀ := C₀
  K := K

variable {N E}

/-- Joint continuity in arbitrary coefficient arrays and the actual block
point, not merely separate continuity for each realized function. -/
theorem coefficients_energy_continuous (B α D C₀ K : ℝ) :
    Continuous (fun p : Coefficients N E × BlockProduct (N + 1) E =>
      (coefficientsData N E p.1 B α D C₀ K).energy p.2) := by
  have hx (i : Fin (N + 1)) : Continuous
      (fun p : Coefficients N E × BlockProduct (N + 1) E => p.2 i) :=
    (blockProjection (E := E) (N + 1) i).continuous.comp continuous_snd
  have hA (i : Fin (N + 1)) : Continuous
      (fun p : Coefficients N E × BlockProduct (N + 1) E => p.1.1 i) :=
    (continuous_apply i).comp continuous_fst.fst
  have ha (i : Fin (N + 1)) : Continuous
      (fun p : Coefficients N E × BlockProduct (N + 1) E => p.1.2.1 i) :=
    (continuous_apply i).comp continuous_fst.snd.fst
  have hb (i : Fin (N + 1)) : Continuous
      (fun p : Coefficients N E × BlockProduct (N + 1) E => p.1.2.2 i) :=
    (continuous_apply i).comp continuous_fst.snd.snd
  have hforce (i : Fin (N + 1)) : Continuous
      (fun p : Coefficients N E × BlockProduct (N + 1) E =>
        forcing (p.1.2.2 i) D C₀ K (p.2 i)) :=
    continuous_const.mul (continuous_const.add ((saturation_contDiff K 0).continuous.comp
      (((hb i).inner (hx i)).div_const D)))
  have hgate (i : Fin (N + 1)) : Continuous
      (fun p : Coefficients N E × BlockProduct (N + 1) E =>
        radialGate (p.1.2.1 i) B α (p.2 i)) :=
    (gate_contDiff 0).continuous.comp
      (((ha i).inner ((radialSquash_contDiff B 0).continuous.comp (hx i))).div_const α)
  unfold Data.energy Data.force Data.gate coefficientsData
  apply Continuous.sub
  · apply Continuous.sub
    · apply continuous_finset_sum
      intro i _
      exact continuous_const.mul ((hx i).inner ((hA i).clm_apply (hx i)))
    · exact hforce 0
  · apply continuous_finset_sum
    intro j _
    exact (hgate j.castSucc).mul (hforce j.succ)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance blockProductMeasurableSpace : MeasurableSpace (BlockProduct N E) := borel _

local instance blockProductBorelSpace : BorelSpace (BlockProduct N E) := ⟨rfl⟩

/-- Riesz duality and the parameterized derivative measurability theorem
apply to the actual energy, so no formula for a surrogate oracle is used. -/
theorem coefficients_gradient_measurable (B α D C₀ K : ℝ) :
    Measurable (fun p : Coefficients N E × BlockProduct (N + 1) E =>
      gradient (coefficientsData N E p.1 B α D C₀ K).energy p.2) := by
  have hd : Measurable (fun p : Coefficients N E × BlockProduct (N + 1) E =>
      fderiv ℝ (coefficientsData N E p.1 B α D C₀ K).energy p.2) :=
    measurable_fderiv_with_param ℝ
      (f := fun q : Coefficients N E => (coefficientsData N E q B α D C₀ K).energy)
      (coefficients_energy_continuous (N := N) (E := E) B α D C₀ K)
  exact (InnerProductSpace.toDual ℝ (BlockProduct (N + 1) E)).symm.continuous.measurable.comp hd

end RandomizedFO2003.Cascade
