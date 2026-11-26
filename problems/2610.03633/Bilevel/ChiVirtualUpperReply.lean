import Bilevel.ChiVirtualUpperContinuity
import Bilevel.ChiVirtualBorelReply
import Bilevel.ChiUpperRegularity

/-! Borel full upper-gradient reply, including the actual nonlinear upper
base. Only the disclosed arrays and query enter this formula. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped Topology
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension PartialLegendre ChiUpper
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualUpperBase_reframe (m : ℕ) (M : Node E) (UM : Space M.n →ₗᵢ[ℝ] E)
    (ν : ℝ) (D : Geometry F) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (z : Joint E (Blocks m F)) :
    virtualUpperBase m (reframeNode M UM) ν (reframeGeometry D U) d ρ R rM r macroColumns columns z=
      virtualUpperBase m M ν D d ρ R rM r macroColumns columns z := by
  unfold virtualUpperBase
  rw [virtualOuterCarrier_reframe]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem stateUpperBase_reframe (m : ℕ) (M : Node E) (UM : Space M.n →ₗᵢ[ℝ] E)
    (ν : ℝ) (D : Geometry F) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ)
    (p : VirtualState M D) :
    stateUpperBase m (reframeNode M UM) ν (reframeGeometry D U) d ρ R rM r p=
      stateUpperBase m M ν D d ρ R rM r p := by
  funext z
  exact virtualUpperBase_reframe m M UM ν D U d ρ R (rM p.1) (r p.1) p.2.1 p.2.2 z

def virtualUpperGradient (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (s : ℕ)
    (b : Normals s) (p : FullVirtualQuery M D m s) : FullNormalVariables E (Blocks m F) (Normals s) :=
  fullUpperGradient (stateUpperBase m M ν D d ρ R rM r p.1) b p.2

theorem virtualUpperGradient_eq (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (s : ℕ)
    (b : Normals s) (p : FullVirtualQuery M D m s)
    (hf : Differentiable ℝ (stateUpperBase m M ν D d ρ R rM r p.1)) :
    virtualUpperGradient m M ν D d ρ R rM r s b p=
      gradient (fullUpper (stateUpperBase m M ν D d ρ R rM r p.1) b) p.2 :=
  (fullUpper_hasGradientAt _ hf b p.2).gradient.symm

theorem virtualUpperGradient_eq_original (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (s : ℕ)
    (b : Normals s) (p : FullVirtualQuery M D m s) (f : Joint E (Blocks m F) → ℝ)
    (hf : Differentiable ℝ f)
    (he : gradient (stateUpperBase m M ν D d ρ R rM r p.1) (baseProjection p.2)=gradient f (baseProjection p.2)) :
    virtualUpperGradient m M ν D d ρ R rM r s b p=gradient (fullUpper f b) p.2 := by
  rw [(fullUpper_hasGradientAt f hf b p.2).gradient]
  change pack (pack (gradient (stateUpperBase m M ν D d ρ R rM r p.1) (baseProjection p.2)).fst 0)
    (pack (gradient (stateUpperBase m M ν D d ρ R rM r p.1) (baseProjection p.2)).snd b)=_
  rw [he]
  rfl

theorem virtualUpperGradient_reframe (m : ℕ) (M : Node E) (UM : Space M.n →ₗᵢ[ℝ] E)
    (ν : ℝ) (D : Geometry F) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (s : ℕ)
    (b : Normals s) (p : FullVirtualQuery M D m s) :
    virtualUpperGradient m (reframeNode M UM) ν (reframeGeometry D U) d ρ R rM r s b p=
      virtualUpperGradient m M ν D d ρ R rM r s b p := by
  unfold virtualUpperGradient
  rw [stateUpperBase_reframe]

theorem virtualUpperGradient_eq_of_base_germ (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (s : ℕ)
    (b : Normals s) (p : FullVirtualQuery M D m s) (f : Joint E (Blocks m F) → ℝ)
    (hf : Differentiable ℝ f)
    (he : f =ᶠ[𝓝 (baseProjection p.2)] stateUpperBase m M ν D d ρ R rM r p.1) :
    virtualUpperGradient m M ν D d ρ R rM r s b p=gradient (fullUpper f b) p.2 :=
  virtualUpperGradient_eq_original m M ν D d ρ R rM r s b p f hf he.gradient_eq.symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

theorem virtualUpperGradient_measurable (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (s : ℕ)
    [MeasurableSpace (Joint E (Blocks m F))] [BorelSpace (Joint E (Blocks m F))]
    [MeasurableSpace (FullNormalVariables E (Blocks m F) (Normals s))]
    [BorelSpace (FullNormalVariables E (Blocks m F) (Normals s))]
    (b : Normals s) :
    Measurable (virtualUpperGradient m M ν D d ρ R rM r s b) := by
  let U := Blocks m F
  let V := Normals s
  let W := Joint E U
  let Q := FullNormalVariables E U V
  letI : MeasurableSpace U := borel U
  letI : BorelSpace U := ⟨rfl⟩
  letI : SecondCountableTopology U := inferInstance
  letI : SecondCountableTopology W := inferInstance
  letI : SecondCountableTopology (Joint U V) := inferInstance
  letI : SecondCountableTopology Q :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ W (Joint U V)).toHomeomorph.secondCountableTopology
  letI : BorelSpace (VirtualState M D) := inferInstance
  letI : SecondCountableTopology (VirtualState M D) := inferInstance
  letI : MeasurableSpace (Joint U V) := borel (Joint U V)
  letI : BorelSpace (Joint U V) := ⟨rfl⟩
  have hscalar := stateUpperBase_continuous m M ν D d ρ R rM r
  have hgrad := ParametricGradient.gradient_measurable
    (stateUpperBase m M ν D d ρ R rM r) hscalar
  have hpoint := (baseProjection (X:=E) (U:=U) (V:=V)).continuous.measurable.comp
    (measurable_snd : Measurable (Prod.snd : FullVirtualQuery M D m s → Q))
  have heval := hgrad.comp (measurable_fst.prodMk hpoint)
  have hfst := (jointFstLinear : W →L[ℝ] E).continuous.measurable.comp heval
  have hsnd := (jointSndLinear : W →L[ℝ] U).continuous.measurable.comp heval
  have hz : Measurable (fun _ : FullVirtualQuery M D m s => (0:U)) := measurable_const
  have hb : Measurable (fun _ : FullVirtualQuery M D m s => b) := measurable_const
  have hx := (packLinear (X:=E) (Y:=U)).continuous.measurable.comp (hfst.prodMk hz)
  have hy := (packLinear (X:=U) (Y:=V)).continuous.measurable.comp (hsnd.prodMk hb)
  have hout := (packLinear (X:=W) (Y:=Joint U V)).continuous.measurable.comp (hx.prodMk hy)
  exact hout

end Bilevel.ChiPrefixEvaluation
