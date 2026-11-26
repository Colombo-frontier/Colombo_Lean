import Bilevel.ChiPrimitiveExtensionOracle

/-! A compact source-facing certificate for the actual conservative SFO.
The returned Oracle includes full mean-square integrability, centering and
variance. Its truth and every sample are tied to the displayed scalars. -/
noncomputable section
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry PartialLegendre ChiExtension
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

def HasConservativeOracle {μ Lf Lg Cf ρ : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (g g₀ : Joint X Y → ℝ) (B : ℝ) : Prop :=
  ∀ [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] (σ : ℝ),
  ∃ hB : 0<B,
  ∃ O : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
    (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) σ,
    (∀ z,O.truth z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd)) ∧
    (∀ z coin,O.sample z coin=gradient (ChiConservative.samplePotential g g₀ (BernoulliOracle.probability B σ) coin) z)

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] in
theorem extension_hasConservativeOracle
    (Ext Ext₀ : Joint (Joint X U) V → ℝ) (hExt : ContDiff ℝ 3 Ext) (hExt₀ : ContDiff ℝ 3 Ext₀)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/4)
    {μ L ρ η : ℝ} (hμ : 0<μ) (hη : 0<η)
    (hjet : ∀ z,‖iteratedFDeriv ℝ 1 (fun q => Ext q-Ext₀ q) z‖≤η)
    (P : Model.Primitive (X:=Joint X U) (Y:=Joint U V) μ L L L ρ)
    (hP : ∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ ha
      (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) :
    HasConservativeOracle P
      (fullExtensionLower Ext hExt ⟨1/12,by norm_num⟩ ha (by change (1:ℝ)/12<1;norm_num) μ L)
      (fullExtensionLower Ext₀ hExt₀ ⟨1/4,by norm_num⟩ hi (by change (1:ℝ)/4<1;norm_num) μ L) (4*μ*η) := by
  intro instM instB instS σ
  obtain ⟨hB,O,ht,hs,_hm,_hv⟩ := extension_primitive_oracle Ext Ext₀ hExt hExt₀ ha hi hμ hη hjet P hP σ
  exact ⟨hB,O,ht,hs⟩

end Bilevel.ChiPrimitive
