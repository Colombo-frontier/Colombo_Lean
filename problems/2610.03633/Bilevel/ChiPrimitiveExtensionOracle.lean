import Bilevel.ChiHierarchyOracle
import Bilevel.ChiPrimitiveOracle

/-! The actual active and inactive extensions produce a full-query SFO
for the same Primitive, with fixed globally conservative sample scalars. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry PartialLegendre ChiExtension
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace (FullNormalVariables X U V)] [BorelSpace (FullNormalVariables X U V)]
  [SecondCountableTopology (FullNormalVariables X U V)]

set_option maxHeartbeats 1200000 in
theorem extension_primitive_oracle
    (Ext Ext₀ : Joint (Joint X U) V → ℝ) (hExt : ContDiff ℝ 3 Ext) (hExt₀ : ContDiff ℝ 3 Ext₀)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖ ≤ (1:ℝ)/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖ ≤ (1:ℝ)/4)
    {μ L ρ η : ℝ} (hμ : 0 < μ) (hη : 0 < η)
    (hjet : ∀ z,‖iteratedFDeriv ℝ 1 (fun q => Ext q-Ext₀ q) z‖ ≤ η)
    (P : Model.Primitive (X:=Joint X U) (Y:=Joint U V) μ L L L ρ)
    (hP : ∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ ha
      (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) (σ : ℝ) :
    let g := fullExtensionLower Ext hExt ⟨1/12,by norm_num⟩ ha (by change (1:ℝ)/12<1;norm_num) μ L
    let g₀ := fullExtensionLower Ext₀ hExt₀ ⟨1/4,by norm_num⟩ hi (by change (1:ℝ)/4<1;norm_num) μ L
    ∃ hB : 0 < 4*μ*η,
    ∃ O : FreshOracle.Oracle (Query:=FullNormalVariables X U V) (E:=FullNormalVariables X U V)
      (BernoulliOracle.law (BernoulliOracle.probability (4*μ*η) σ) (BernoulliOracle.probability_le_one hB)) σ,
      (∀ z,O.truth z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd)) ∧
      (∀ z coin,O.sample z coin=gradient (ChiConservative.samplePotential g g₀
        (BernoulliOracle.probability (4*μ*η) σ) coin) z) ∧
      (∀ z,(∫ coin,O.sample z coin ∂BernoulliOracle.law (BernoulliOracle.probability (4*μ*η) σ)
        (BernoulliOracle.probability_le_one hB))=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd)) ∧
      (∀ z,(∫ coin,‖(O.sample z coin).fst-P.gx z.fst z.snd‖^2+‖(O.sample z coin).snd-P.gy z.fst z.snd‖^2
        ∂BernoulliOracle.law (BernoulliOracle.probability (4*μ*η) σ) (BernoulliOracle.probability_le_one hB)) ≤ σ^2) := by
  dsimp only
  have hB : 0 < 4*μ*η := by positivity
  have henv := ChiOuter.source_conjugate_coefficient hμ.le hη.le
  let O := extensionFreshOracle Ext Ext₀ hExt hExt₀ ⟨1/12,by norm_num⟩ ⟨1/4,by norm_num⟩ ha hi
    (by change (1:ℝ)/12<1;norm_num) (by change (1:ℝ)/4<1;norm_num) μ L hμ.le (σ:=σ) hB hjet henv
  have htruth (z : FullNormalVariables X U V) : O.truth z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd) :=
    lower_full_gradient P _ (fun q => (fullExtensionLower_hasGradientAt Ext hExt ⟨1/12,by norm_num⟩ ha
      (by change (1:ℝ)/12<1;norm_num) μ L q).differentiableAt) hP z
  refine ⟨hB,O,htruth,?_,?_,?_⟩
  · exact extensionFreshOracle_conservative Ext Ext₀ hExt hExt₀ ⟨1/12,by norm_num⟩ ⟨1/4,by norm_num⟩ ha hi
      (by change (1:ℝ)/12<1;norm_num) (by change (1:ℝ)/4<1;norm_num) μ L hμ.le hB hjet henv
  · intro z
    exact (O.sample_mean z).trans (htruth z)
  · intro z
    have hh := O.variance z
    rw [htruth z] at hh
    simpa only [norm_sq] using hh

end Bilevel.ChiPrimitive
