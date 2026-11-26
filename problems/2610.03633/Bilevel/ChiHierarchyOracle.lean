import Bilevel.ChiHierarchySignal
import Bilevel.ChiExtensionOracle

/-! Actual complete-hierarchy informative gradient and fixed conservative
oracle. The source's normal width is retained in the supplied signal budget. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem source_conjugate_coefficient {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 ≤ η) :
    (Real.sqrt 2*(3*μ/2)/(1-max ((1:ℝ)/12) (1/4)))*η ≤ 4*μ*η := by
  have he : max ((1:ℝ)/12) (1/4)=(1:ℝ)/4 := by norm_num
  rw [he]
  have hs : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hh := mul_le_mul_of_nonneg_right hs (mul_nonneg hμ hη)
  convert mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring

theorem hierarchy_lower_signal_envelope (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0 < c) (hβ : 0 < (D J []).width) (hv : 1 ≤ v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ)
    (dn : ℝ) (hdn : 0 < dn) (hw : ∀ i : Fin J,0 < (D (i.val+1) []).width)
    (μ L B : ℝ) (hμ : 0 ≤ μ)
    (hsignal : ∀ z,‖iteratedFDeriv ℝ 1 (outerSignalNormal m M D J c v s fineIndex) z‖ ≤ B) :
    let Ext := hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
    let Ext₀ := hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
    let hExt := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw
    let hExt₀ := hierarchyInactiveExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw
    ∀ (ha : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖ ≤ (1:ℝ)/12)
      (hi : ∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖ ≤ (1:ℝ)/4) (q : FullNormalVariables E (Blocks m F) (Normals s)),
    ‖gradient (fullExtensionLower Ext hExt ⟨1/12,by norm_num⟩ ha (by change (1:ℝ)/12<1;norm_num) μ L) q-
      gradient (fullExtensionLower Ext₀ hExt₀ ⟨1/4,by norm_num⟩ hi (by change (1:ℝ)/4<1;norm_num) μ L) q‖ ≤ 4*μ*B/dn := by
  dsimp only
  intro ha hi q
  have hB : 0 ≤ B := (norm_nonneg _).trans (hsignal 0)
  have hh := fullExtensionLower_two_bound_envelope _ _
    (hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw)
    (hierarchyInactiveExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw)
    ⟨1/12,by norm_num⟩ ⟨1/4,by norm_num⟩ ha hi
    (by change (1:ℝ)/12<1;norm_num) (by change (1:ℝ)/4<1;norm_num) μ L hμ
    (hierarchy_difference_first_bound m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hdn B hsignal) q
  apply hh.trans
  convert source_conjugate_coefficient hμ (div_nonneg hB hdn.le) using 1
  ring

def hierarchyFreshOracle (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0 < c) (hβ : 0 < (D J []).width) (hv : 1 ≤ v)
    (s : ℕ) [MeasurableSpace (FullNormalVariables E (Blocks m F) (Normals s))]
    [BorelSpace (FullNormalVariables E (Blocks m F) (Normals s))]
    [SecondCountableTopology (FullNormalVariables E (Blocks m F) (Normals s))]
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ)
    (dn : ℝ) (hdn : 0 < dn) (hw : ∀ i : Fin J,0 < (D (i.val+1) []).width)
    (μ L B σ : ℝ) (hμ : 0 < μ) (hB : 0 < B)
    (hsignal : ∀ z,‖iteratedFDeriv ℝ 1 (outerSignalNormal m M D J c v s fineIndex) z‖ ≤ B)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2 (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖ ≤ (1:ℝ)/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2 (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖ ≤ (1:ℝ)/4) :
    FreshOracle.Oracle (Query:=FullNormalVariables E (Blocks m F) (Normals s))
      (E:=FullNormalVariables E (Blocks m F) (Normals s))
      (BernoulliOracle.law (BernoulliOracle.probability (4*μ*B/dn) σ)
        (BernoulliOracle.probability_le_one (by positivity))) σ :=
  extensionFreshOracle _ _
    (hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw)
    (hierarchyInactiveExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw)
    ⟨1/12,by norm_num⟩ ⟨1/4,by norm_num⟩ ha hi
    (by change (1:ℝ)/12<1;norm_num) (by change (1:ℝ)/4<1;norm_num) μ L hμ.le (by positivity)
    (hierarchy_difference_first_bound m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hdn B hsignal)
    (by convert source_conjugate_coefficient hμ.le (div_nonneg hB.le hdn.le) using 1; ring)

end Bilevel.ChiOuter
