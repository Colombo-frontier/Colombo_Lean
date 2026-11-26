import Bilevel.ChiCanonicalQueryFamily

/-! A canonical actual expected-query certificate supplies hardness for the
common conservative Primitive class, retaining the same hidden mean instance. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre ChiUpper
  PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}
  (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)

theorem CanonicalQueryCertificate.conservative_hardness
    (μ ρ Δ R₀ σf σg B rate : ℝ) (hR₀ : 0≤R₀) (hB : 0<B)
    (hfamily : ∀ a : Orientations (sourceCounts macroN cn ratios resolutions) J dim,
      ∃ P : Model.Primitive (X:=CanonicalX J dim) (Y:=CanonicalY J dim) μ L L L ρ,
      ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,P.hyperobjective r x=jointOuter (J+1)
          (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
          (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR) rad R J K x) ∧
        H.HasFullOracle μ ρ B a P)
    (hRate : CanonicalQueryCertificate.RateProperty.{0,0} H μ (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB) rate) :
    Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε rate := by
  classical
  choose P r hz hgap hm hFull using hfamily
  obtain ⟨F,hF,hcons,hmean⟩ := H.query_family μ ρ Δ R₀ σf σg B rate hR₀ hB P r hgap hz hm hFull hRate
  exact F.hardness _ ε rate hcons hF

end Bilevel.ChiHierarchyHaar
