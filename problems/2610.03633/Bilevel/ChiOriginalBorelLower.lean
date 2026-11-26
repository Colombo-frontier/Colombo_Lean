import Bilevel.ChiOriginalPotential

/-! Joint Borel original lower-gradient response. The original extension
and its chosen contraction certificate are identified exactly with the
complete-column evaluator, including a different inactive bound. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension PartialLegendre
variable {E F A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
  (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
  (h2 : ∀ p : {p : VirtualState M D | ValidState M D (fun _ => M.n+1) (fun _ => fullCounts D) p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m M D J (fun _ => M.n+1) (fun _ => fullCounts D)
      c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
  (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
  (δ : NNReal) (hδ : δ<1)
  (hOriginal : ∀ a,ContDiff ℝ 3 (originalPotential active m (reframeNode M (UM a))
    (reframeGeometry D (U a)) J c v hc hβ hv s index radialIndex fineIndex rad R dn))
  (hOriginal2 : ∀ a z,‖iteratedFDeriv ℝ 2 (originalPotential active m (reframeNode M (UM a))
    (reframeGeometry D (U a)) J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤(δ:ℝ))

theorem complete_lower_reply_eq_original (μ L : ℝ) (a : A)
    (q : FullNormalVariables E (Blocks m F) (Normals s)) :
    virtualFullGradient active m M D J (fun _ => M.n+1) (fun _ => fullCounts D)
      c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L (fullFrameState M D UM U a,q)=
    gradient (fullExtensionLower (originalPotential active m (reframeNode M (UM a))
      (reframeGeometry D (U a)) J c v hc hβ hv s index radialIndex fineIndex rad R dn)
      (hOriginal a) δ (hOriginal2 a) hδ μ L) q := by
  rw [virtualFullGradient_eq active m M D J (fun _ => M.n+1) (fun _ => fullCounts D)
    c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L
    (fullFrameState M D UM U a,q) (fullFrameState_valid M D UM U a)]
  congr 1
  exact fullExtensionLower_congr
    (statePotential_full_frame active m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn UM U a)
    _ _ _ _ _ _ _ _ μ L

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace A]
  [MeasurableSpace (Joint (Blocks m F) (Normals s))] [BorelSpace (Joint (Blocks m F) (Normals s))]
  [MeasurableSpace (Joint E (Joint (Blocks m F) (Normals s)))]
  [BorelSpace (Joint E (Joint (Blocks m F) (Normals s)))]
  [MeasurableSpace (FullNormalVariables E (Blocks m F) (Normals s))]
  [BorelSpace (FullNormalVariables E (Blocks m F) (Normals s))]

include hR hw h2 in
theorem original_lower_reply_measurable (hdata : Measurable (frameData M D UM U)) (μ L : ℝ) :
    Measurable (fun p : A × FullNormalVariables E (Blocks m F) (Normals s) =>
      gradient (fullExtensionLower (originalPotential active m (reframeNode M (UM p.1))
        (reframeGeometry D (U p.1)) J c v hc hβ hv s index radialIndex fineIndex rad R dn)
        (hOriginal p.1) δ (hOriginal2 p.1) hδ μ L) p.2) := by
  have hstate := fullFrameState_measurable M D UM U hdata
  have harg : Measurable (fun p : A × FullNormalVariables E (Blocks m F) (Normals s) =>
      (fullFrameState M D UM U p.1,p.2)) := (hstate.comp measurable_fst).prodMk measurable_snd
  have hm := (virtualFullGradient_measurable active m M D J (fun _ => M.n+1) (fun _ => fullCounts D)
    c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L).comp harg
  convert hm using 1
  funext p
  exact (complete_lower_reply_eq_original active m M D J c v hc hβ hv s index radialIndex fineIndex
    rad R dn hR hw h2 UM U δ hδ hOriginal hOriginal2 μ L p.1 p.2).symm

end Bilevel.ChiPrefixEvaluation
