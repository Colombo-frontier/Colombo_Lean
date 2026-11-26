import Bilevel.ChiOuterCarrierSignalLedger
import Bilevel.ChiSignalExtension
import Bilevel.ChiFineSignalCore

/-! The globally fixed inactive normal extension for the complete actual
outer-and-inner hierarchy. The signal has a fixed resolution w_last/8 and
its full-space gradient/jet envelope is proved from the source family. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule SmallGapLiftSupport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerSignalNormal (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (s : ℕ) (i : Fin s) : ChiExtension.Full (Joint E (Blocks m F)) s → ℝ :=
  let W := width c (D d []).width θ (levels θ)
  ChiExtension.normalTerm s i (outerFineSignal m M D d (W/8)) W

def outerInactiveNormal (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s) :
    ChiExtension.Full (Joint E (Blocks m F)) s → ℝ :=
  fun z => outerFineNormal m M D d c θ hc hβ hθ s i z-outerSignalNormal m M D d c θ s i z

theorem outerSignalNormal_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s) :
    ContDiff ℝ 3 (outerSignalNormal m M D d c θ s i) :=
  ChiExtension.normalTerm_contDiff s i (outerFineSignal_contDiff m M D d _)
    (width_pos c _ θ hc hβ hθ _)

theorem outerInactiveNormal_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s) :
    ContDiff ℝ 3 (outerInactiveNormal m M D d c θ hc hβ hθ s i) :=
  (outerFineNormal_contDiff m M D d c θ hc hβ hθ s i).sub
    (outerSignalNormal_contDiff m M D d c θ hc hβ hθ s i)

theorem outerSignalNormal_zero_trace (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s)
    (z : Joint E (Blocks m F)) : outerSignalNormal m M D d c θ s i (pack z 0)=0 :=
  ChiExtension.normalTerm_zero_trace s i _ (width_pos c _ θ hc hβ hθ _) z

theorem outerInactiveNormal_zero_trace (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s)
    (z : Joint E (Blocks m F)) : outerInactiveNormal m M D d c θ hc hβ hθ s i (pack z 0)=0 := by
  rw [outerInactiveNormal,outerFineNormal_zero_trace,outerSignalNormal_zero_trace m M D d c θ hc hβ hθ,
    sub_self]

theorem outerInactiveNormal_normal_gradient (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s)
    (z : Joint E (Blocks m F)) :
    HasGradientAt (fun q : ChiExtension.Normals s => outerInactiveNormal m M D d c θ hc hβ hθ s i (pack z q))
      (EuclideanSpace.single i (outerFineFlatFrontier m M D d
        (width c (D d []).width θ (levels θ)/8) z)) 0 := by
  have hs := ChiExtension.normalTerm_normal_gradient s i
    (outerFineSignal m M D d (width c (D d []).width θ (levels θ)/8))
    (width_pos c _ θ hc hβ hθ (levels θ)) z
  have hh := (outerFineNormal_normal_gradient m M D d c θ hc hβ hθ s i z).sub hs
  have hg : HasGradientAt (fun q : ChiExtension.Normals s =>
      outerInactiveNormal m M D d c θ hc hβ hθ s i (pack z q))
      (EuclideanSpace.single i (outerFineFrontier m M D d z)-
        EuclideanSpace.single i (outerFineSignal m M D d (width c (D d []).width θ (levels θ)/8) z)) 0 := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_sub] using hh
  convert hg using 1
  ext k
  simp only [PiLp.sub_apply,EuclideanSpace.single_apply,outerFineSignal_eq_sub]
  split_ifs <;> ring

theorem source_outer_signal_normal_jets : ∃ B : ℝ,1≤B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (d m : ℕ) (c θ : ℝ),0<c → c≤1/128 → 1≤θ →
      let ℓ := (D d []).ell
      let β := (D d []).width
      let W := width c β θ (levels θ)
      ∀ (s : ℕ) (i : Fin s) (z : ChiExtension.Full (Joint E (Blocks m F)) s),
      ‖iteratedFDeriv ℝ 1 (outerSignalNormal m M D d c θ s i) z‖≤2*C*B^(d+2)*ℓ*β*W ∧
      ‖iteratedFDeriv ℝ 2 (outerSignalNormal m M D d c θ s i) z‖≤11*C*B^(d+2)*ℓ*β ∧
      ‖iteratedFDeriv ℝ 3 (outerSignalNormal m M D d c θ s i) z‖≤92*C*B^(d+2)*ℓ*β/W := by
  obtain ⟨B,hB,hledger⟩ := source_outer_signal_ledger
  have hB0 : 0≤B := by linarith
  refine ⟨B,hB,fun E F _ _ _ _ _ _ n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V => ?_⟩
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  intro d m c θ hc hcs hθ
  let ℓ := (D d []).ell
  let β := (D d []).width
  let W := width c β θ (levels θ)
  have hp := parentScale_positive initial r η hl hw hr hη (d+1)
  have hell : 0≤ℓ := hp.1.le
  have hβ : 0<β := hp.2
  let P : ChiFine.Parameters := ⟨ℓ,β,θ,c,hell,hβ,hθ,hc,hcs⟩
  have hW : 0<W := P.finalWidth_pos
  have hτ : 0<W/8 := P.signalResolution_pos
  have hτβ : W/8≤β/16 := by have hh := P.signalResolution_small;change W/8≤β/1024 at hh;linarith
  have hjets := hledger E F n initial hl hw r η b A K ζ cn CR Km
    hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V d m (W/8) hτ hτβ
  intro s i z
  have hh := ChiFine.signal_normal_jets (outerFineSignal_contDiff m M D d (W/8))
    (pow_nonneg hB0 (d+2)) (show 0≤ℓ*β by positivity) hW hjets s i z
  simpa only [mul_assoc] using hh

end Bilevel.ChiOuter
