import Bilevel.EndpointTransportOuterFineCoupling
import Bilevel.ChiCarrierSourceWidths
import Bilevel.ChiOuterCarrierLedger

/-! The actual physical fine coupling after the one-sided macro selection,
with every geometric width premise discharged by the source family. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ZeroChainSchedule SmallGapLiftSupport

theorem source_outer_physical_fine_coupling_jets : ∃ Cb : ℝ,1≤Cb ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      (n D nM : ℕ) (Q : Rotations n D) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (Ar K ζ cn CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR → 1≤Km →
      ∀ (UM : Space nM →ₗᵢ[ℝ] E)
      (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block D),
      let M := sourceMacroNode nM initial Km UM
      let G := sourceGeometry initial r η b Ar K ζ cn CR U
      ∀ (m : ℕ) (macroP : X →L[ℝ] E) (A : X →L[ℝ] Blocks m (Block D))
      (B : X →L[ℝ] Physical n D),‖macroP‖≤1 → ‖A‖≤1 → ‖B‖≤1 →
      ∀ (d : ℕ) (P : ChiFine.Parameters),P.β=(G d []).width →
      ∀ y : CompensatedMean.LowerSpace X,
      ‖iteratedFDeriv ℝ 1 (outerPhysicalFineData m Q M macroP G A B P d).coupling y‖≤6*C*Cb^(d+2)*P.ℓ*P.β^2 ∧
      ‖iteratedFDeriv ℝ 2 (outerPhysicalFineData m Q M macroP G A B P d).coupling y‖≤12*C*Cb^(d+2)*P.ℓ*P.β*Real.sqrt P.θ/P.c ∧
      ‖iteratedFDeriv ℝ 3 (outerPhysicalFineData m Q M macroP G A B P d).coupling y‖≤24*C*Cb^(d+2)*P.ℓ*P.θ/P.c^2 := by
  obtain ⟨Cb,hCb,hb⟩ := outer_physical_coupling_jets
  refine ⟨Cb,hCb,fun E _ _ _ X _ _ n D nM Q initial hl hw r η b Ar K ζ cn CR Km hr hη hη1 hbp hbp1 hK hζ hζ1 hCR hKm UM U => ?_⟩
  dsimp only
  let M := sourceMacroNode nM initial Km UM
  let G := sourceGeometry initial r η b Ar K ζ cn CR U
  have hpos := parentScale_positive initial r η hl hw hr hη
  have hadm (j : ℕ) (I : List ℕ) : NodeJetAdmissible (G j I) :=
    sourceNode_admissible Ar K ζ cn (η j) CR _ _ (r j) (b j) (U j I)
      hK hζ hζ1 (hη j) (hη1 j) hCR (hpos j).1 (hpos j).2 (hr j) (hbp j) (hbp1 j)
  have hmono := parentScale_width_antitone initial r η hl hw hr hη hη1
  intro m macroP A B hm hA hB d P hβ y
  apply hb E X n D m M macroP hm hw (sourceMacro_radius_ge_width hw hKm UM)
    G hadm A B hA hB Q P d _ _ _ y
  · rw [hβ]
    exact hmono (show 0≤d+1 by omega)
  · intro k I hk
    rw [hβ]
    exact hmono (by omega : k+1≤d+1)
  · intro I
    rw [hβ]
    exact (hadm d I).2.2.1

end Bilevel.EndpointTransportResponse
