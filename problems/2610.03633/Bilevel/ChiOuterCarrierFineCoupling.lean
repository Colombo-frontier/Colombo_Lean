import Bilevel.ChiOuterCarrierFineData
import Bilevel.ChiFineGeneric

/-! Actual outer-and-inner selected fine extension. All derivative bounds
below are discharged from the source construction, including mixed outer
derivatives, and retain the finite annular overlap of the deepest frontier. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule SmallGapLiftSupport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerCoupling (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (y : CompensatedMean.LowerSpace (Joint E (Blocks m F))) : ℝ :=
  ∑ p ∈ Finset.range (levels θ+1),outerFinePiece m M D d c θ p (CompensatedMean.uProj _ y)*
    SmallGapProfiles.normal (width c (D d []).width θ p) (CompensatedMean.sProj _ y)

theorem outerCoupling_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) :
    ContDiff ℝ 3 (outerCoupling m M D d c θ) :=
  (outerFineData m M D d c θ hc hβ hθ).coupling_contDiff

theorem source_outer_coupling_jets : ∃ B : ℝ,1≤B ∧
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
      ∀ y : CompensatedMean.LowerSpace (Joint E (Blocks m F)),
      ‖iteratedFDeriv ℝ 1 (outerCoupling m M D d c θ) y‖≤6*C*B^(d+2)*ℓ*β^2 ∧
      ‖iteratedFDeriv ℝ 2 (outerCoupling m M D d c θ) y‖≤12*C*B^(d+2)*ℓ*β*Real.sqrt θ/c ∧
      ‖iteratedFDeriv ℝ 3 (outerCoupling m M D d c θ) y‖≤24*C*B^(d+2)*ℓ*θ/c^2 := by
  obtain ⟨B,hB,hledger⟩ := source_outer_selected_fine_ledger
  refine ⟨B,hB,fun E F _ _ _ _ _ _ n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V => ?_⟩
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  intro d m c θ hc hcs hθ
  let ℓ := (D d []).ell
  let β := (D d []).width
  have hpos := parentScale_positive initial r η hl hw hr hη (d+1)
  have hell : 0≤ℓ := hpos.1.le
  have hβ : 0<β := hpos.2
  let P : ChiFine.Parameters := ⟨ℓ,β,θ,c,hell,hβ,hθ,hc,hcs⟩
  let Q := outerFineData m M D d c θ hc hβ hθ
  have hbound : ∀ p,p≤Q.J → ∀ x,|Q.e p x|≤B^(d+2)*P.amplitude*P.θ^(-amplitudeExponent p) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (Q.e p) x‖≤
        B^(d+2)*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ p)^k.val) := by
    intro p hp x
    have hjets (q : ℕ) (hq : q≤3) := (hledger E F n initial hl hw r η b A K ζ cn CR Km
      hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V d m x q hq).2 c θ hc hcs hθ p hp
    constructor
    · have ht := hjets 0 (by norm_num)
      rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at ht
      exact ht.trans_eq (by dsimp [fineScale,P,ChiFine.Parameters.amplitude,ℓ,β,D];ring)
    · intro k
      have ht := hjets (k.val+1) (by omega)
      have hδ := pieceResolution_pos c β θ hc hβ hθ p
      apply ht.trans_eq
      dsimp only [fineScale,P,ChiFine.Parameters.amplitude]
      change B^(d+2)*(ℓ*β/(pieceResolution c β θ p)^k.val)=
        B^(d+2)*(ℓ*β^2)/(β*(pieceResolution c β θ p)^k.val)
      field_simp [hβ.ne',hδ.ne']
      ring
  intro y
  exact ChiFine.generic_coupling_bounds P Q rfl (fun _ => rfl) (B^(d+2))
    (one_le_pow₀ hB) hbound (outerFineData_overlap m M D d c θ hc hβ hθ) y

end Bilevel.ChiOuter
