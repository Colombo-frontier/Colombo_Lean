import Bilevel.ChiCarrierFineData
import Bilevel.ChiFineGeneric

/-! The actual recursive selected fine normal extension, with its mixed
derivative and full-gradient budgets. The source ledger and annular overlap
are proved for this construction, rather than assumed as certificates. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule SmallGapLiftSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def selectedCoupling (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ)
    (y : CompensatedMean.LowerSpace (Blocks m E)) : ℝ :=
  ∑ p ∈ Finset.range (levels θ+1),selectedFinePiece m D d j I c θ p (CompensatedMean.uProj _ y)*
    SmallGapProfiles.normal (width c (D (j+d) []).width θ p) (CompensatedMean.sProj _ y)

theorem selectedCoupling_contDiff (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D (j+d) []).width) (hθ : 1≤θ) :
    ContDiff ℝ 3 (selectedCoupling m D d j I c θ) :=
  (fineData m D d j I c θ hc hβ hθ).coupling_contDiff

theorem source_selected_coupling_jets : ∃ B : ℝ,1≤B ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let D := sourceGeometry initial r η b A K ζ cn CR U
      ∀ (d j : ℕ) (I : List ℕ) (m : ℕ) (c θ : ℝ),0<c → c≤1/128 → 1≤θ →
      let ℓ := (D (j+d) []).ell
      let β := (D (j+d) []).width
      ∀ y : CompensatedMean.LowerSpace (Blocks m F),
      ‖iteratedFDeriv ℝ 1 (selectedCoupling m D d j I c θ) y‖≤6*C*B^(d+1)*ℓ*β^2 ∧
      ‖iteratedFDeriv ℝ 2 (selectedCoupling m D d j I c θ) y‖≤12*C*B^(d+1)*ℓ*β*Real.sqrt θ/c ∧
      ‖iteratedFDeriv ℝ 3 (selectedCoupling m D d j I c θ) y‖≤24*C*B^(d+1)*ℓ*θ/c^2 := by
  obtain ⟨B,hB,hledger⟩ := source_selected_fine_ledger
  refine ⟨B,hB,fun F _ _ _ initial hl hw r η b A K ζ cn CR hr hη hη1 hb hb1 hK hζ hζ1 hCR U => ?_⟩
  dsimp only
  let D := sourceGeometry initial r η b A K ζ cn CR U
  intro d j I m c θ hc hcs hθ
  let ℓ := (D (j+d) []).ell
  let β := (D (j+d) []).width
  have hpos := parentScale_positive initial r η hl hw hr hη (j+d+1)
  have hell : 0≤ℓ := hpos.1.le
  have hβ : 0<β := hpos.2
  let P : ChiFine.Parameters := ⟨ℓ,β,θ,c,hell,hβ,hθ,hc,hcs⟩
  let Q := fineData m D d j I c θ hc hβ hθ
  have hbound : ∀ p,p≤Q.J → ∀ x,|Q.e p x|≤B^(d+1)*P.amplitude*P.θ^(-amplitudeExponent p) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (Q.e p) x‖≤
        B^(d+1)*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ p)^k.val) := by
    intro p hp x
    have hjets (q : ℕ) (hq : q≤3) := (hledger F initial hl hw r η b A K ζ cn CR
      hr hη hη1 hb hb1 hK hζ hζ1 hCR U d j I m x q hq).2 c θ hc hcs hθ p hp
    constructor
    · have ht := hjets 0 (by norm_num)
      rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at ht
      exact ht.trans_eq (by dsimp [fineScale,P,ChiFine.Parameters.amplitude,ℓ,β,D];ring)
    · intro k
      have ht := hjets (k.val+1) (by omega)
      have hδ := pieceResolution_pos c β θ hc hβ hθ p
      apply ht.trans_eq
      dsimp only [fineScale,P,ChiFine.Parameters.amplitude]
      change B^(d+1)*(ℓ*β/(pieceResolution c β θ p)^k.val)=
        B^(d+1)*(ℓ*β^2)/(β*(pieceResolution c β θ p)^k.val)
      field_simp [hβ.ne',hδ.ne']
      ring
  intro y
  exact ChiFine.generic_coupling_bounds P Q rfl (fun _ => rfl) (B^(d+1))
    (one_le_pow₀ hB) hbound (fineData_overlap m D d j I c θ hc hβ hθ) y

end Bilevel.ChiCarrier
