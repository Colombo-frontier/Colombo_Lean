import Bilevel.ChiOuterCarrierInactive

/-! Both globally fixed outer-selected fine potentials satisfy the source
fine orders. All tangential, ancestor, and normal variables are included. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule SmallGapLiftSupport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem outerInactiveNormal_last_atom (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s)
    (p : Joint E (Blocks m F)) (q : ChiExtension.Normals s) :
    outerInactiveNormal m M D d c θ hc hβ hθ s i (pack p q)=
      (∑ j ∈ Finset.range (levels θ),outerFinePiece m M D d c θ j p*
        SmallGapProfiles.normal (width c (D d []).width θ j) (q i))+
      (outerFinePiece m M D d c θ (levels θ) p-
        outerFineSignal m M D d (width c (D d []).width θ (levels θ)/8) p)*
        SmallGapProfiles.normal (width c (D d []).width θ (levels θ)) (q i) := by
  simp only [outerInactiveNormal,outerFineNormal,ChiExtension.fineTerm_sum,outerFineData,
    outerSignalNormal,ChiExtension.normalTerm_formula]
  rw [Finset.sum_range_succ]
  ring

theorem source_outer_inactive_normal_jets : ∃ B : ℝ,1≤B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (d m : ℕ) (c θ : ℝ) (hc : 0<c),c≤1/128 → ∀ hθ : 1≤θ,
      let ℓ := (D d []).ell
      let β := (D d []).width
      ∀ (hβ : 0<β) (s : ℕ) (i : Fin s) (z : ChiExtension.Full (Joint E (Blocks m F)) s),
      ‖iteratedFDeriv ℝ 1 (outerInactiveNormal m M D d c θ hc hβ hθ s i) z‖≤8*C*B^(d+2)*ℓ*β^2 ∧
      ‖iteratedFDeriv ℝ 2 (outerInactiveNormal m M D d c θ hc hβ hθ s i) z‖≤23*C*B^(d+2)*ℓ*β*Real.sqrt θ/c ∧
      ‖iteratedFDeriv ℝ 3 (outerInactiveNormal m M D d c θ hc hβ hθ s i) z‖≤116*C*B^(d+2)*ℓ*θ/c^2 := by
  obtain ⟨Ba,hBa,ha⟩ := source_outer_coupling_jets
  obtain ⟨Bs,hBs,hs⟩ := source_outer_signal_normal_jets
  have hBa0 : 0≤Ba := by linarith
  have hBs0 : 0≤Bs := by linarith
  let B := Ba+Bs
  have hB : 1≤B := by unfold B;linarith
  have hBaB : Ba≤B := by unfold B;linarith
  have hBsB : Bs≤B := by unfold B;linarith
  refine ⟨B,hB,fun E F _ _ _ _ _ _ n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V => ?_⟩
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  intro d m c θ hc hcs hθ
  let ℓ := (D d []).ell
  let β := (D d []).width
  intro hβ s i z
  have hell : 0≤ℓ := (parentScale_positive initial r η hl hw hr hη (d+1)).1.le
  have hC := C_pos
  have hB0 : 0≤B := by linarith
  have hap := pow_le_pow_left₀ hBa0 hBaB (d+2)
  have hsp := pow_le_pow_left₀ hBs0 hBsB (d+2)
  let P : ChiFine.Parameters := ⟨ℓ,β,θ,c,hell,hβ,hθ,hc,hcs⟩
  let W := P.finalWidth
  have hW : 0<W := P.finalWidth_pos
  have hWβ : W≤β := by have hh := P.normal_width_small (levels θ);change W≤β/128 at hh;linarith
  have hc1 : c≤1 := by linarith
  have hθpos : 0<θ := by linarith
  have hunit : 1≤Real.sqrt θ/c := (one_le_div hc).mpr (hc1.trans (Real.one_le_sqrt.mpr hθ))
  have hratio : β/W≤θ/c := by
    have hlo := P.final_normal_width
    change c*β/θ≤W ∧ _ at hlo
    apply (div_le_div_iff₀ hW hc).mpr
    have hh := (div_le_iff₀ hθpos).mp hlo.1
    nlinarith
  have hratio' : β/W≤θ/c^2 := hratio.trans
    (div_le_div_of_nonneg_left hθpos.le (sq_pos_of_pos hc) (by nlinarith))
  have ha0 := ha E F n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V
    d m c θ hc hcs hθ (ChiExtension.normalSlice s i z)
  have hac (k : ℕ) (hk : k≤3) := ChiExtension.fineTerm_jet_contraction s i
    (outerFineData m M D d c θ hc hβ hθ) z k hk
  have ha1 : ‖iteratedFDeriv ℝ 1 (outerFineNormal m M D d c θ hc hβ hθ s i) z‖≤6*C*B^(d+2)*ℓ*β^2 := by
    apply ((hac 1 (by norm_num)).trans ha0.1).trans
    gcongr
  have ha2 : ‖iteratedFDeriv ℝ 2 (outerFineNormal m M D d c θ hc hβ hθ s i) z‖≤12*C*B^(d+2)*ℓ*β*Real.sqrt θ/c := by
    apply ((hac 2 (by norm_num)).trans ha0.2.1).trans
    gcongr
  have ha3 : ‖iteratedFDeriv ℝ 3 (outerFineNormal m M D d c θ hc hβ hθ s i) z‖≤24*C*B^(d+2)*ℓ*θ/c^2 := by
    apply ((hac 3 (by norm_num)).trans ha0.2.2).trans
    gcongr
  have hs0 := hs E F n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V
    d m c θ hc hcs hθ s i z
  have hs1 : ‖iteratedFDeriv ℝ 1 (outerSignalNormal m M D d c θ s i) z‖≤2*C*B^(d+2)*ℓ*β^2 := by
    apply hs0.1.trans
    change 2*C*Bs^(d+2)*ℓ*β*W≤_
    calc
      _ ≤ 2*C*B^(d+2)*ℓ*β*β := by gcongr
      _ = _ := by ring
  have hs2 : ‖iteratedFDeriv ℝ 2 (outerSignalNormal m M D d c θ s i) z‖≤11*C*B^(d+2)*ℓ*β*Real.sqrt θ/c := by
    apply hs0.2.1.trans
    calc
      _ ≤ 11*C*B^(d+2)*ℓ*β := by gcongr
      _ ≤ 11*C*B^(d+2)*ℓ*β*Real.sqrt θ/c := by
        have hh := mul_le_mul_of_nonneg_left hunit (show 0≤11*C*B^(d+2)*ℓ*β by positivity)
        simpa only [mul_one,mul_div_assoc] using hh
  have hs3 : ‖iteratedFDeriv ℝ 3 (outerSignalNormal m M D d c θ s i) z‖≤92*C*B^(d+2)*ℓ*θ/c^2 := by
    apply hs0.2.2.trans
    change 92*C*Bs^(d+2)*ℓ*β/W≤_
    calc
      _ ≤ 92*C*B^(d+2)*ℓ*β/W := by gcongr
      _ ≤ 92*C*B^(d+2)*ℓ*θ/c^2 := by
        have hh := mul_le_mul_of_nonneg_left hratio' (show 0≤92*C*B^(d+2)*ℓ by positivity)
        simpa only [mul_div_assoc] using hh
  have hsub (k : ℕ) (hk : k≤3) := ZeroChainResidualBounds.jet_sub_norm_le
    (outerFineNormal_contDiff m M D d c θ hc hβ hθ s i)
    (outerSignalNormal_contDiff m M D d c θ hc hβ hθ s i) z k hk
  refine ⟨(hsub 1 (by norm_num)).trans ((add_le_add ha1 hs1).trans_eq (by ring)),
    (hsub 2 (by norm_num)).trans ((add_le_add ha2 hs2).trans_eq (by ring)),
    (hsub 3 (by norm_num)).trans ((add_le_add ha3 hs3).trans_eq (by ring))⟩

end Bilevel.ChiOuter
