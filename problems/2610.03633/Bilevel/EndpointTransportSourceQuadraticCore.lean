import Bilevel.EndpointTransportQuadraticCore

/-! Actual depth-zero exact-quadratic upper budgets. The macro release and
leaf payload use the physical endpoints, and the public bowl is gamma-scaled. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter

set_option maxHeartbeats 1000000 in
theorem source_quadratic_core_budgets (A K ζ cn CR Km : ℝ) (hA : 0≤A) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km) :
    ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n dim nM : ℕ) (Q : Rotations n dim) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ),(∀ j,1≤r j) → r 0=1 → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) →
      ∀ (U : Space nM →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block dim),
      let M := sourceMacroNode nM initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      let ρ := b 0*(ζ*initial.curvature)
      let R := (D 0 []).radius
      ∀ z : Joint E (Physical n dim),
      ‖iteratedFDeriv ℝ 2 (quadraticCore Q M (initial.curvature/24) D ρ R) z‖≤C*initial.curvature ∧
      ‖gradient (fun v => quadraticCore Q M (initial.curvature/24) D ρ R (pack z.fst v)) z.snd‖≤C*initial.force := by
  obtain ⟨Cg,Ch,hCg,hCh,hmacro⟩ := Regularity.macro_jet_two_uniform
  obtain ⟨Cc,hCc,hcarrier⟩ := source_outer_physical_ledger A K ζ cn hA hK hζ hζ1 hcn hcn1
  obtain ⟨Cr,hCr,hcorrection⟩ := physical_macro_release_correction_jets
  let Cm := Ch+4*Cg/Km+1/24
  let C := 1+Cm+Cr+Cc^2+CR
  have hKm0 : 0<Km := by linarith
  have hCR0 : 0<CR := by linarith
  have hCm : 0≤Cm := by dsimp [Cm];positivity
  have hCc0 : 0≤Cc := by linarith
  have hCr0 : 0≤Cr := by linarith
  have hC : 1≤C := by dsimp only [C];nlinarith only [hCm,hCr,hCR,sq_nonneg Cc]
  refine ⟨C,hC,fun E _ _ _ n dim nM Q initial hl hw r η b hr hr0 hη hη1 hlen hb hb1 U V => ?_⟩
  dsimp only
  let M := sourceMacroNode nM initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  let ρ := b 0*(ζ*initial.curvature)
  let R := (D 0 []).radius
  have hMrad : M.width≤M.radius := sourceMacro_radius_ge_width hw hKm U
  have hnode (I : List ℕ) :
      0≤(D 0 I).ell ∧ 0<(D 0 I).width ∧ (D 0 I).width≤(D 0 I).radius ∧
      0<(D 0 I).parentWidth ∧ (D 0 I).parentWidth≤(D 0 I).radius :=
    sourceNode_admissible A K ζ cn (η 0) CR _ _ (r 0) (b 0) (V 0 I)
      hK hζ hζ1 (hη 0) (hη1 0) hCR hl hw (hr 0) (hb 0) (hb1 0)
  have hell : (D 0 []).ell=initial.curvature := by
    change r 0*initial.curvature=_
    rw [hr0,one_mul]
  have hwidth : (D 0 []).width*Real.sqrt (((D 0 []).n:ℝ)+1) ≤ initial.width :=
    source_width_sqrt_length_le_parent hcn hcn1 (hη 0) hw (hr 0) (hlen 0)
  have hρ : 0≤ρ := mul_nonneg (hb 0).le (mul_nonneg hζ.le hl.le)
  have hρle : ρ ≤ initial.curvature := by
    have hh := mul_le_mul (hb1 0) hζ1 hζ.le zero_le_one
    have hm := mul_le_mul_of_nonneg_right hh hl.le
    dsimp only [ρ]
    nlinarith only [hm]
  have hR : 0<R := (hnode []).2.1.trans_le (hnode []).2.2.1
  have hρR : ρ*R=CR*initial.force := by
    change (b 0*(ζ*initial.curvature))*
      (CR*(initial.curvature*initial.width)*Real.sqrt (r 0)/(b 0*(ζ*initial.curvature)))=CR*initial.force
    rw [hr0,Real.sqrt_one]
    unfold Scale.force
    field_simp [(hb 0).ne',hζ.ne',hl.ne']
  intro z
  let P : Joint E (Physical n dim) →L[ℝ] E := PartialLegendre.jointFstLinear
  let B : Joint E (Physical n dim) →L[ℝ] Physical n dim := PartialLegendre.jointSndLinear
  have hc := hcarrier E (Joint E (Physical n dim)) n dim nM Q initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
    0 P 0 B ChiPrimitive.jointFstLinear_norm (by simp) ChiPrimitive.jointSndLinear_norm
  have hcor := hcorrection E (Joint E (Physical n dim)) n dim M (fun i => D 0 [i.val]) hl.le hw hMrad
    (fun i => hnode [i.val]) (fun _ => rfl) P B ChiPrimitive.jointFstLinear_norm ChiPrimitive.jointSndLinear_norm Q z
  have hcor1 : ‖iteratedFDeriv ℝ 1 (physicalMacroReleaseCorrection M P (fun i => D 0 [i.val]) B Q) z‖≤Cr*initial.force := by
    have hh := hcor 1 (by norm_num)
    convert hh using 1
    change Cr*(initial.curvature*initial.width)=Cr*(initial.curvature*initial.width^2)/initial.width^1
    field_simp
    ring
  have hcor2 : ‖iteratedFDeriv ℝ 2 (physicalMacroReleaseCorrection M P (fun i => D 0 [i.val]) B Q) z‖≤Cr*initial.curvature := by
    have hh := hcor 2 (by norm_num)
    convert hh using 1
    change Cr*initial.curvature=Cr*(initial.curvature*initial.width^2)/initial.width^2
    field_simp
    ring
  have hcar1 : ‖iteratedFDeriv ℝ 1 (outerPhysicalCarrier 0 Q M P D 0 B 0 0) z‖≤Cc^2*initial.force := by
    have hh := hc 0 0 le_rfl z 1 (by norm_num)
    change ‖iteratedFDeriv ℝ 1 (outerPhysicalCarrier 0 Q M P D 0 B 0 0) z‖≤
      Cc^(0+2)*ledgerScale (((D 0 []).n:ℝ)+1) (D 0 []).ell (D 0 []).width 1 at hh
    simp only [zero_add,ledgerScale,hell] at hh
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left hwidth (mul_nonneg (sq_nonneg Cc) hl.le)
    unfold Scale.force
    nlinarith only [hm]
  have hcar2 : ‖iteratedFDeriv ℝ 2 (outerPhysicalCarrier 0 Q M P D 0 B 0 0) z‖≤Cc^2*initial.curvature := by
    have hh := hc 0 0 le_rfl z 2 (by norm_num)
    change ‖iteratedFDeriv ℝ 2 (outerPhysicalCarrier 0 Q M P D 0 B 0 0) z‖≤
      Cc^(0+2)*ledgerScale (((D 0 []).n:ℝ)+1) (D 0 []).ell (D 0 []).width 2 at hh
    simpa only [zero_add,ledgerScale,hell] using hh
  have hp := physical_scaled_bowl_jets ρ R hρ hR z
  have hp1 := hp.1
  rw [hρR] at hp1
  have hp2 := hp.2.trans hρle
  have hlow1 := quadraticCoreLower_jet_bound Q M D ρ R z 1 (by norm_num) _ _ _ hcor1 hcar1 hp1
  have hlow2 := quadraticCoreLower_jet_bound Q M D ρ R z 2 (by norm_num) _ _ _ hcor2 hcar2 hp2
  constructor
  · have hmacro' := hmacro E nM initial.curvature initial.width Km hl.le hw hKm0 U z.fst
    have hu := quadraticCore_second_bound Q M (initial.curvature/24) D ρ R z _ _ hmacro' hlow2
    apply hu.trans
    have hm := mul_nonneg hCR0.le hl.le
    change Cm*initial.curvature+(Cr*initial.curvature+Cc^2*initial.curvature+initial.curvature)≤C*initial.curvature
    dsimp only [C]
    nlinarith only [hm]
  · apply quadraticCore_lower_gradient_bound Q M (initial.curvature/24) D ρ R z.fst z.snd
    apply hlow1.trans
    have hm := mul_nonneg (show 0≤1+Cm by positivity) (show 0 ≤ initial.force by exact mul_nonneg hl.le hw.le)
    dsimp only [C]
    nlinarith only [hm]

end Bilevel.EndpointTransportResponse


