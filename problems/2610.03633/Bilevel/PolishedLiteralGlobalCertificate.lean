import Bilevel.PolishedLiteralGlobal
import Bilevel.PolishedLiteralMicroMean

/-! The manuscript's numerical global macro--micro margin for its actual
finite mean. The positive receiver, release, chain, floors, radial maps,
active-index reduction, and both Euclidean gradient comparisons are proved
from the displayed functions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain ZeroChainPotential RadialWrapper

namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- The source's displayed parameter choices, without any derivative or
margin premise. The index convention is S=n+1 and M=microDimension+1. -/
structure SourceCalibration (P : Parameters (X:=X) (U:=U)) (Km A Cu ζ κ : ℝ) : Prop where
  macroEll : P.macroNode.ell=P.L
  macroRadial : P.macroRadial=P.L/24
  macroRadius : P.macroNode.radius=Km*P.macroNode.width*Real.sqrt ((P.macroNode.n:ℝ)+1)
  microDimension : P.n=Nat.floor (ζ^6*κ^2)-1
  microWidth : P.β=P.macroNode.width/κ
  microRadial : P.ν=ζ*P.L
  microRadius : P.radius=Cu*P.macroNode.width/ζ
  receiver : P.receiver=A
  force : P.force=P.L*(P.macroNode.width/κ)

end Parameters

/-- Source theorem `thm:global`, with universal numerical constants and the
source's explicit choices recorded by SourceCalibration. The hypothesis is
only the manuscript's terminal macro-coordinate condition. -/
theorem literal_global_certificate :
    ∃ Km A Cu ζ κ₀ cstar : ℝ,
      0<Km ∧ 0<A ∧ 0<Cu ∧ 0<ζ ∧ ζ≤1 ∧ 4≤κ₀ ∧ 0<cstar ∧ 1≤Km ∧ 1≤Cu ∧ 2/ζ^3≤κ₀ ∧
      ∀ κ : ℝ,κ₀≤κ →
      ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
        [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
        (P : Parameters (X:=X) (U:=U)),
        P.SourceCalibration Km A Cu ζ κ → 0<P.L → 0<P.macroNode.width →
        ∀ (x : X) (v : U),
          P.macroNode.coordinates x (Fin.last P.macroNode.n)<P.macroNode.width →
          cstar*(P.L*P.macroNode.width)≤‖gradient (P.outerMean κ) (pack x v)‖ := by
  obtain ⟨Km,hKm1,hmacro⟩ := numerical_macro_endgame_with_radius
  have hKm : 0<Km := lt_of_lt_of_le zero_lt_one hKm1
  obtain ⟨Cs,Cr,hCs,hCr,henvelopes⟩ := constructed_literal_derivative_envelopes
  let B := literalControl (Cr+Cs)
  have hB : 0≤B := (literalControl_bounds (add_nonneg hCr hCs)).1
  let wstar := descentThreshold B
  let γ := releaseTolerance B
  have hws : 0<wstar := (descentThreshold_range hB).1
  have hγ : 0<γ := (descentThreshold_range hB).2.2
  have hRcoef : 0≤Real.exp 1*gaussianBound := mul_nonneg (Real.exp_pos _).le gaussianBound_nonneg
  obtain ⟨A,Cu,hA,hCu1,hmicro⟩ := parametric_micro_endgame_with_radius (Real.exp 1*gaussianBound) wstar hRcoef hws
  have hCu : 0<Cu := lt_of_lt_of_le zero_lt_one hCu1
  obtain ⟨C,hC,hchain⟩ := chain_value_control
  obtain ⟨ζ,κv,hζ,hζ1,hζw,hκv,hκvscale,hpayload⟩ := payload_parameters C Cu A wstar γ hC hCu hA hws hγ
  obtain ⟨κm,hκm,hκmscale,hmicro⟩ := hmicro ζ hζ hζ1 hζw
  let κ₀ := max κv κm
  let cu := min wstar 1/2
  let cstar := min (1/4) cu
  have hcu : 0<cu := div_pos (lt_min hws zero_lt_one) (by norm_num)
  have hcstar : 0<cstar := lt_min (by norm_num) hcu
  refine ⟨Km,A,Cu,ζ,κ₀,cstar,hKm,hA,hCu,hζ,hζ1,hκv.trans (le_max_left _ _),hcstar,hKm1,hCu1,hκvscale.trans (le_max_left _ _),?_⟩
  intro κ hκ X U _ _ _ _ _ _ P hcal hL hb x v hlast
  have hκv' : κv≤κ := (le_max_left _ _).trans hκ
  have hκm' : κm≤κ := (le_max_right _ _).trans hκ
  have hκ4 : 4≤κ := hκv.trans hκv'
  have hκpos : 0<κ := by linarith
  have hell : 0≤P.macroNode.ell := by rw [hcal.macroEll];exact hL.le
  have hs : 0<Real.sqrt ((P.macroNode.n:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  have hRm : 0<P.macroNode.radius := by rw [hcal.macroRadius];positivity
  have hRu : 0<P.radius := by rw [hcal.microRadius];positivity
  have hgeom := micro_floor_geometry hζ hζ1 hκ4 (hκvscale.trans hκv')
  let M := Nat.floor (ζ^6*κ^2)
  have hcount : ((P.n:ℝ)+1)=(M:ℝ) := by
    rw [hcal.microDimension]
    exact_mod_cast Nat.sub_add_cancel hgeom.1
  have hsize : Real.sqrt ((P.n:ℝ)+1)≤ζ^3*κ := by
    apply (Real.sqrt_le_left (by positivity : 0≤ζ^3*κ)).mpr
    rw [hcount]
    have ht : (M:ℝ)≤ζ^6*κ^2 := Nat.floor_le (by positivity)
    nlinarith only [ht]
  have hsizeκ : Real.sqrt ((P.n:ℝ)+1)≤κ := by
    rw [hcal.microDimension]
    exact hgeom.2
  obtain ⟨hδ,hδsmall⟩ := hpayload κ hκv'
  let δ := payloadTolerance C Cu A ζ κ
  have hW (i : Fin (P.macroNode.n+1)) :
      |P.microCore i (κ • v)|≤δ*(P.macroNode.ell*P.macroNode.width^2) := by
    have ht := wrapped_micro_value_bound C hC hchain P.n P.L P.macroNode.width κ ζ Cu A
      hL hb hκpos hζ hCu hA.le hsize (P.frames i) (κ • v)
    simpa only [Parameters.microCore,Parameters.coordinates,Parameters.terminal,
      hcal.microWidth,hcal.microRadial,hcal.microRadius,hcal.receiver,hcal.force,
      hcal.macroEll,payloadTolerance,δ] using ht
  have hm : (P.macroNode.ell*P.macroNode.width)/2≤
      ‖fderiv ℝ (macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial
        P.macroNode.radius P.macroNode.frame) x‖ := by
    have ht := hmacro P.macroNode.n P.L P.macroNode.width hL hb X P.macroNode.frame x
    have htlast : WrappedChain.coordinates P.macroNode.n
        (Km*P.macroNode.width*Real.sqrt ((P.macroNode.n:ℝ)+1)) P.macroNode.frame x
        (Fin.last P.macroNode.n)<P.macroNode.width := by
      simpa only [Node.coordinates,hcal.macroRadius] using hlast
    have ht' := ht htlast
    rw [GradientJetBounds.gradient_norm_eq] at ht'
    simpa only [hcal.macroEll,hcal.macroRadial,hcal.macroRadius] using ht'
  have hs' (i : Fin (P.macroNode.n+1)) :=
    (henvelopes X P.macroNode hell hb hRm i x).1
  have hr' (i : Fin (P.macroNode.n+1)) :=
    (henvelopes X P.macroNode hell hb hRm i x).2
  have hsplit := P.meanBase_stop_or_descend Cs Cr δ hCs hCr hδ hδsmall hell hb hRm x (κ • v) hs' hr' hW hm
  have hE : 0≤P.L*P.macroNode.width := mul_nonneg hL.le hb.le
  rcases hsplit with hstop|⟨i,hi,hQ⟩
  · have hpartial : (P.L*P.macroNode.width)/4≤
        ‖gradient (fun y => P.outerMean κ (pack y v)) x‖ := by
      rw [GradientJetBounds.gradient_norm_eq]
      simpa only [Parameters.outerMean,hcal.macroEll] using hstop
    have hc := mul_le_mul_of_nonneg_right (min_le_left (1/4:ℝ) cu) hE
    exact (by nlinarith only [hc,hpartial] : cstar*(P.L*P.macroNode.width)≤
      ‖gradient (fun y => P.outerMean κ (pack y v)) x‖).trans (P.outerMean_x_norm_le κ x v)
  · have hi0 : wrappedSelector P.macroNode i x≠0 := ne_of_gt (hws.trans hi)
    have hcoeff := P.actual_residual_coefficient_bound hL.le hcal.macroEll x i
    have hweight := (wrappedSelector_range P.macroNode i x).2
    have hmic := hmicro P.n P.L P.macroNode.width κ
      (wrappedSelector P.macroNode i x) (wrappedResidual P.macroNode i x)
      hL hb hκm' hsizeκ hi.le hweight hcoeff.1 hcoeff.2 U (P.frames i) (κ • v)
    have hQ' : releaseGate (WrappedChain.coordinates P.n (Cu*P.macroNode.width/ζ)
        (P.frames i) (κ • v) (Fin.last P.n)/P.macroNode.width)<1 := by
      simpa only [Parameters.microRelease,Parameters.terminal,Parameters.coordinates,hcal.microRadius] using hQ
    have hmicrograd := hmic hQ'
    have hnorm : ‖gradient (fun u => P.meanBase (pack x u)) (κ • v)‖=
        ‖gradient (microAttached P.n P.L (P.macroNode.width/κ) A (ζ*P.L)
          (P.L*(P.macroNode.width/κ)) P.macroNode.width (wrappedSelector P.macroNode i x)
          (wrappedResidual P.macroNode i x) (Cu*P.macroNode.width/ζ) (P.frames i)) (κ • v)‖ := by
      rw [P.meanBase_u_gradient_eq hRu x i hi0]
      rw [hcal.microWidth,hcal.microRadial,hcal.microRadius,hcal.receiver,hcal.force]
    rw [← hnorm] at hmicrograd
    have hscaled := mul_le_mul_of_nonneg_left hmicrograd hκpos.le
    have hscale : κ*(min wstar 1*(P.L*(P.macroNode.width/κ))/2)=cu*(P.L*P.macroNode.width) := by
      dsimp only [cu]
      field_simp
      ring
    rw [hscale] at hscaled
    have hgn := P.outerMean_u_gradient_norm κ x v
    rw [abs_of_pos hκpos] at hgn
    rw [← hgn] at hscaled
    have hc := mul_le_mul_of_nonneg_right (min_le_right (1/4:ℝ) cu) hE
    exact (hc.trans hscaled).trans (P.outerMean_u_norm_le κ x v)

end Bilevel.PolishedLiteral
