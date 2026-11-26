import Bilevel.PolishedLiteralUpperAssembly
import Bilevel.PolishedLiteralGlobalCertificate

/-! Source-calibrated budgets for the literal upper base and exact mean
base. Every derivative estimate is derived from the actual functions. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain RadialWrapper

theorem source_base_budgets :
    ∀ (Km A Cu ζ : ℝ),1≤Km → 0≤A → 1≤Cu → 0<ζ → ζ≤1 →
    ∃ C : ℝ,0≤C ∧
    ∀ (κ : ℝ),4≤κ → 2/ζ^3≤κ →
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)),P.SourceCalibration Km A Cu ζ κ →
      0<P.L → 0<P.macroNode.width →
      (∀ z,‖iteratedFDeriv ℝ 2 P.meanBase z‖≤C*P.L) ∧
      (∀ z,‖iteratedFDeriv ℝ 2 P.upperBase z‖≤C*P.L) ∧
      (∀ x u,‖gradient (fun v => P.upperBase (pack x v)) u‖≤C*P.L*P.macroNode.width) := by
  intro Km A Cu ζ hKm hA hCu hζ hζ1
  obtain ⟨B,hB,hbase⟩ := lowerBase_first_second
  obtain ⟨Cg,Ch,hCg,hCh,hmacro⟩ := Regularity.macro_jet_two_uniform
  obtain ⟨Cr,hCr,hres⟩ := selected_residual_joint_jet_bounds
  let Crad := Cu/ζ
  let Cm := Ch+4*Cg/Km+1/24
  let C := Cm+1+B A Crad+Cr+Cu+1
  have hKm0 : 0<Km := by linarith
  have hCu0 : 0<Cu := by linarith
  have hCrad : 0≤Crad := div_nonneg hCu0.le hζ.le
  have hCm : 0≤Cm := by dsimp [Cm];positivity
  have hBB := hB A Crad hA hCrad
  have hCr0 : 0≤Cr := by linarith
  have hC : 0≤C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro κ hκ hκscale X U _ _ _ _ _ _ P hcal hL hb
  have hk : 0<κ := by linarith
  have hβ : 0<P.β := by rw [hcal.microWidth];positivity
  have hβb : P.β≤P.macroNode.width := by
    rw [hcal.microWidth]
    exact (div_le_self hb.le (by linarith))
  have hν : 0≤P.ν := by rw [hcal.microRadial];positivity
  have hνL : P.ν≤P.L := by rw [hcal.microRadial];nlinarith only [mul_le_mul_of_nonneg_right hζ1 hL.le]
  have hA' : 0≤P.receiver := by rw [hcal.receiver];exact hA
  have hf : P.force=P.L*P.β := by rw [hcal.force,hcal.microWidth]
  have hbR : P.macroNode.width≤P.radius := by
    rw [hcal.microRadius]
    apply (le_div_iff₀ hζ).mpr
    have hζCu : ζ≤Cu := hζ1.trans hCu
    nlinarith only [mul_le_mul_of_nonneg_right hζCu hb.le]
  have hRb : P.radius≤Crad*P.macroNode.width := by
    rw [hcal.microRadius]
    dsimp [Crad]
    apply le_of_eq
    ring
  have hRm : P.macroNode.width≤P.macroNode.radius := by
    rw [hcal.macroRadius]
    have hs : 1≤Real.sqrt ((P.macroNode.n:ℝ)+1) := Real.one_le_sqrt.2 (by
      have hn : (0:ℝ)≤P.macroNode.n := Nat.cast_nonneg _
      linarith)
    have hh : 1≤Km*Real.sqrt ((P.macroNode.n:ℝ)+1) := one_le_mul_of_one_le_of_one_le hKm hs
    nlinarith only [mul_le_mul_of_nonneg_left hh hb.le]
  have hwidth : P.β*Real.sqrt ((P.n:ℝ)+1)≤P.macroNode.width := by
    have hgeom := (micro_floor_geometry hζ hζ1 hκ hκscale).2
    rw [← hcal.microDimension] at hgeom
    rw [hcal.microWidth]
    have ht := mul_le_mul_of_nonneg_left hgeom (div_nonneg hb.le hk.le)
    have he : P.macroNode.width/κ*κ=P.macroNode.width := div_mul_cancel₀ _ hk.ne'
    exact ht.trans_eq he
  have hlo := hbase X U P Crad hL hβ hA' hν hνL hf hcal.macroEll hβb hbR hRb hCrad hRm hwidth
  have hres' := hres X U P hL.le hβ (hβb.trans hbR) hβb hRm
  have hm (x : X) : ‖iteratedFDeriv ℝ 2
      (macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial
        P.macroNode.radius P.macroNode.frame) x‖≤Cm*P.L := by
    have ht := hmacro X P.macroNode.n P.L P.macroNode.width Km hL.le hb hKm0 P.macroNode.frame x
    simpa only [hcal.macroEll,hcal.macroRadial,hcal.macroRadius,Cm] using ht
  have hmean (z : Joint X U) : ‖iteratedFDeriv ℝ 2 P.meanBase z‖≤(Cm+1+B A Crad)*P.L := by
    have he : P.meanBase=fun y =>
        macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial P.macroNode.radius P.macroNode.frame y.fst+
          P.lowerBase y := funext P.meanBase_eq
    have h23 : (2:WithTop ℕ∞)≤3 := by exact_mod_cast (show (2:ℕ)≤3 by omega)
    rw [he]
    change ‖iteratedFDeriv ℝ 2 (fun y =>
      (macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial P.macroNode.radius P.macroNode.frame ∘
        fstMap (X:=X) (U:=U)) y+P.lowerBase y) z‖≤_
    rw [iteratedFDeriv_add_apply'
      ((((macro_contDiff P.macroNode P.macroRadial 3).comp (fstMap (X:=X) (U:=U)).contDiff).of_le h23).contDiffAt)
      ((P.lowerBase_contDiff.of_le h23).contDiffAt)]
    have hc := (ChiOuter.contraction_jet_bound (fstMap (X:=X) (U:=U)) fstMap_norm_le
      (macro_contDiff P.macroNode P.macroRadial 3) z 2 (by norm_num)).trans (hm z.fst)
    have ht := (norm_add_le _ _).trans (add_le_add hc (hlo z).2)
    rw [hcal.receiver] at ht
    nlinarith only [ht,hνL]
  have hu (z : Joint X U) : ‖iteratedFDeriv ℝ 2 P.upperBase z‖≤(Cm+1+B A Crad+Cr)*P.L := by
    have he : P.upperBase=fun y => P.meanBase y-P.selectedResidual y := by
      funext y
      have ht := P.exact_cancellation y
      linarith
    rw [he]
    have hr2 : ‖iteratedFDeriv ℝ 2 P.selectedResidual z‖≤Cr*P.L := by
      have ht := hres' z 2 (by norm_num)
      convert ht using 1
      field_simp [hβ.ne']
    exact (ZeroChainResidualBounds.jet_sub_norm_le P.meanBase_contDiff P.selectedResidual_contDiff z 2 (by norm_num)).trans
      ((add_le_add (hmean z) hr2).trans_eq (by ring))
  have hy (x : X) (u : U) : ‖gradient (fun v => P.upperBase (pack x v)) u‖≤
      (Cu+B A Crad+Cr)*P.L*P.macroNode.width := by
    let H : Joint X U → ℝ := fun z => P.lowerBase z-P.selectedResidual z
    have hH : ContDiff ℝ 3 H := P.lowerBase_contDiff.sub P.selectedResidual_contDiff
    have hr1 : ‖iteratedFDeriv ℝ 1 P.selectedResidual (pack x u)‖≤Cr*P.L*P.macroNode.width := by
      have ht := hres' (pack x u) 1 (by norm_num)
      have he : Cr*P.L*P.β^2/P.β^1=Cr*P.L*P.β := by field_simp;ring
      rw [he] at ht
      exact ht.trans (mul_le_mul_of_nonneg_left hβb (by positivity))
    have hh : ‖gradient H (pack x u)‖≤(Cu+B A Crad+Cr)*P.L*P.macroNode.width := by
      rw [GradientJetBounds.gradient_norm_eq,← Composition.norm_first]
      change ‖iteratedFDeriv ℝ 1 (fun z => P.lowerBase z-P.selectedResidual z) (pack x u)‖≤_
      have ht := (ZeroChainResidualBounds.jet_sub_norm_le P.lowerBase_contDiff P.selectedResidual_contDiff
        (pack x u) 1 (by norm_num)).trans (add_le_add (hlo (pack x u)).1 hr1)
      rw [hcal.receiver,hcal.microRadial,hcal.microRadius] at ht
      have he : (ζ*P.L)*(Cu*P.macroNode.width/ζ)=Cu*P.L*P.macroNode.width := by field_simp;ring
      rw [he] at ht
      nlinarith only [ht]
    have he : (fun v => P.upperBase (pack x v))=fun v =>
        macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial P.macroNode.radius P.macroNode.frame x+
          H (pack x v) := by
      funext v
      have hm := P.meanBase_eq (pack x v)
      have hc := P.exact_cancellation (pack x v)
      change P.meanBase (pack x v)=
        macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial P.macroNode.radius P.macroNode.frame x+
          P.lowerBase (pack x v) at hm
      dsimp only [H]
      linarith
    have hg := ((hH.differentiable (by norm_num)) (pack x u)).hasGradientAt
    have hp := PrimitiveGeometry.partial_y hg
    rw [he,← norm_fderiv_eq_norm_gradient,fderiv_const_add,norm_fderiv_eq_norm_gradient,hp.gradient]
    exact (WithLp.norm_snd_le X (gradient H (pack x u))).trans hh
  refine ⟨fun z => (hmean z).trans ?_,fun z => (hu z).trans ?_,fun x u => (hy x u).trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hL.le
    dsimp [C]
    linarith
  · apply mul_le_mul_of_nonneg_right _ hL.le
    dsimp [C]
    linarith
  · apply mul_le_mul_of_nonneg_right _ hb.le
    apply mul_le_mul_of_nonneg_right _ hL.le
    dsimp [C]
    linarith

end Bilevel.PolishedLiteral
