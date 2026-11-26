import Bilevel.PublicRadialThird

/-! Source-facing public radial extension, its exact normal trace, and the
displayed dimension-independent derivative budgets at every normal query. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PublicRadialExtension
open RadialWrapper PrimitiveGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem potential_jet_two_bound (a R : ℝ) (ha : 0≤a) (hR : 0<R)
    (e z : E) (he : ‖e‖≤1) : ‖iteratedFDeriv ℝ 2 (potential a R e) z‖≤3*a := by
  rw [← GradientJetBounds.hessian_norm_eq (potential_contDiff a R e 3) z]
  exact actual_hessian_norm_bound a R ha hR e z he

theorem potential_jet_three_bound (a R : ℝ) (ha : 0≤a) (hR : 0<R)
    (e z : E) (he : ‖e‖≤1) : ‖iteratedFDeriv ℝ 3 (potential a R e) z‖≤9*a/R := by
  rw [← GradientJetBounds.third_norm_eq (potential_contDiff a R e 3) z]
  rw [show fderiv ℝ (gradient (potential a R e))=hessianField a R e from
    funext (actual_hessian a R hR e)]
  exact actual_third_norm_bound a R ha hR e z he

def normalDirection : Joint E ℝ := pack 0 1

def radial (ν R d : ℝ) : Joint E ℝ → ℝ := potential (ν*R/d) R normalDirection

omit [CompleteSpace E] in
theorem normalDirection_norm : ‖(normalDirection : Joint E ℝ)‖=1 := by
  rw [normalDirection,norm_pack]
  norm_num

omit [CompleteSpace E] in
theorem normalDirection_inner (p : E) (t : ℝ) :
    ⟪normalDirection,pack p t⟫=t := by
  rw [WithLp.prod_inner_apply]
  change ⟪(0:E),p⟫+⟪(1:ℝ),t⟫=t
  simp

omit [CompleteSpace E] in
theorem radial_formula (ν R d : ℝ) (hR : 0<R) (p : E) (t : ℝ) :
    radial ν R d (pack p t)=(ν*R/d)*t*(Real.sqrt (R^2+‖p‖^2+t^2)-R) := by
  rw [radial,potential_formula _ R hR,normalDirection_inner,norm_sq]
  change (ν*R/d)*t*(Real.sqrt (R^2+(‖p‖^2+‖t‖^2))-R)= _
  simp only [Real.norm_eq_abs,sq_abs]
  congr 3
  ring

omit [CompleteSpace E] in
theorem radial_trace (ν R d : ℝ) (p : E) : radial ν R d (pack p 0)=0 := by
  simp only [radial,potential,normalDirection_inner,mul_zero,zero_mul]

theorem radial_normal_trace_gradient (ν R d : ℝ) (hR : 0<R) (p : E) :
    gradient (radial ν R d) (pack p 0)=
      pack (0:E) ((ν*R^2/d)*(Real.sqrt (1+‖p‖^2/R^2)-1)) := by
  rw [radial,potential_gradient _ R hR,gradientField,normalDirection_inner]
  simp only [mul_zero,zero_smul,add_zero]
  change pack ((((ν*R/d)/R)*bowl 1 R (pack p (0:ℝ))) • (0:E))
    ((((ν*R/d)/R)*bowl 1 R (pack p (0:ℝ))) • (1:ℝ))= _
  rw [smul_zero,smul_eq_mul,mul_one]
  congr 1
  have hc : (ν*R/d)/R=ν/d := by rw [div_right_comm,mul_div_cancel_right₀ ν hR.ne']
  have hb : bowl 1 R (pack p (0:ℝ))=R^2*(Real.sqrt (1+‖p‖^2/R^2)-1) := by
    unfold bowl
    rw [norm_sq]
    change 1*R^2*(Real.sqrt (1+(‖p‖^2+‖(0:ℝ)‖^2)/R^2)-1)= _
    simp
  rw [hc,hb]
  ring

def radialCoefficient (ν R d : ℝ) (p : E) (t : ℝ) : ℝ :=
  (ν/d)*t*scale R (pack p t)

theorem radial_tangential_gradient (ν R d : ℝ) (hR : 0<R) (p : E) (t : ℝ) :
    (gradient (radial ν R d) (pack p t)).fst=radialCoefficient ν R d p t • p := by
  rw [radial,potential_gradient _ R hR,gradientField,normalDirection_inner]
  change (((ν*R/d)/R)*bowl 1 R (pack p t)) • (0:E)+
    (((ν*R/d)/R)*t) • (scale R (pack p t) • p)= _
  rw [smul_zero,zero_add,smul_smul]
  congr 1
  unfold radialCoefficient
  rw [div_right_comm,mul_div_cancel_right₀ ν hR.ne']

omit [CompleteSpace E] in
theorem radialCoefficient_bound (ν R d : ℝ) (hν : 0≤ν) (hR : 0<R) (hd : 0<d)
    (p : E) (t : ℝ) : |radialCoefficient ν R d p t|≤ν*R/d := by
  have ht : |t|≤‖pack p t‖ := by
    simpa only [Real.norm_eq_abs] using WithLp.norm_snd_le E (pack p t)
  have hh := (mul_le_mul_of_nonneg_left ht (scale_pos R (pack p t)).le).trans
    (compressed_radius_bound R hR (pack p t))
  unfold radialCoefficient
  rw [abs_mul,abs_mul,abs_of_nonneg (div_nonneg hν hd.le),abs_of_pos (scale_pos R (pack p t))]
  have hb := mul_le_mul_of_nonneg_left hh (div_nonneg hν hd.le)
  convert hb using 1 <;> ring

theorem radial_jet_bounds (ν R d : ℝ) (hν : 0≤ν) (hR : 0<R) (hd : 0<d)
    (z : Joint E ℝ) :
    ‖iteratedFDeriv ℝ 2 (radial ν R d) z‖≤3*(ν*R/d) ∧
      ‖iteratedFDeriv ℝ 3 (radial ν R d) z‖≤9*ν/d := by
  have ha : 0≤ν*R/d := by positivity
  have he : ‖(normalDirection : Joint E ℝ)‖≤1 := normalDirection_norm.le
  constructor
  · exact potential_jet_two_bound _ R ha hR normalDirection z he
  · have hh := potential_jet_three_bound _ R ha hR normalDirection z he
    change ‖iteratedFDeriv ℝ 3 (radial ν R d) z‖≤9*(ν*R/d)/R at hh
    convert hh using 1
    field_simp
    ring

end Bilevel.PublicRadialExtension
