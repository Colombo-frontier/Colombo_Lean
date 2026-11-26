import Bilevel.PartialLegendreStrongConvex
import Bilevel.PrimitiveGeometry

/-! Exact primal response from the dual normal-zero trace. The tangential
derivative vanishes because the actual scalar trace vanishes identically;
normal linearity away from zero is not required. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (P : Joint U V → ℝ) (G : Joint U V → Joint U V)
  (hP : ∀ z,HasGradientAt P (G z) z)
  (htrace : ∀ p, P (pack p (0:V))=0)
include hP htrace

theorem trace_first_gradient_zero (p : U) : (G (pack p (0:V))).fst=0 := by
  have hp := PrimitiveGeometry.partial_x (f := P)
    (gx := (G (pack p (0:V))).fst) (gy := (G (pack p (0:V))).snd) (x := p) (y := (0:V)) (hP _)
  have he : (fun p : U => P (pack p (0:V))) = fun _ => (0:ℝ) := funext htrace
  rw [he] at hp
  exact hp.unique (hasGradientAt_const p (0:ℝ))

theorem trace_graph (t : U → V) (ht : ∀ p,(G (pack p (0:V))).snd=t p) (p : U) :
    pack p (0:V)+G (pack p (0:V))=pack p (t p) := by
  change pack (p+(G (pack p (0:V))).fst) (0+(G (pack p (0:V))).snd)=pack p (t p)
  rw [trace_first_gradient_zero P G hP htrace p,ht,add_zero,zero_add]

variable {δ : NNReal} (hδ : δ < 1) (hG : LipschitzWith δ G)

omit hP htrace in
def normalResponse (m c : ℝ) (v : U) (t : U → V) : Joint U V :=
  pack ((c/m) • v) (t ((c/m) • v))

omit hP htrace in
def normalLower (m c : ℝ) (v : U) (y : Joint U V) : ℝ :=
  coupledLower hδ hG P m (pack (c • v) (0:V)) y

omit hP htrace in
theorem normalLower_formula (m c : ℝ) (v : U) (y : Joint U V) :
    normalLower P G hδ hG m c v y = m*conjugate hδ hG P y-c*⟪v,y.fst⟫ := by
  unfold normalLower coupledLower
  rw [WithLp.prod_inner_apply]
  change _- (⟪c • v,y.fst⟫+⟪(0:V),y.snd⟫)=_
  rw [real_inner_smul_left,inner_zero_left,add_zero]

omit hP htrace [CompleteSpace U] [CompleteSpace V] in
theorem scaled_target {m : ℝ} (hm : m ≠ 0) (c : ℝ) (v : U) :
    m • pack ((c/m) • v) (0:V)=pack (c • v) (0:V) := by
  change pack (m • ((c/m) • v)) (m • (0:V))=pack (c • v) (0:V)
  rw [smul_smul,smul_zero,show m*(c/m)=c by field_simp]

theorem normalLower_unique_response {m : ℝ} (hm : 0 < m) (c : ℝ) (v : U)
    (t : U → V) (ht : ∀ p,(G (pack p (0:V))).snd=t p) (y : Joint U V) :
    (∀ w,normalLower P G hδ hG m c v y ≤ normalLower P G hδ hG m c v w) ↔
      y=normalResponse m c v t := by
  have hh := coupledLower_unique hδ hG P hP hm (pack ((c/m) • v) (0:V)) y
  rw [scaled_target hm.ne' c v,trace_graph P G hP htrace t ht] at hh
  exact hh

theorem normalLower_response_minimizes {m : ℝ} (hm : 0 < m) (c : ℝ) (v : U)
    (t : U → V) (ht : ∀ p,(G (pack p (0:V))).snd=t p) (y : Joint U V) :
    normalLower P G hδ hG m c v (normalResponse m c v t) ≤ normalLower P G hδ hG m c v y :=
  (normalLower_unique_response P G hP htrace hδ hG hm c v t ht _).mpr rfl y

end Bilevel.PartialLegendre
