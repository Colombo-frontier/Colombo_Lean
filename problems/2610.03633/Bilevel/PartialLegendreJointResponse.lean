import Bilevel.PartialLegendreJoint
import Bilevel.PartialLegendreNormalTrace

/-! The source's exact lower response, with all outer parameters retained.
Only the dual normal-zero trace is used, even though the primal normal
response need not be zero or inside a linearity interval. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {δ : NNReal} {G : Joint X (Joint U V) → Joint X (Joint U V)}
  (hG : LipschitzWith δ G) (hδ : δ<1) (P : Joint X (Joint U V) → ℝ)

def jointNormalLower (m c : ℝ) (x : X) (v : U) (y : Joint U V) : ℝ :=
  m*jointConjugate hG hδ P (pack x y)-c*⟪v,y.fst⟫

omit [CompleteSpace X] in
theorem jointNormalLower_slice (m c : ℝ) (x : X) (v : U) (y : Joint U V) :
    jointNormalLower hG hδ P m c x v y=
      normalLower (fun z => P (pack x z)) (fun z => (G (pack x z)).snd)
        hδ (jointSlice_lipschitz hG x) m c v y := by
  rw [normalLower_formula]
  rfl

variable (hP : ∀ q,HasGradientAt P (G q) q)
  (htrace : ∀ x p,P (pack x (pack p (0:V)))=0)
  (t : X → U → V) (ht : ∀ x p,(G (pack x (pack p (0:V)))).snd.snd=t x p)
include hP htrace ht

theorem jointNormalLower_unique_response {m : ℝ} (hm : 0<m) (c : ℝ)
    (x : X) (v : U) (y : Joint U V) :
    (∀ w,jointNormalLower hG hδ P m c x v y≤jointNormalLower hG hδ P m c x v w) ↔
      y=pack ((c/m) • v) (t x ((c/m) • v)) := by
  simp only [jointNormalLower_slice]
  exact normalLower_unique_response (fun z => P (pack x z))
    (fun z => (G (pack x z)).snd) (jointSlice_hasGradientAt P hP x) (htrace x)
    hδ (jointSlice_lipschitz hG x) hm c v (t x) (ht x) y

theorem jointNormalLower_response_minimizes {m : ℝ} (hm : 0<m) (c : ℝ)
    (x : X) (v : U) (y : Joint U V) :
    jointNormalLower hG hδ P m c x v (pack ((c/m) • v) (t x ((c/m) • v)))≤
      jointNormalLower hG hδ P m c x v y :=
  (jointNormalLower_unique_response hG hδ P hP htrace t ht hm c x v _).mpr rfl y

theorem jointNormalLower_response_growth {m : ℝ} (hm : 0<m) (c : ℝ)
    (x : X) (v : U) (y : Joint U V) :
    m/(2*(1+(δ:ℝ)))*‖y-pack ((c/m) • v) (t x ((c/m) • v))‖^2≤
      jointNormalLower hG hδ P m c x v y-
        jointNormalLower hG hδ P m c x v (pack ((c/m) • v) (t x ((c/m) • v))) := by
  have hh := coupledLower_growth hδ (jointSlice_lipschitz hG x) (fun z => P (pack x z))
    (jointSlice_hasGradientAt P hP x) hm (pack ((c/m) • v) (0:V)) y
  rw [scaled_target hm.ne' c v,
    trace_graph (fun z => P (pack x z)) (fun z => (G (pack x z)).snd)
      (jointSlice_hasGradientAt P hP x) (htrace x) (t x) (ht x)] at hh
  simpa only [jointNormalLower_slice,normalLower] using hh

end Bilevel.PartialLegendre
