import Bilevel.ChiUpperRegularity
import Bilevel.ChiExtensionStrongConvex

/-! Actual admissible bilevel objectives, including an attained unique lower
response. The hypotheses are quantitative derivative budgets of the concrete
base and extension, subsequently supplied by source calibration. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre ChiPrimitive ChiUpper
open scoped RealInnerProductSpace
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem primitive_of_extension_jets
    (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (δ:ℝ)) (hδ : δ < 1)
    (hsmall : (δ:ℝ) ≤ 1/12) (hzero : ∀ p,f (pack p (0:V))=0)
    (μ L ρ : ℝ) (hμ : 0 < μ) (hμL : 2*μ ≤ L) (hρ : 0 ≤ ρ)
    (hthird : ∀ z,‖iteratedFDeriv ℝ 3 f z‖ ≤ ρ/(3*(3*μ/2)))
    (base : Joint X U → ℝ) (hbase : ContDiff ℝ 3 base)
    (hbase2 : ∀ z,‖iteratedFDeriv ℝ 2 base z‖ ≤ L)
    (hbase1 : ∀ x u,‖gradient (fun v => base (pack x v)) u‖ ≤ 3*L/4)
    (b : V) (hbN : ‖b‖ ≤ L/4) :
    ∃ P : Model.Primitive (X:=Joint X U) (Y:=Joint U V) μ L L L ρ,
      (∀ x y,P.f x y=base (pack x.fst y.fst)+⟪b,y.snd⟫) ∧
      (∀ x y,P.g x y=extensionLower f hf δ hb hδ (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,
        (∀ x,r.y x=pack ((L/(6*μ)) • x.snd) (normalTrace f x.fst ((L/(6*μ)) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=base (pack x.fst ((L/(6*μ)) • x.snd))+
          ⟪b,normalTrace f x.fst ((L/(6*μ)) • x.snd)⟫) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) := by
  have hL : 0 ≤ L := by linarith
  have hbaseD := hbase.differentiable (by norm_num)
  obtain ⟨K,hC,hD,_,hV,hG⟩ := fullExtensionLower_regular f hf δ hb hδ hsmall μ L ρ hμ hμL hρ hthird
  let lower := fullExtensionLower f hf δ hb hδ μ L
  let upper := fullUpper base b
  have hstrong : ∀ x y w,lower (pack x y)+⟪gradient (fun v => lower (pack x v)) y,w-y⟫+
      μ/2*‖w-y‖^2 ≤ lower (pack x w) := by
    intro x y w
    exact extensionLower_strong_convex f hf δ hb hδ hsmall hμ (L/4) x.fst x.snd y w
  have hupper : ∀ x y,‖gradient (fun v => upper (pack x v)) y‖ ≤ L := by
    intro x y
    exact (fullUpper_lower_bound base hbaseD b hbase1 x y).trans (by linarith)
  have hU := fullUpper_gradient_lipschitz base hbaseD b hL
    (GradientJetBounds.gradient_lipschitz hbase L hbase2)
  let P := fromFull upper lower (fullUpper_differentiable base hbaseD b)
    (hC.differentiable (by norm_num)) K hD μ L L L ρ hμ hL hL hL hρ hstrong hupper hU hG hV
  have he : (L/4)/(3*μ/2)=L/(6*μ) := by field_simp;ring
  let r : P.Response := {
    y := fun x => pack ((L/(6*μ)) • x.snd) (normalTrace f x.fst ((L/(6*μ)) • x.snd))
    minimizes := by
      intro x y
      change extensionLower f hf δ hb hδ (3*μ/2) (L/4) x.fst x.snd
        (pack ((L/(6*μ)) • x.snd) (normalTrace f x.fst ((L/(6*μ)) • x.snd))) ≤ _
      rw [← he]
      exact extensionLower_response_minimizes f hf δ hb hδ hzero (by positivity) (L/4) x.fst x.snd y }
  refine ⟨P,fun _ _ => rfl,fun _ _ => rfl,r,fun _ => rfl,fun _ => rfl,?_⟩
  intro x y
  constructor
  · intro hy
    exact P.lower_solution_unique x y (r.y x) hy (r.minimizes x)
  · rintro rfl
    exact r.minimizes x

end Bilevel.ChiExtension
