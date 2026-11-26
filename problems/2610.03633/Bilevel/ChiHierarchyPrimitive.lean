import Bilevel.ChiBilevelPrimitive
import Bilevel.ChiOuterBilevelTrace

/-! The concrete recursive extension and upper readout form the source
Primitive, with the exact recursive hyperobjective at the unique response. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem hierarchy_primitive_of_budgets (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (j : ℕ)
    (c v : ℝ) (hc : 0 < c) (hβ : 0 < (D (j+1) []).width) (hv : 1 ≤ v)
    (coarseIndex radialIndex : Fin (j+1) → Fin (2*(j+1))) (fineIndex : Fin (2*(j+1)))
    (rad R : ℕ → ℝ) (hw : ∀ i : Fin (j+1),0 < (D (i.val+1) []).width)
    (hR : ∀ i : Fin (j+1),0 < R (i.val+1))
    (μ L ρ : ℝ) (hμ : 0 < μ) (hμL : 2*μ ≤ L) (hρ : 0 ≤ ρ) :
    let dn := normalCoefficient L (j+1)
    let Ext := hierarchyExtension m M D (j+1) c v hc hβ hv (2*(j+1)) coarseIndex radialIndex fineIndex rad R dn
    let hExt := hierarchyExtension_contDiff m M D (j+1) c v hc hβ hv (2*(j+1)) coarseIndex radialIndex fineIndex rad R dn hw
    let base := upperBase m M ν D (j+1) (rad 0) (R 0)
    ∀ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖ ≤ (1:ℝ)/12,
    (∀ z,‖iteratedFDeriv ℝ 3 Ext z‖ ≤ ρ/(3*(3*μ/2))) →
    (∀ z,‖iteratedFDeriv ℝ 2 base z‖ ≤ L) →
    (∀ x u,‖gradient (fun w => base (pack x w)) u‖ ≤ 3*L/4) →
    ∃ P : Model.Primitive (X:=Joint E (Blocks m F)) (Y:=Joint (Blocks m F) (Normals (2*(j+1)))) μ L L L ρ,
      (∀ x y,P.f x y=hierarchyUpper m M ν D (j+1) rad R (2*(j+1)) dn x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb (by change (1:ℝ)/12<1;norm_num)
        (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,
        (∀ x,r.y x=pack ((L/(6*μ)) • x.snd) (normalTrace Ext x.fst ((L/(6*μ)) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter m M ν D rad R (j+1) (L/(6*μ)) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) := by
  dsimp only
  intro hb hthird hbase2 hbase1
  let dn := normalCoefficient L (j+1)
  let Ext := hierarchyExtension m M D (j+1) c v hc hβ hv (2*(j+1)) coarseIndex radialIndex fineIndex rad R dn
  have hExt := hierarchyExtension_contDiff m M D (j+1) c v hc hβ hv (2*(j+1)) coarseIndex radialIndex fineIndex rad R dn hw
  let base := upperBase m M ν D (j+1) (rad 0) (R 0)
  let b := dn • normalOnes (2*(j+1))
  have hL : 0 < L := by linarith
  have hdn : dn ≠ 0 := (normalCoefficient_pos hL (by omega)).ne'
  have hbN : ‖b‖ ≤ L/4 := by
    have hh := source_readout_gradient_norm hL (j+1) (by omega) 0
    rw [(weightedReadout_hasGradientAt (2*(j+1)) dn 0).gradient] at hh
    exact hh.le
  obtain ⟨P,hf,hg,r,hr,_,hu⟩ := primitive_of_extension_jets Ext hExt ⟨1/12,by norm_num⟩ hb
    (by change (1:ℝ)/12<1;norm_num) (by norm_num) (hierarchyExtension_zero_trace m M D (j+1) c v hc hβ hv
      (2*(j+1)) coarseIndex radialIndex fineIndex rad R dn hw) μ L ρ hμ hμL hρ hthird
    base (upperBase_contDiff m M ν D (j+1) (rad 0) (R 0)) hbase2 hbase1 b hbN
  have hinner (q : Normals (2*(j+1))) : ⟪b,q⟫=dn*normalReadout (2*(j+1)) q := by
    change ⟪dn • normalOnes (2*(j+1)),q⟫=_
    rw [real_inner_smul_left,← InnerProductSpace.toDual_apply,normalOnes_toDual]
  have hf' : ∀ x y,P.f x y=hierarchyUpper m M ν D (j+1) rad R (2*(j+1)) dn x.fst y := by
    intro x y
    rw [hf,hinner]
    rfl
  refine ⟨P,hf',hg,r,hr,?_,hu⟩
  intro x
  change P.f x (r.y x)=_
  rw [hf',hr]
  exact hierarchyUpper_response_value m M ν D j c v hc hβ hv (2*(j+1)) coarseIndex radialIndex fineIndex
    rad R dn hdn hw hR (L/(6*μ)) x.fst x.snd

end Bilevel.ChiOuter
