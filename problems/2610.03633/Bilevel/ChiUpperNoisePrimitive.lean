import Bilevel.ChiUpperNoiseOracle
import Bilevel.ChiQuadraticPrimitive

/-! Actual prescribed upper-noise Primitive with a public isotropic
quadratic lower objective and attained affine response. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry PartialLegendre
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem fullCore_second_bound (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    {L : ℝ} (hb : ∀ z,‖iteratedFDeriv ℝ 2 (core m M ν D ρ R) z‖≤L)
    (q : Queries E (Blocks m F)) : ‖iteratedFDeriv ℝ 2 (fullCore m M ν D ρ R) q‖≤L := by
  let π : Queries E (Blocks m F) →L[ℝ] Joint E (Blocks m F) := queryProjection
  exact (contraction_jet_bound π (queryProjection_norm (E:=E) (U:=Blocks m F))
    (core_contDiff m M ν D ρ R) q 2 (by norm_num)).trans (hb _)

theorem fullCore_lower_bound (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    {C : ℝ} (hb : ∀ x u,‖gradient (fun v => core m M ν D ρ R (pack x v)) u‖≤C)
    (x : Joint E (Blocks m F)) (u : Blocks m F) :
    ‖gradient (fun v => fullCore m M ν D ρ R (pack x v)) u‖≤C := hb x.fst u

set_option maxHeartbeats 1000000 in
theorem direct_quadratic_primitive (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    {μ L : ℝ} (hμ : 0<μ) (hcond : 2*μ≤L)
    (hjet : ∀ z,‖iteratedFDeriv ℝ 2 (core m M ν D ρ R) z‖≤L/4)
    (hupper : ∀ x u,‖gradient (fun v => core m M ν D ρ R (pack x v)) u‖≤L/4) :
    ∃ P : Model.Primitive (X:=Joint E (Blocks m F)) (Y:=Blocks m F) μ L L L 0,
      (∀ x u,P.f x u=core m M ν D ρ R (pack x.fst u)) ∧
      (∀ x u,P.g x u=(3*μ/4)*‖u‖^2-(L/4)*⟪x.snd,u⟫) ∧
      (∀ x u,P.gy x u=(3*μ/2) • u-(L/4) • x.snd) ∧
      (∀ x u,P.gyy x u=(3*μ/2) • ContinuousLinearMap.id ℝ (Blocks m F)) ∧
      ∃ r : P.Response,(∀ x,r.y x=(L/(6*μ)) • x.snd) ∧
        (∀ x,P.hyperobjective r x=jointOuter m M ν D ρ R 0 (L/(6*μ)) x) ∧
        (∀ x u,P.IsLowerSolution x u ↔ u=(L/(6*μ)) • x.snd) := by
  have hL : 0<L := (by linarith only [hμ] : 0<2*μ).trans_le hcond
  let H : Blocks m F →L[ℝ] Blocks m F := (3*μ/2) • ContinuousLinearMap.id ℝ (Blocks m F)
  let C : Joint E (Blocks m F) →L[ℝ] Blocks m F := (L/4) • jointSndLinear
  have hsym (u v : Blocks m F) : ⟪H u,v⟫=⟪u,H v⟫ := by
    change ⟪(3*μ/2) • u,v⟫=⟪u,(3*μ/2) • v⟫
    rw [real_inner_smul_left,real_inner_smul_right]
  have hcoerce (u : Blocks m F) : μ*‖u‖^2≤⟪u,H u⟫ := by
    change μ*‖u‖^2≤⟪u,(3*μ/2) • u⟫
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    nlinarith only [mul_nonneg hμ.le (sq_nonneg ‖u‖)]
  have hH : ‖H‖≤3*μ/2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    change ‖(3*μ/2) • u‖≤(3*μ/2)*‖u‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
  have hC : ‖C‖≤L/4 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖(L/4) • x.snd‖≤(L/4)*‖x‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E x) (by positivity)
  have hbudget : ‖H‖+‖C‖≤L := by linarith only [hH,hC,hcond]
  have hresponse (x : Joint E (Blocks m F)) : H ((L/(6*μ)) • x.snd)=C x := by
    change (3*μ/2) • ((L/(6*μ)) • x.snd)=(L/4) • x.snd
    rw [smul_smul]
    congr 1
    field_simp
    ring
  obtain ⟨P,hf,hg,hgy,hgyy,_hgxy,r,hr,hm,hu⟩ := ChiQuadratic.quadratic_primitive
    (fullCore m M ν D ρ R) (fullCore_contDiff m M ν D ρ R) H C hsym μ L L L hμ hL.le hL.le hcoerce hbudget
    (fun x u => (fullCore_lower_bound m M ν D ρ R hupper x u).trans (by linarith only [hL]))
    (fun z => (fullCore_second_bound m M ν D ρ R hjet z).trans (by linarith only [hL]))
    (fun x => (L/(6*μ)) • x.snd) hresponse
  refine ⟨P,hf,?_,hgy,hgyy,r,hr,?_,hu⟩
  · intro x u
    rw [hg]
    change (1/2)*⟪u,(3*μ/2) • u⟫-⟪(L/4) • x.snd,u⟫=_
    rw [real_inner_smul_right,real_inner_smul_left,real_inner_self_eq_norm_sq]
    ring
  · intro x
    rw [hm]
    exact core_dilation m M ν D ρ R (L/(6*μ)) x.fst x.snd

end Bilevel.ChiUpperNoise
