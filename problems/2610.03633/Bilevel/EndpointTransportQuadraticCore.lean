import Bilevel.EndpointTransportMacroRelease
import Bilevel.EndpointTransportOuterCarriers
import Bilevel.EndpointTransportOuterTrace
import Bilevel.EndpointTransportUpperBase

/-! The actual depth-zero upper core for an exact quadratic lower oracle.
Both the macro release and terminal payload use physical endpoint readouts;
the public bowl uses the full physical norm with its exact gamma scaling. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry RadialWrapper PartialLegendre
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def quadraticCoreLower {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (ρ R : ℝ) (z : Joint E (Physical n D)) : ℝ :=
  physicalMacroReleaseCorrection M (jointFstLinear (A:=E) (B:=Physical n D)) (fun i => G 0 [i.val]) (jointSndLinear (A:=E) (B:=Physical n D)) Q z+
    outerPhysicalCarrier 0 Q M (jointFstLinear (A:=E) (B:=Physical n D)) G 0 (jointSndLinear (A:=E) (B:=Physical n D)) 0 0 z+
    bowl (ρ/EndpointTransportMatrix.gamma n^2) (EndpointTransportMatrix.gamma n*R) z.snd

def quadraticCore {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (z : Joint E (Physical n D)) : ℝ :=
  macroValue M.n M.ell M.width ν M.radius M.frame z.fst+quadraticCoreLower Q M G ρ R z

theorem quadraticCoreLower_contDiff {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (ρ R : ℝ) : ContDiff ℝ 3 (quadraticCoreLower Q M G ρ R) :=
  ((physicalMacroReleaseCorrection_contDiff M (jointFstLinear (A:=E) (B:=Physical n D)) (fun i => G 0 [i.val]) (jointSndLinear (A:=E) (B:=Physical n D)) Q).add
    (outerPhysicalCarrier_contDiff 0 Q M (jointFstLinear (A:=E) (B:=Physical n D)) G 0 (jointSndLinear (A:=E) (B:=Physical n D)) 0 0)).add
    ((full_bowl_contDiff _ _ 3).comp (jointSndLinear (A:=E) (B:=Physical n D)).contDiff)

theorem quadraticCore_contDiff {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) : ContDiff ℝ 3 (quadraticCore Q M ν G ρ R) :=
  ((macro_contDiff M ν 3).comp (jointFstLinear (A:=E) (B:=Physical n D)).contDiff).add (quadraticCoreLower_contDiff Q M G ρ R)

theorem quadraticCore_eq_physicalOuter {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (x : E) (Y : Physical n D) (u : ℕ → Block D) :
    quadraticCore Q M ν G (ρ 0) (R 0) (pack x Y)=physicalOuter Q M ν G ρ R 0 x u Y := by
  have hfst : ((jointFstLinear (A:=E) (B:=Physical n D)) : Joint E (Physical n D) →L[ℝ] E) (pack x Y)=x := rfl
  have hsnd : ((jointSndLinear (A:=E) (B:=Physical n D)) : Joint E (Physical n D) →L[ℝ] Physical n D) (pack x Y)=Y := rfl
  have hx : (pack x Y).fst=x := rfl
  have hY : (pack x Y).snd=Y := rfl
  simp only [quadraticCore,quadraticCoreLower,physicalMacroReleaseCorrection,outerPhysicalCarrier,
    macroSelected,macroSelector,physicalCarrier,physicalOuter,attachment,physicalRecursive,physicalPublic,
    if_pos rfl,if_true,Function.comp_apply,Finset.sum_add_distrib,mul_comm,hfst,hsnd,hx,hY]
  ring

theorem quadraticCoreLower_jet_bound {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (ρ R : ℝ) (z : Joint E (Physical n D))
    (k : ℕ) (hk : k≤3) (Bc Bp Br : ℝ)
    (hc : ‖iteratedFDeriv ℝ k (physicalMacroReleaseCorrection M (jointFstLinear (A:=E) (B:=Physical n D))
      (fun i => G 0 [i.val]) (jointSndLinear (A:=E) (B:=Physical n D)) Q) z‖≤Bc)
    (hp : ‖iteratedFDeriv ℝ k (outerPhysicalCarrier 0 Q M (jointFstLinear (A:=E) (B:=Physical n D)) G 0 (jointSndLinear (A:=E) (B:=Physical n D)) 0 0) z‖≤Bp)
    (hr : ‖iteratedFDeriv ℝ k (fun y : Joint E (Physical n D) =>
      bowl (ρ/EndpointTransportMatrix.gamma n^2) (EndpointTransportMatrix.gamma n*R) y.snd) z‖≤Br) :
    ‖iteratedFDeriv ℝ k (quadraticCoreLower Q M G ρ R) z‖≤Bc+Bp+Br := by
  apply scalar_add_jet_bound _ _
    ((physicalMacroReleaseCorrection_contDiff M (jointFstLinear (A:=E) (B:=Physical n D)) (fun i => G 0 [i.val]) (jointSndLinear (A:=E) (B:=Physical n D)) Q).add
      (outerPhysicalCarrier_contDiff 0 Q M (jointFstLinear (A:=E) (B:=Physical n D)) G 0 (jointSndLinear (A:=E) (B:=Physical n D)) 0 0))
    ((full_bowl_contDiff _ _ 3).comp (jointSndLinear (A:=E) (B:=Physical n D)).contDiff) z k hk _ _ _ hr
  exact scalar_add_jet_bound _ _
    (physicalMacroReleaseCorrection_contDiff M (jointFstLinear (A:=E) (B:=Physical n D)) (fun i => G 0 [i.val]) (jointSndLinear (A:=E) (B:=Physical n D)) Q)
    (outerPhysicalCarrier_contDiff 0 Q M (jointFstLinear (A:=E) (B:=Physical n D)) G 0 (jointSndLinear (A:=E) (B:=Physical n D)) 0 0) z k hk _ _ hc hp

theorem quadraticCore_lower_gradient_bound {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (x : E) (Y : Physical n D) (B : ℝ)
    (hb : ‖iteratedFDeriv ℝ 1 (quadraticCoreLower Q M G ρ R) (pack x Y)‖≤B) :
    ‖gradient (fun w => quadraticCore Q M ν G ρ R (pack x w)) Y‖≤B := by
  have hg := (((quadraticCoreLower_contDiff Q M G ρ R).differentiable (by norm_num)) (pack x Y)).hasGradientAt
  have hy := PrimitiveGeometry.partial_y hg
  rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq] at hb
  change ‖gradient (fun w => macroValue M.n M.ell M.width ν M.radius M.frame x+
    quadraticCoreLower Q M G ρ R (pack x w)) Y‖≤B
  rw [← norm_fderiv_eq_norm_gradient,fderiv_const_add,norm_fderiv_eq_norm_gradient,hy.gradient]
  exact (WithLp.norm_snd_le E (gradient (quadraticCoreLower Q M G ρ R) (pack x Y))).trans hb

theorem quadraticCore_second_bound {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (z : Joint E (Physical n D)) (Bm Bl : ℝ)
    (hm : ‖iteratedFDeriv ℝ 2 (macroValue M.n M.ell M.width ν M.radius M.frame) z.fst‖≤Bm)
    (hl : ‖iteratedFDeriv ℝ 2 (quadraticCoreLower Q M G ρ R) z‖≤Bl) :
    ‖iteratedFDeriv ℝ 2 (quadraticCore Q M ν G ρ R) z‖≤Bm+Bl := by
  let P : Joint E (Physical n D) →L[ℝ] E := (jointFstLinear (A:=E) (B:=Physical n D))
  let f : E → ℝ := macroValue M.n M.ell M.width ν M.radius M.frame
  have hp := linear_jet_contraction P ChiPrimitive.jointFstLinear_norm (macro_contDiff M ν 3) z 2 (by norm_num)
  exact scalar_add_jet_bound (f ∘ P) (quadraticCoreLower Q M G ρ R)
    ((macro_contDiff M ν 3).comp P.contDiff) (quadraticCoreLower_contDiff Q M G ρ R)
    z 2 (by norm_num) Bm Bl (hp.trans hm) hl

omit [CompleteSpace E] in
theorem physical_scaled_bowl_jets {n D : ℕ} (ρ R : ℝ) (hρ : 0≤ρ) (hR : 0<R)
    (z : Joint E (Physical n D)) :
    let f := fun y : Joint E (Physical n D) =>
      bowl (ρ/EndpointTransportMatrix.gamma n^2) (EndpointTransportMatrix.gamma n*R) y.snd
    ‖iteratedFDeriv ℝ 1 f z‖≤ρ*R ∧ ‖iteratedFDeriv ℝ 2 f z‖≤ρ := by
  dsimp only
  let γ := EndpointTransportMatrix.gamma n
  have hγ : 0<γ := gamma_positive n
  have hγ1 : 1≤γ := (gamma_range n).1
  have hρ' : 0≤ρ/γ^2 := div_nonneg hρ (sq_nonneg γ)
  have hR' : 0<γ*R := mul_pos hγ hR
  have hb1 : ‖iteratedFDeriv ℝ 1 (bowl (ρ/γ^2) (γ*R)) z.snd‖≤(ρ/γ^2)*(γ*R) := by
    rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq,Regularity.bowl_gradient _ _ hR']
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hρ']
    exact mul_le_mul_of_nonneg_left (compress_norm_le_radius _ hR' _) hρ'
  have hb2 := Regularity.bowl_jet_two (ρ/γ^2) (γ*R) hρ' hR' z.snd
  let P : Joint E (Physical n D) →L[ℝ] Physical n D := (jointSndLinear (A:=E) (B:=Physical n D))
  have hj1 := linear_jet_contraction P ChiPrimitive.jointSndLinear_norm (full_bowl_contDiff (ρ/γ^2) (γ*R) 3) z 1 (by norm_num)
  have hj2 := linear_jet_contraction P ChiPrimitive.jointSndLinear_norm (full_bowl_contDiff (ρ/γ^2) (γ*R) 3) z 2 (by norm_num)
  refine ⟨(hj1.trans hb1).trans ?_,(hj2.trans hb2).trans ?_⟩
  · have he : (ρ/γ^2)*(γ*R)=(ρ*R)/γ := by field_simp;ring
    rw [he]
    exact div_le_self (mul_nonneg hρ hR.le) hγ1
  · exact div_le_self hρ (by nlinarith only [hγ1])

end Bilevel.EndpointTransportResponse
