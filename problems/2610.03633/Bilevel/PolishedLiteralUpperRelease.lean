import Bilevel.PolishedLiteralSelection
import Bilevel.PolishedLiteralResidualJetsBase

/-! Exact joint macro residual and release-correction jets for the literal
source functions. Exclusivity is derived from the actual selector jets. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain ChiCarrier ZeroChainPotential
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def incomingFactor (M : Node X) (i : Fin (M.n+1)) (z : Joint X U) : ℝ :=
  -(M.ell*M.width^2)*phi (M.coordinates z.fst i/M.width)

omit [CompleteSpace U] in
theorem incomingFactor_contDiff (M : Node X) (i : Fin (M.n+1)) :
    ContDiff ℝ 3 (incomingFactor (U:=U) M i) :=
  contDiff_const.mul ((phi_contDiff 3).comp
    ((((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp (M.coordinates_contDiff 3)).comp
      (fstMap (X:=X) (U:=U)).contDiff).div_const M.width))

omit [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] in
theorem residual_factor (M : Node X) (i : Fin (M.n+1)) (z : Joint X U) :
    wrappedResidual M i z.fst=jointSelector M i z*incomingFactor M i z := by
  change (M.ell*M.width^2)*(-selector M.n i (M.width⁻¹ • M.coordinates z.fst)*
    phi ((M.width⁻¹ • M.coordinates z.fst) i))=
    selector M.n i (M.width⁻¹ • M.coordinates z.fst)*(-(M.ell*M.width^2)*phi (M.coordinates z.fst i/M.width))
  simp only [PiLp.smul_apply,smul_eq_mul,div_eq_inv_mul]
  ring

omit [CompleteSpace U] in
theorem selected_joint_sum_bound (M : Node X)
    (f : Fin (M.n+1) → Joint X U → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (z : Joint X U) (k : ℕ) (hk : k≤3) (B : ℝ) (hB : 0≤B)
    (hb : ∀ i,‖iteratedFDeriv ℝ k (fun y => jointSelector M i y*f i y) z‖≤B) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ i : Fin (M.n+1),jointSelector M i y*f i y) z‖≤B := by
  rw [iteratedFDeriv_sum (fun i _ => ((jointSelector_contDiff M i).mul (hf i)).of_le
    (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  apply norm_sum_le_of_exclusive _ B hB hb
  intro i j hij hi
  by_contra hj
  have hsupport (a : Fin (M.n+1))
      (ha : iteratedFDeriv ℝ k (fun y => jointSelector M a y*f a y) z≠0) :
      ∃ q≤k,iteratedFDeriv ℝ q (jointSelector M a) z≠0 := by
    by_contra! hz
    exact ha (ZeroChainResidualBounds.jet_mul_zero_left (jointSelector_contDiff M a) (hf a) z k hk hz)
  obtain ⟨a,ha,hai⟩ := hsupport i hi
  obtain ⟨b,hb,hbj⟩ := hsupport j hj
  exact hij (jointSelector_jets_unique M i j z a b (by omega) (by omega) hai hbj)

theorem joint_macro_residual_jets : ∃ C : ℝ,1≤C ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (M : Node X),0≤M.ell → 0<M.width → M.width≤M.radius →
      ∀ i (z : Joint X U) k,k≤3 →
      ‖iteratedFDeriv ℝ k (fun y : Joint X U => wrappedResidual M i y.fst) z‖≤
        C*(M.ell*M.width^2)/M.width^k := by
  obtain ⟨B,hB,hraw⟩ := outer_residual_uniform_jets
  have hB0 : 0≤B := by linarith
  refine ⟨100000*B,by linarith,fun X U _ _ _ _ _ _ M hell hh hhR i z k hk => ?_⟩
  apply (ChiOuter.contraction_jet_bound (fstMap (X:=X) (U:=U)) fstMap_norm_le
    (wrappedResidual_contDiff M i 3) z k hk).trans
  exact scaled_radial_profile_jet_bound (outer_residual_contDiff M.n i) B (M.ell*M.width^2) M.width M.radius
    hB0 (by positivity) hh hhR (fun q hq y => hraw M.n i y q hq) M.frame z.fst k hk

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

def microNode (i : Fin (P.macroNode.n+1)) : Node U where
  n := P.n
  ell := P.L
  width := P.β
  receiver := P.receiver
  nu := P.ν
  force := P.force
  parentWidth := P.macroNode.width
  tailRadius := P.macroNode.width
  radius := P.radius
  frame := P.frames i

def releaseCorrection (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),wrappedResidual P.macroNode i z.fst*(P.microRelease i z.snd-1)

theorem releaseCorrection_contDiff : ContDiff ℝ 3 P.releaseCorrection :=
  ContDiff.sum (fun i _ => ((wrappedResidual_contDiff P.macroNode i 3).comp
    (fstMap (X:=X) (U:=U)).contDiff).mul
    (((P.microRelease_contDiff i).comp (sndMap (X:=X) (U:=U)).contDiff).sub contDiff_const))

theorem releaseCorrection_selected : P.releaseCorrection=fun z =>
    ∑ i : Fin (P.macroNode.n+1),jointSelector P.macroNode i z*
      (incomingFactor P.macroNode i z*(P.microRelease i z.snd-1)) := by
  funext z
  apply Finset.sum_congr rfl
  intro i _
  rw [residual_factor]
  ring

end Parameters

theorem release_correction_jets : ∃ C : ℝ,1≤C ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)),0≤P.macroNode.ell → 0≤P.L → 0<P.β →
      P.β≤P.radius → 0<P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.macroNode.width≤P.radius → ∀ (z : Joint X U) k,k≤3 →
      ‖iteratedFDeriv ℝ k P.releaseCorrection z‖≤C*(P.macroNode.ell*P.macroNode.width^2)/P.macroNode.width^k := by
  obtain ⟨Cr,hCr,hres⟩ := joint_macro_residual_jets
  obtain ⟨Cq,hCq,hrel⟩ := constructed_node_jets
  have hCr0 : 0≤Cr := by linarith
  have hCq0 : 0≤Cq := by linarith
  refine ⟨8*Cr*Cq,by nlinarith [mul_le_mul hCr hCq zero_le_one hCr0],?_⟩
  intro X U _ _ _ _ _ _ P hell hL hβ hβR hb hbR hmR z k hk
  let f := fun i : Fin (P.macroNode.n+1) => fun y : Joint X U =>
    incomingFactor P.macroNode i y*(P.microRelease i y.snd-1)
  have hf (i : Fin (P.macroNode.n+1)) : ContDiff ℝ 3 (f i) :=
    (incomingFactor_contDiff P.macroNode i).mul
      (((P.microRelease_contDiff i).comp (sndMap (X:=X) (U:=U)).contDiff).sub contDiff_const)
  rw [P.releaseCorrection_selected]
  apply selected_joint_sum_bound P.macroNode f hf z k hk _ (by positivity)
  intro i
  have he : (fun y => jointSelector P.macroNode i y*f i y)=
      fun y => wrappedResidual P.macroNode i y.fst*(P.microRelease i y.snd-1) := by
    funext y
    rw [residual_factor]
    dsimp only [f]
    ring
  rw [he]
  have hr (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y : Joint X U => wrappedResidual P.macroNode i y.fst) z‖≤
        (Cr*(P.macroNode.ell*P.macroNode.width^2))/P.macroNode.width^q :=
    hres X U P.macroNode hell hb hbR i z q (by omega)
  have hq (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y : Joint X U => P.microRelease i y.snd-1) z‖≤Cq/P.macroNode.width^q := by
    apply (ChiOuter.contraction_jet_bound (sndMap (X:=X) (U:=U)) sndMap_norm_le
      ((P.microRelease_contDiff i).sub contDiff_const) z q (by omega)).trans
    change ‖iteratedFDeriv ℝ q (fun y : U => P.microRelease i y-1) z.snd‖≤Cq/P.macroNode.width^q
    by_cases hq0 : q=0
    · subst q
      rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one]
      have hv : 0≤P.microRelease i z.snd ∧ P.microRelease i z.snd≤1 :=
        ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
      exact (abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩).trans hCq
    · rw [ZeroChainCarry.jet_sub_constant (P.microRelease_contDiff i) 1 z.snd q (by omega) (by omega)]
      exact (hrel U (P.microNode i) hL hβ hβR hb hmR 0 z.snd q (by omega)).2.2
  have hs := same_width_product_jets ((wrappedResidual_contDiff P.macroNode i 3).comp
      (fstMap (X:=X) (U:=U)).contDiff)
    (((P.microRelease_contDiff i).comp (sndMap (X:=X) (U:=U)).contDiff).sub contDiff_const)
    (Cr*(P.macroNode.ell*P.macroNode.width^2)) Cq P.macroNode.width
    (by positivity) hCq0 hb z k hk hr hq
  convert hs using 1
  ring

end Bilevel.PolishedLiteral
