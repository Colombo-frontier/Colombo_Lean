import Bilevel.PolishedLiteralUpperSelected

/-! Assembly of the actual lower-variable part of the literal mean. The
macro-only term is separated so its growing first derivative is never
charged to the upper primitive's lower gradient budget. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain ChiCarrier RadialWrapper
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

def lowerBase (z : Joint X U) : ℝ :=
  bowl P.ν P.radius z.snd+selected P.macroNode P.microCore z+P.releaseCorrection z

theorem lowerBase_contDiff : ContDiff ℝ 3 P.lowerBase :=
  (((full_bowl_contDiff P.ν P.radius 3).comp (sndMap (X:=X) (U:=U)).contDiff).add
    (ContDiff.sum (fun i _ => (jointSelector_contDiff P.macroNode i).mul
      ((P.microCore_contDiff i).comp (sndMap (X:=X) (U:=U)).contDiff)))).add P.releaseCorrection_contDiff

theorem meanBase_eq (z : Joint X U) : P.meanBase z=
    macroValue P.macroNode.n P.macroNode.ell P.macroNode.width P.macroRadial P.macroNode.radius P.macroNode.frame z.fst+
      P.lowerBase z := by
  simp only [meanBase,macroCarrier,lowerBase,selected,jointSelector,releaseCorrection,
    mul_sub,mul_one,Finset.sum_sub_distrib]
  ring

theorem lowerBase_jet_sum (z : Joint X U) (k : ℕ) (hk : k≤3) (Bb Bs Br : ℝ)
    (hb : ‖iteratedFDeriv ℝ k (fun y : Joint X U => bowl P.ν P.radius y.snd) z‖≤Bb)
    (hs : ‖iteratedFDeriv ℝ k (selected P.macroNode P.microCore) z‖≤Bs)
    (hr : ‖iteratedFDeriv ℝ k P.releaseCorrection z‖≤Br) :
    ‖iteratedFDeriv ℝ k P.lowerBase z‖≤Bb+Bs+Br := by
  have hc : ContDiff ℝ 3 (selected P.macroNode P.microCore) :=
    ContDiff.sum (fun i _ => (jointSelector_contDiff P.macroNode i).mul
      ((P.microCore_contDiff i).comp (sndMap (X:=X) (U:=U)).contDiff))
  have hp : ContDiff ℝ 3 (fun y : Joint X U => bowl P.ν P.radius y.snd) :=
    (full_bowl_contDiff P.ν P.radius 3).comp (sndMap (X:=X) (U:=U)).contDiff
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  unfold lowerBase
  rw [iteratedFDeriv_add_apply' (((hp.add hc).of_le hk').contDiffAt)
      ((P.releaseCorrection_contDiff.of_le hk').contDiffAt),
    iteratedFDeriv_add_apply' ((hp.of_le hk').contDiffAt) ((hc.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hb hs)) hr)

end Parameters

theorem lowerBase_first_second : ∃ B : ℝ → ℝ → ℝ,
    (∀ A Cr,0≤A → 0≤Cr → 0≤B A Cr) ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (Cr : ℝ),
      0<P.L → 0<P.β → 0≤P.receiver → 0≤P.ν → P.ν≤P.L →
      P.force=P.L*P.β → P.macroNode.ell=P.L →
      P.β≤P.macroNode.width → P.macroNode.width≤P.radius →
      P.radius≤Cr*P.macroNode.width → 0≤Cr → P.macroNode.width≤P.macroNode.radius →
      P.β*Real.sqrt ((P.n:ℝ)+1)≤P.macroNode.width → ∀ z : Joint X U,
      ‖iteratedFDeriv ℝ 1 P.lowerBase z‖≤P.ν*P.radius+B P.receiver Cr*P.L*P.macroNode.width ∧
      ‖iteratedFDeriv ℝ 2 P.lowerBase z‖≤P.ν+B P.receiver Cr*P.L := by
  obtain ⟨Cs,C,Cg,Ch,Dr,hCs,hC,hCg,hCh,hDr,hs⟩ := selected_core_jets
  obtain ⟨Crel,hCrel,hr⟩ := release_correction_jets
  let B := fun A Cr => 8*Cs*coreJetConstant C Cg Ch Dr A Cr+Crel
  have hB : ∀ A Cr,0≤A → 0≤Cr → 0≤B A Cr := by
    intro A Cr hA hCr
    have hcore := coreJetConstant_nonneg hC hCg hCh hDr hA hCr
    dsimp [B]
    have hCs0 : 0≤Cs := by linarith
    have hCrel0 : 0≤Crel := by linarith
    positivity
  refine ⟨B,hB,?_⟩
  intro X U _ _ _ _ _ _ P Cr hL hβ hA hν hνL hf hℓ hβb hbR hRb hCr hmR hwidth z
  have hb : 0<P.macroNode.width := hβ.trans_le hβb
  have hR : 0<P.radius := hb.trans_le hbR
  have hsel := hs X U P Cr hL hβ hA hν hνL hf hβb hbR hRb hCr hmR hwidth
  have hrel := hr X U P (by rw [hℓ];exact hL.le) hL.le hβ (hβb.trans hbR) hb hmR hbR
  have hb1 : ‖iteratedFDeriv ℝ 1 (fun y : Joint X U => bowl P.ν P.radius y.snd) z‖≤P.ν*P.radius := by
    apply (ChiOuter.contraction_jet_bound (sndMap (X:=X) (U:=U)) sndMap_norm_le
      (full_bowl_contDiff P.ν P.radius 3) z 1 (by norm_num)).trans
    rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq,
      ChiOuter.Regularity.bowl_gradient P.ν P.radius hR,norm_smul,Real.norm_eq_abs,abs_of_nonneg hν]
    exact mul_le_mul_of_nonneg_left (compress_norm_le_radius P.radius hR _) hν
  have hb2 : ‖iteratedFDeriv ℝ 2 (fun y : Joint X U => bowl P.ν P.radius y.snd) z‖≤P.ν :=
    (ChiOuter.contraction_jet_bound (sndMap (X:=X) (U:=U)) sndMap_norm_le
      (full_bowl_contDiff P.ν P.radius 3) z 2 (by norm_num)).trans
      (ChiOuter.Regularity.bowl_jet_two P.ν P.radius hν hR _)
  constructor
  · have ht := P.lowerBase_jet_sum z 1 (by norm_num) _ _ _ hb1 (hsel z 1 (by norm_num)) (hrel z 1 (by norm_num))
    apply ht.trans
    rw [hℓ]
    dsimp [B]
    apply le_of_eq
    field_simp [hb.ne']
    ring
  · have ht := P.lowerBase_jet_sum z 2 (by norm_num) _ _ _ hb2 (hsel z 2 (by norm_num)) (hrel z 2 (by norm_num))
    apply ht.trans
    rw [hℓ]
    dsimp [B]
    apply le_of_eq
    field_simp [hb.ne']
    ring

end Bilevel.PolishedLiteral
