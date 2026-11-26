import Bilevel.PolishedLiteralUpperCoreJets
import Bilevel.PolishedLiteralUpperRelease

/-! The actual sum of selected literal micro cores has a joint Hessian
bound independent of the number of macro stages and of the orientations. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain ChiCarrier ZeroChainPotential
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

theorem selected_core_jets : ∃ Cs C Cg Ch Dr : ℝ,1≤Cs ∧ 0≤C ∧ 0≤Cg ∧ 0≤Ch ∧ 0≤Dr ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (Cr : ℝ),
      0<P.L → 0<P.β → 0≤P.receiver → 0≤P.ν → P.ν≤P.L →
      P.force=P.L*P.β → P.β≤P.macroNode.width → P.macroNode.width≤P.radius →
      P.radius≤Cr*P.macroNode.width → 0≤Cr →
      P.macroNode.width≤P.macroNode.radius →
      P.β*Real.sqrt ((P.n:ℝ)+1)≤P.macroNode.width →
      ∀ (z : Joint X U) k,k≤2 →
        ‖iteratedFDeriv ℝ k (selected P.macroNode P.microCore) z‖≤
          (8*Cs*coreJetConstant C Cg Ch Dr P.receiver Cr)*P.L*P.macroNode.width^2/P.macroNode.width^k := by
  obtain ⟨Cs,hCs,hsel⟩ := joint_selector_jet_bounds
  obtain ⟨C,Cg,Ch,Dr,hC,hCg,hCh,hDr,hcore⟩ := wrapped_core_jets
  have hCs0 : 0≤Cs := by linarith
  refine ⟨Cs,C,Cg,Ch,Dr,hCs,hC,hCg,hCh,hDr,?_⟩
  intro X U _ _ _ _ _ _ P Cr hL hβ hA hν hνL hforce hβb hbR hRb hCr hmR hwidth z k hk
  have hb : 0<P.macroNode.width := hβ.trans_le hβb
  have hR : 0<P.radius := hb.trans_le hbR
  let B := coreJetConstant C Cg Ch Dr P.receiver Cr
  have hB : 0≤B := coreJetConstant_nonneg hC hCg hCh hDr hA hCr
  apply selected_jet_bound P.macroNode P.microCore P.microCore_contDiff z k (by omega) _ (by positivity)
  intro i
  have hs (q : ℕ) (hq : q≤k) : ‖iteratedFDeriv ℝ q (jointSelector P.macroNode i) z‖≤Cs/P.macroNode.width^q :=
    hsel X U P.macroNode hb hmR i z q (by omega)
  have hf (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y : Joint X U => P.microCore i y.snd) z‖≤
        (B*P.L*P.macroNode.width^2)/P.macroNode.width^q := by
    apply (ChiOuter.contraction_jet_bound (sndMap (X:=X) (U:=U)) sndMap_norm_le
      (P.microCore_contDiff i) z q (by omega)).trans
    have ht := hcore U P.n P.L P.β P.receiver P.ν P.macroNode.width P.radius Cr
      hL hβ hA hν hνL hβb hbR hRb hCr hwidth (P.frames i) z.snd q (by omega)
    have he : P.microCore i=rawCore P.n P.L P.β P.receiver P.ν P.macroNode.width ∘
        WrappedChain.coordinates P.n P.radius (P.frames i) := by
      funext u
      simp only [Parameters.microCore,Parameters.terminal,Parameters.coordinates,hforce,
        rawCore,Function.comp_def]
    rw [he]
    exact ht
  have ht := same_width_product_jets (jointSelector_contDiff P.macroNode i)
    ((P.microCore_contDiff i).comp (sndMap (X:=X) (U:=U)).contDiff)
    Cs (B*P.L*P.macroNode.width^2) P.macroNode.width hCs0 (by positivity) hb z k (by omega) hs hf
  convert ht using 1
  ring

end Bilevel.PolishedLiteral
