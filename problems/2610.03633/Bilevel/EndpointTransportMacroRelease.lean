import Bilevel.EndpointTransportReleaseCorrection
import Bilevel.EndpointTransportOuterSelection
import Bilevel.ChiOuterReleaseJets

/-! The macro-to-physical release correction for the depth-zero exact
quadratic transport family. Full mixed jets retain a numerical constant
independent of the number of macro stages and transport layers. -/
noncomputable section
set_option maxHeartbeats 700000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def physicalMacroReleaseCorrection {n D : ℕ} (M : Node E) (P : X →L[ℝ] E)
    (kids : Fin (M.n+1) → Node (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (x : X) : ℝ :=
  ∑ i : Fin (M.n+1),wrappedResidual M i (P x)*(physicalRelease Q (kids i) (B x)-1)

theorem physicalMacroReleaseCorrection_contDiff {n D : ℕ} (M : Node E) (P : X →L[ℝ] E)
    (kids : Fin (M.n+1) → Node (Block D)) (B : X →L[ℝ] Physical n D) (Q : Rotations n D) :
    ContDiff ℝ 3 (physicalMacroReleaseCorrection M P kids B Q) :=
  ContDiff.sum (fun i _ => ((wrappedResidual_contDiff M i 3).comp P.contDiff).mul
    (((physicalRelease_contDiff Q (kids i) 3).comp B.contDiff).sub contDiff_const))

theorem physical_macro_release_correction_jets : ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D : ℕ) (M : Node E) (kids : Fin (M.n+1) → Node (Block D)),
      0≤M.ell → 0<M.width → M.width≤M.radius → (∀ i,NodeJetAdmissible (kids i)) →
      (∀ i,(kids i).parentWidth=M.width) →
      ∀ (P : X →L[ℝ] E) (B : X →L[ℝ] Physical n D),‖P‖≤1 → ‖B‖≤1 →
      ∀ (Q : Rotations n D) (x : X) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (physicalMacroReleaseCorrection M P kids B Q) x‖≤
        C*(M.ell*M.width^2)/M.width^k := by
  obtain ⟨Bm,hBm,hm⟩ := outer_residual_uniform_jets
  let Cm := 100000*Bm
  have hCm : 1≤Cm := by dsimp [Cm];linarith
  obtain ⟨Cr,hCr,hr⟩ := physical_release_jets
  have hCm0 : 0≤Cm := by linarith
  have hCr0 : 0≤Cr := by linarith
  refine ⟨8*Cm*Cr,by nlinarith,fun E _ _ _ X _ _ n D M kids hell hw hwR hk hp P B hP hB Q x k hq => ?_⟩
  let f := fun i : Fin (M.n+1) => fun y : X =>
    outerIncomingFactor (F:=ℝ) 0 M i (macroLift P y)*(physicalRelease Q (kids i) (B y)-1)
  have hf (i : Fin (M.n+1)) : ContDiff ℝ 3 (f i) :=
    ((outerIncomingFactor_contDiff 0 M i).comp (macroLift P).contDiff).mul
      (((physicalRelease_contDiff Q (kids i) 3).comp B.contDiff).sub contDiff_const)
  have hfactor (i : Fin (M.n+1)) (y : X) :
      macroSelector M P i y*f i y=wrappedResidual M i (P y)*(physicalRelease Q (kids i) (B y)-1) := by
    have he := outerResidual_factor (F:=ℝ) 0 M i (macroLift P y)
    change wrappedResidual M i (P y)=macroSelector M P i y*outerIncomingFactor 0 M i (macroLift P y) at he
    rw [he]
    dsimp only [f]
    ring
  have he : physicalMacroReleaseCorrection M P kids B Q=macroSelected M P f := by
    funext y
    apply Finset.sum_congr rfl
    intro i _
    exact (hfactor i y).symm
  rw [he]
  apply macroSelected_sum_bound M P f hf x k hq _ (by positivity)
  intro i
  rw [show (fun y => macroSelector M P i y*f i y)=
      (fun y => wrappedResidual M i (P y)*(physicalRelease Q (kids i) (B y)-1)) from funext (hfactor i)]
  have hres (q : ℕ) (hqk : q≤k) :
      ‖iteratedFDeriv ℝ q (wrappedResidual M i ∘ P) x‖≤(Cm*(M.ell*M.width^2))/M.width^q := by
    apply (linear_jet_contraction P hP (wrappedResidual_contDiff M i 3) x q (by omega)).trans
    exact scaled_radial_profile_jet_bound (outer_residual_contDiff M.n i) Bm (M.ell*M.width^2) M.width M.radius
      (by linarith) (by positivity) hw hwR (fun a ha y => hm M.n i y a ha) M.frame (P x) q (by omega)
  have hrel (q : ℕ) (hqk : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y => physicalRelease Q (kids i) (B y)-1) x‖≤Cr/M.width^q := by
    apply physical_release_sub_one Q (kids i) B Cr M.width hCr x q (by omega)
    have hh := (linear_jet_contraction B hB (physicalRelease_contDiff Q (kids i) 3) x q (by omega)).trans
      (hr n D Q (kids i) (hk i) (B x) q (by omega))
    simpa only [hp i] using hh
  have hh := same_width_product_jets ((wrappedResidual_contDiff M i 3).comp P.contDiff)
    (((physicalRelease_contDiff Q (kids i) 3).comp B.contDiff).sub contDiff_const)
    (Cm*(M.ell*M.width^2)) Cr M.width (by positivity) hCr0 hw x k hq hres hrel
  exact hh.trans_eq (by ring)

end Bilevel.EndpointTransportResponse
