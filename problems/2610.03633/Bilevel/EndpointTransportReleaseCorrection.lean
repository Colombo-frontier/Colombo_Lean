import Bilevel.EndpointTransportRelease

/-! Full joint jets of the actual last ordinary carrier's physical release
correction, without a factor equal to the number of child stages. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def physicalReleaseCorrection {n D : ℕ} (m j : ℕ) (N : Node (Block D))
    (kids : Fin (N.n+1) → Node (Block D)) (A : X →L[ℝ] Blocks m (Block D))
    (B : X →L[ℝ] Physical n D) (Q : Rotations n D) (x : X) : ℝ :=
  ∑ i : Fin (N.n+1),jointResidual m j N i (A x)*(physicalRelease Q (kids i) (B x)-1)

theorem physicalReleaseCorrection_contDiff {n D : ℕ} (m j : ℕ) (N : Node (Block D))
    (kids : Fin (N.n+1) → Node (Block D)) (A : X →L[ℝ] Blocks m (Block D))
    (B : X →L[ℝ] Physical n D) (Q : Rotations n D) :
    ContDiff ℝ 3 (physicalReleaseCorrection m j N kids A B Q) :=
  ContDiff.sum (fun i _ => ((jointResidual_contDiff m j N i 3).comp A.contDiff).mul
    (((physicalRelease_contDiff Q (kids i) 3).comp B.contDiff).sub contDiff_const))

theorem physical_release_sub_one {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (B : X →L[ℝ] Physical n D) (C h : ℝ) (hC : 1≤C) (x : X) (k : ℕ) (hk : k≤3)
    (hb : ‖iteratedFDeriv ℝ k (physicalRelease Q N ∘ B) x‖≤C/h^k) :
    ‖iteratedFDeriv ℝ k (fun y => physicalRelease Q N (B y)-1) x‖≤C/h^k := by
  by_cases hk0 : k=0
  · subst k
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one]
    have hr := physicalRelease_range Q N (B x)
    exact (abs_le.mpr ⟨by linarith only [hr.1],by linarith only [hr.2]⟩).trans hC
  · change ‖iteratedFDeriv ℝ k (fun y => (physicalRelease Q N ∘ B) y-1) x‖≤C/h^k
    rw [ZeroChainCarry.jet_sub_constant ((physicalRelease_contDiff Q N 3).comp B.contDiff) 1 x k (by omega) hk]
    exact hb

theorem physical_release_correction_jets : ∃ C : ℝ,1≤C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D m j : ℕ) (N : Node (Block D)) (kids : Fin (N.n+1) → Node (Block D)),
      NodeJetAdmissible N → (∀ i,NodeJetAdmissible (kids i)) →
      (∀ i,(kids i).parentWidth=N.width) →
      ∀ (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (Q : Rotations n D) (x : X) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (physicalReleaseCorrection m j N kids A B Q) x‖≤C*(N.ell*N.width^2)/N.width^k := by
  obtain ⟨Cn,hCn,hn⟩ := constructed_joint_node_jets
  obtain ⟨Cr,hCr,hr⟩ := physical_release_jets
  have hCn0 : 0≤Cn := by linarith
  have hCr0 : 0≤Cr := by linarith
  refine ⟨8*Cn*Cr,by nlinarith,fun X _ _ n D m j N kids hN hk hp A B hA hB Q x k hq => ?_⟩
  let f := fun i : Fin (N.n+1) => fun y : X =>
    jointIncomingFactor m j N i (A y)*(physicalRelease Q (kids i) (B y)-1)
  have hf (i : Fin (N.n+1)) : ContDiff ℝ 3 (f i) :=
    ((jointIncomingFactor_contDiff m j N i).comp A.contDiff).mul
      (((physicalRelease_contDiff Q (kids i) 3).comp B.contDiff).sub contDiff_const)
  have he : physicalReleaseCorrection m j N kids A B Q=fun y =>
      ∑ i : Fin (N.n+1),ChiLiftedCarrier.selector m j N A i y*f i y := by
    funext y
    apply Finset.sum_congr rfl
    intro i _
    rw [jointResidual_factor]
    dsimp [ChiLiftedCarrier.selector,f]
    ring
  rw [he]
  have hell := hN.1
  have hw := hN.2.1
  apply ChiLiftedCarrier.selected_products_jet_bound m j N A f hf x k hq _ (by positivity)
  intro i
  have hi : (fun y => ChiLiftedCarrier.selector m j N A i y*f i y)=
      fun y => (jointResidual m j N i ∘ A) y*(physicalRelease Q (kids i) (B y)-1) := by
    funext y
    simp only [Function.comp_apply,jointResidual_factor]
    dsimp [ChiLiftedCarrier.selector,f]
    ring
  rw [hi]
  have hres (q : ℕ) (hqk : q≤k) :
      ‖iteratedFDeriv ℝ q (jointResidual m j N i ∘ A) x‖≤(Cn*(N.ell*N.width^2))/N.width^q :=
    (linear_jet_contraction A hA (jointResidual_contDiff m j N i 3) x q (by omega)).trans
      (hn (Block D) N hN.1 hN.2.1 hN.2.2.1 hN.2.2.2.1 hN.2.2.2.2 m j i (A x) q (by omega)).2.1
  have hrel (q : ℕ) (hqk : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y => physicalRelease Q (kids i) (B y)-1) x‖≤Cr/N.width^q := by
    apply physical_release_sub_one Q (kids i) B Cr N.width hCr x q (by omega)
    have hh := (linear_jet_contraction B hB (physicalRelease_contDiff Q (kids i) 3) x q (by omega)).trans
      (hr n D Q (kids i) (hk i) (B x) q (by omega))
    simpa only [hp i] using hh
  have hh := same_width_product_jets ((jointResidual_contDiff m j N i 3).comp A.contDiff)
    (((physicalRelease_contDiff Q (kids i) 3).comp B.contDiff).sub contDiff_const)
    (Cn*(N.ell*N.width^2)) Cr N.width (by positivity) hCr0 hw x k hq hres hrel
  exact hh.trans_eq (by ring)

end Bilevel.EndpointTransportResponse
